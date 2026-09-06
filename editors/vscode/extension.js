// A client for `kleenextt --server`: diagnostics and Lean's `$/lean/fileProgress`,
// over the LSP subset the server speaks. Self-contained, so the extension needs
// no build step or npm install. The server is built from the extension's own
// sources with lake on first use, using the elan that the Lean 4 extension
// installs.
'use strict';

const vscode = require('vscode');
const cp = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');

const LANGUAGE = 'kleenextt';
const BINARY = path.join('.lake', 'build', 'bin', 'kleenextt');

/** JSON-RPC over the server's stdio. */
class Connection {
  constructor(command, cwd, onNotification, onExit) {
    this.nextId = 1;
    this.pending = new Map();
    this.buffer = Buffer.alloc(0);
    this.exited = false;
    this.onNotification = onNotification;
    this.process = cp.spawn(command, ['--server'], { cwd, stdio: ['pipe', 'pipe', 'pipe'] });
    this.process.stdout.on('data', (chunk) => this.receive(chunk));
    this.process.stderr.on('data', (chunk) => log.append(chunk.toString()));
    this.exit = new Promise((resolve) => {
      this.process.on('error', (err) => { this.exited = true; onExit(this, err); resolve(); });
      this.process.on('exit', (code, signal) => { this.exited = true; onExit(this, null, code, signal); resolve(); });
    });
  }

  receive(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    for (;;) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n');
      if (headerEnd < 0) return;
      const headers = this.buffer.slice(0, headerEnd).toString();
      const match = /Content-Length:\s*(\d+)/i.exec(headers);
      if (!match) {
        this.buffer = this.buffer.slice(headerEnd + 4);
        continue;
      }
      const length = parseInt(match[1], 10);
      const bodyStart = headerEnd + 4;
      if (this.buffer.length < bodyStart + length) return;
      const body = this.buffer.slice(bodyStart, bodyStart + length).toString();
      this.buffer = this.buffer.slice(bodyStart + length);
      let message;
      try {
        message = JSON.parse(body);
      } catch (err) {
        log.appendLine(`unparsable message from server: ${err}`);
        continue;
      }
      this.dispatch(message);
    }
  }

  dispatch(message) {
    if (message.id !== undefined && message.method === undefined) {
      const pending = this.pending.get(message.id);
      if (!pending) return;
      this.pending.delete(message.id);
      if (message.error) pending.reject(new Error(message.error.message));
      else pending.resolve(message.result);
    } else if (message.method !== undefined) {
      this.onNotification(message.method, message.params);
    }
  }

  send(message) {
    if (!this.process.stdin.writable) return;
    const body = JSON.stringify({ jsonrpc: '2.0', ...message });
    this.process.stdin.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  }

  request(method, params) {
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.send({ id, method, params });
    });
  }

  notify(method, params) {
    this.send({ method, params });
  }

  dispose() {
    for (const pending of this.pending.values()) pending.reject(new Error('connection closed'));
    this.pending.clear();
    if (!this.exited) this.process.kill();
  }
}

const log = vscode.window.createOutputChannel('kleenextt');
const diagnostics = vscode.languages.createDiagnosticCollection('kleenextt');
const processingDecoration = vscode.window.createTextEditorDecorationType({
  overviewRulerLane: vscode.OverviewRulerLane.Left,
  overviewRulerColor: 'rgba(255, 165, 0, 0.7)',
  backgroundColor: 'rgba(255, 165, 0, 0.08)',
  isWholeLine: true,
});
const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);

/** elan's lake, as the Lean 4 extension installs it, else whatever is on PATH. */
function lake() {
  const elan = path.join(os.homedir(), '.elan', 'bin', 'lake');
  return fs.existsSync(elan) ? elan : 'lake';
}

/** Let the Lean 4 extension's Unicode input work in .ktt files. */
function enableLeanInput() {
  const config = vscode.workspace.getConfiguration('lean4');
  const languages = config.get('input.languages', ['lean4', 'lean']);
  if (languages.includes(LANGUAGE)) return;
  config.update('input.languages', [...languages, LANGUAGE], vscode.ConfigurationTarget.Global)
    .then(undefined, (err) => log.appendLine(`could not update lean4.input.languages: ${err}`));
}

const severities = [
  vscode.DiagnosticSeverity.Error,
  vscode.DiagnosticSeverity.Error,
  vscode.DiagnosticSeverity.Warning,
  vscode.DiagnosticSeverity.Information,
  vscode.DiagnosticSeverity.Hint,
];

function toRange(range) {
  return new vscode.Range(
    new vscode.Position(range.start.line, range.start.character),
    new vscode.Position(range.end.line, range.end.character));
}

/** One server per session, started on the first .ktt document. */
class Server {
  constructor(context) {
    this.context = context;
    this.connection = null;
    this.starting = null;
    this.building = null;
    this.progress = new Map();
  }

  /** The configured executable, the workspace's build, or the extension's own,
   * built now if missing. */
  async executable(document) {
    const configured = vscode.workspace.getConfiguration('kleenextt').get('executablePath', '');
    const folder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = folder ? folder.uri.fsPath : path.dirname(document.uri.fsPath);
    if (configured) return { command: configured, cwd };
    if (folder) {
      const built = path.join(folder.uri.fsPath, BINARY);
      if (fs.existsSync(built)) return { command: built, cwd };
    }
    const own = path.join(this.context.extensionPath, BINARY);
    if (!fs.existsSync(own)) await this.build();
    return { command: own, cwd };
  }

  /** `lake build` in the extension directory; elan fetches the pinned toolchain
   * on first use. */
  build() {
    if (this.building) return this.building;
    const root = this.context.extensionPath;
    this.building = vscode.window.withProgress({
      location: vscode.ProgressLocation.Notification,
      title: 'kleenextt: building the server with lake (the first build also downloads Lean)',
    }, () => new Promise((resolve, reject) => {
      const command = lake();
      log.appendLine(`${command} build kleenextt in ${root}`);
      const proc = cp.spawn(command, ['build', '--no-ansi', 'kleenextt'], { cwd: root });
      proc.stdout.on('data', (chunk) => log.append(chunk.toString()));
      proc.stderr.on('data', (chunk) => log.append(chunk.toString()));
      proc.on('error', (err) => reject(new Error(`could not run ${command}: ${err.message}`)));
      proc.on('exit', (code, signal) => {
        if (code === 0) resolve();
        else reject(new Error(`lake build exited with ${signal || code}`));
      });
    })).finally(() => { this.building = null; });
    return this.building;
  }

  start(document) {
    if (this.connection || this.starting) return this.starting;
    this.starting = this.executable(document).then(({ command, cwd }) => {
      log.appendLine(`starting ${command} --server in ${cwd}`);
      const connection = new Connection(command, cwd,
        (method, params) => this.onNotification(method, params),
        (from, err, code, signal) => this.onExit(from, command, err, code, signal));
      this.connection = connection;
      return connection.request('initialize', {
        processId: process.pid,
        rootUri: vscode.Uri.file(cwd).toString(),
        capabilities: {},
        initializationOptions: {
          timeBudget: vscode.workspace.getConfiguration('kleenextt').get('timeBudget', 5),
        },
      }).then(() => {
        if (this.connection !== connection) return;
        connection.notify('initialized', {});
        for (const open of vscode.workspace.textDocuments) {
          if (open.languageId === LANGUAGE) this.open(open);
        }
      });
    }).catch((err) => {
      log.appendLine(`${err}`);
      vscode.window.showErrorMessage(`kleenextt: ${err.message}`, 'Show Output')
        .then((choice) => { if (choice) log.show(); });
    }).finally(() => { this.starting = null; });
    return this.starting;
  }

  /** An unrequested exit; one that `stop` asked for is no longer current. */
  onExit(connection, command, err, code, signal) {
    if (connection !== this.connection) return;
    this.connection = null;
    this.progress.clear();
    this.updateProgress();
    if (err) {
      vscode.window.showErrorMessage(`kleenextt: could not run ${command}: ${err.message}`);
    } else if (code !== 0 || signal) {
      vscode.window.showErrorMessage(`kleenextt: server exited (${signal || code})`);
    }
  }

  onNotification(method, params) {
    if (method === 'textDocument/publishDiagnostics') {
      diagnostics.set(vscode.Uri.parse(params.uri), params.diagnostics.map((d) => {
        const diagnostic = new vscode.Diagnostic(toRange(d.range), d.message, severities[d.severity || 1]);
        diagnostic.source = 'kleenextt';
        return diagnostic;
      }));
    } else if (method === '$/lean/fileProgress') {
      this.progress.set(params.textDocument.uri, params.processing.map((p) => toRange(p.range)));
      this.updateProgress();
    }
  }

  updateProgress() {
    let busy = 0;
    for (const editor of vscode.window.visibleTextEditors) {
      const ranges = this.progress.get(editor.document.uri.toString()) || [];
      editor.setDecorations(processingDecoration, ranges);
      busy += ranges.length;
    }
    if (busy > 0) {
      status.text = '$(sync~spin) kleenextt';
      status.show();
    } else {
      status.hide();
    }
  }

  open(document) {
    this.connection.notify('textDocument/didOpen', {
      textDocument: {
        uri: document.uri.toString(),
        languageId: LANGUAGE,
        version: document.version,
        text: document.getText(),
      },
    });
  }

  change(event) {
    if (!this.connection) return;
    this.connection.notify('textDocument/didChange', {
      textDocument: { uri: event.document.uri.toString(), version: event.document.version },
      contentChanges: event.contentChanges.map((c) => ({
        range: {
          start: { line: c.range.start.line, character: c.range.start.character },
          end: { line: c.range.end.line, character: c.range.end.character },
        },
        text: c.text,
      })),
    });
  }

  close(document) {
    if (!this.connection) return;
    this.connection.notify('textDocument/didClose', { textDocument: { uri: document.uri.toString() } });
    diagnostics.delete(document.uri);
    this.progress.delete(document.uri.toString());
    this.updateProgress();
  }

  async stop() {
    if (this.starting) await this.starting;
    const connection = this.connection;
    if (!connection) return;
    this.connection = null;
    const timeout = (ms) => new Promise((r) => setTimeout(r, ms));
    try {
      await Promise.race([connection.request('shutdown', null), timeout(2000)]);
      connection.notify('exit', null);
      await Promise.race([connection.exit, timeout(1000)]);
    } finally {
      connection.dispose();
      diagnostics.clear();
      this.progress.clear();
      this.updateProgress();
    }
  }

  restart() {
    return this.stop().then(() => {
      const document = vscode.workspace.textDocuments.find((d) => d.languageId === LANGUAGE);
      if (document) return this.start(document);
    });
  }
}

let server = null;

function activate(context) {
  server = new Server(context);
  enableLeanInput();
  context.subscriptions.push(
    log, diagnostics, processingDecoration, status,
    vscode.workspace.onDidOpenTextDocument((document) => {
      if (document.languageId !== LANGUAGE) return;
      if (server.connection) server.open(document);
      else server.start(document);
    }),
    vscode.workspace.onDidChangeTextDocument((event) => {
      if (event.document.languageId === LANGUAGE) server.change(event);
    }),
    vscode.workspace.onDidCloseTextDocument((document) => {
      if (document.languageId === LANGUAGE) server.close(document);
    }),
    vscode.window.onDidChangeVisibleTextEditors(() => server.updateProgress()),
    vscode.languages.registerDefinitionProvider(LANGUAGE, {
      provideDefinition: async (document, position) => {
        if (!server.connection) return null;
        const result = await server.connection.request('textDocument/definition', {
          textDocument: { uri: document.uri.toString() },
          position: { line: position.line, character: position.character },
        });
        const locations = result == null ? [] : Array.isArray(result) ? result : [result];
        return locations.map((l) => new vscode.Location(vscode.Uri.parse(l.uri), toRange(l.range)));
      },
    }),
    vscode.commands.registerCommand('kleenextt.checkToCursor', () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== LANGUAGE || !server.connection) return;
      const position = editor.selection.active;
      return server.connection.request('$/kleenextt/check', {
        textDocument: { uri: editor.document.uri.toString() },
        position: { line: position.line, character: position.character },
      });
    }),
    vscode.commands.registerCommand('kleenextt.checkFile', () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== LANGUAGE || !server.connection) return;
      return server.connection.request('$/kleenextt/check', {
        textDocument: { uri: editor.document.uri.toString() },
      });
    }),
    vscode.commands.registerCommand('kleenextt.restartServer', () => server.restart()),
    vscode.commands.registerCommand('kleenextt.rebuildServer', async () => {
      await server.stop();
      try {
        await server.build();
      } catch (err) {
        vscode.window.showErrorMessage(`kleenextt: ${err.message}`, 'Show Output')
          .then((choice) => { if (choice) log.show(); });
        return;
      }
      await server.restart();
    }));
  const document = vscode.workspace.textDocuments.find((d) => d.languageId === LANGUAGE);
  if (document) server.start(document);
}

function deactivate() {
  return server ? server.stop() : undefined;
}

module.exports = { activate, deactivate };
