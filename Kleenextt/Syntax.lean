import Kleenextt.Syntax.Categories

/-! The grammar, as builtin parsers. Cubical primitives are identifiers
`Frontend.toRaw` recognises at the head of an application; faces are
`(i = 0)`/`(i = 1)` on variables, juxtaposed. -/

namespace Kleenextt.Syntax

open Lean Parser

def kexpr (prec : Nat := 0) : Parser := categoryParser `kexpr prec
def kbinder : Parser := categoryParser `kbinder 0
def kpibinder : Parser := categoryParser `kpibinder 0
def kface : Parser := categoryParser `kface 0
def kentry : Parser := categoryParser `kentry 0
def kcase : Parser := categoryParser `kcase 0
def kcon : Parser := categoryParser `kcon 0

namespace Binder
@[builtin_kbinder_parser] def var := leading_parser ident
@[builtin_kbinder_parser] def hole := leading_parser "_"
@[builtin_kbinder_parser] def typed := leading_parser "(" >> many1 ident >> " : " >> kexpr >> ")"
@[builtin_kbinder_parser] def impl := leading_parser "{" >> ident >> "}"
@[builtin_kbinder_parser] def named := leading_parser "{" >> ident >> " := " >> ident >> "}"
end Binder

namespace PiBinder
@[builtin_kpibinder_parser] def expl := leading_parser "(" >> many1 ident >> " : " >> kexpr >> ")"
@[builtin_kpibinder_parser] def impl := leading_parser "{" >> many1 ident >> " : " >> kexpr >> "}"
@[builtin_kpibinder_parser] def untyped := leading_parser "{" >> many1 ident >> "}"
end PiBinder

@[builtin_kface_parser] def face := leading_parser "(" >> ident >> " = " >> numLit >> ")"
@[builtin_kentry_parser] def entry := leading_parser many1 kface >> " ↦ " >> kexpr
@[builtin_kcase_parser] def «case» := leading_parser ident >> many ident >> " ↦ " >> kexpr
@[builtin_kcon_parser] def con :=
  leading_parser ident >> many kpibinder >> optional ("[" >> sepBy kentry ", " >> "]")

namespace Expr
@[builtin_kexpr_parser] def var := leading_parser ident
@[builtin_kexpr_parser] def univ := leading_parser "Type"
@[builtin_kexpr_parser] def «sorry» := leading_parser "sorry"
@[builtin_kexpr_parser] def split :=
  leading_parser "case " >> kexpr maxPrec >> kexpr maxPrec >> "[" >> sepBy kcase ", " >> "]"
@[builtin_kexpr_parser] def hlevel := leading_parser "hlevel " >> numLit >> kexpr maxPrec
@[builtin_kexpr_parser] def hole := leading_parser "_"
@[builtin_kexpr_parser] def lit := leading_parser numLit
@[builtin_kexpr_parser] def paren := leading_parser "(" >> kexpr >> ")"
@[builtin_kexpr_parser] def tuple := leading_parser "(" >> kexpr >> ", " >> sepBy1 kexpr ", " >> ")"
@[builtin_kexpr_parser] def system := leading_parser "[" >> sepBy kentry ", " >> "]"
@[builtin_kexpr_parser] def app := trailing_parser:60:60 kexpr 61
@[builtin_kexpr_parser] def appImpl := trailing_parser:60:60 "{" >> kexpr >> "}"
@[builtin_kexpr_parser] def appNamed := trailing_parser:60:60 "{" >> ident >> " := " >> kexpr >> "}"
@[builtin_kexpr_parser] def neg := leading_parser:40 "¬" >> kexpr 40
@[builtin_kexpr_parser] def meet := trailing_parser:35:36 " ∧ " >> kexpr 35
@[builtin_kexpr_parser] def join := trailing_parser:30:31 " ∨ " >> kexpr 30
@[builtin_kexpr_parser] def sigmaDep :=
  leading_parser:35 "(" >> ident >> " : " >> kexpr >> ")" >> " × " >> kexpr 35
@[builtin_kexpr_parser] def sigma := trailing_parser:35:36 " × " >> kexpr 35
@[builtin_kexpr_parser] def arrow := trailing_parser:25:26 " → " >> kexpr 25
@[builtin_kexpr_parser] def pi := leading_parser:25 many1 kpibinder >> " → " >> kexpr 25
@[builtin_kexpr_parser] def arrowAscii := trailing_parser:25:26 " -> " >> kexpr 25
@[builtin_kexpr_parser] def piAscii := leading_parser:25 many1 kpibinder >> " -> " >> kexpr 25
@[builtin_kexpr_parser] def lam := leading_parser:10 "λ" >> many1 kbinder >> " => " >> kexpr 10
@[builtin_kexpr_parser] def «let» :=
  leading_parser:10 "let " >> ident >> " : " >> kexpr >> " := " >> kexpr >> "; " >> kexpr 10
end Expr

namespace Cmd
@[builtin_kcmd_parser] def moduleDoc := leading_parser "/-!" >> Command.commentBody
@[builtin_kcmd_parser] def «import» := leading_parser "import " >> ident
@[builtin_kcmd_parser] def kdef := leading_parser "kdef " >> ident >> " : " >> kexpr >> " := " >> kexpr
@[builtin_kcmd_parser] def kdata := leading_parser "kdata " >> ident >> " := " >> sepBy kcon " | "
@[builtin_kcmd_parser] def knf := leading_parser "#knf " >> kexpr
@[builtin_kcmd_parser] def ktime := leading_parser "#ktime " >> kexpr
@[builtin_kcmd_parser] def ktrace := leading_parser "#ktrace " >> kexpr
@[builtin_kcmd_parser] def kterm := leading_parser "#kterm " >> kexpr
@[builtin_kcmd_parser] def khead := leading_parser "#khead " >> numLit >> kexpr
@[builtin_kcmd_parser] def koverlaps := leading_parser "#koverlaps " >> numLit >> kexpr
@[builtin_kcmd_parser] def kstable := leading_parser "#kstable " >> numLit >> kexpr
@[builtin_kcmd_parser] def ktype := leading_parser "#ktype " >> kexpr
@[builtin_kcmd_parser] def kconv := leading_parser "#kconv " >> kexpr >> " = " >> kexpr
@[builtin_kcmd_parser] def kdiffer := leading_parser "#kdiffer " >> kexpr >> " = " >> kexpr
@[builtin_kcmd_parser] def kfail := leading_parser "#kfail " >> kexpr
end Cmd

end Kleenextt.Syntax
