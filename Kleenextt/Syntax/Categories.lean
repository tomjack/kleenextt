import Lean.Parser

/-! The syntax categories, registered as builtin when this module initialises,
so they exist in the compiler when it is loaded as a plugin and in the
executable, which reads no `.olean` files. -/

namespace Lean.Parser.Category

def kexpr : Category := {}
def kbinder : Category := {}
def kpibinder : Category := {}
def kface : Category := {}
def kentry : Category := {}
def kcase : Category := {}
def kcon : Category := {}
def kcmd : Category := {}

end Lean.Parser.Category

namespace Kleenextt.Syntax

open Lean Parser

builtin_initialize
  registerBuiltinParserAttribute `builtin_kexpr_parser ``Category.kexpr
  registerBuiltinParserAttribute `builtin_kbinder_parser ``Category.kbinder
  registerBuiltinParserAttribute `builtin_kpibinder_parser ``Category.kpibinder
  registerBuiltinParserAttribute `builtin_kface_parser ``Category.kface
  registerBuiltinParserAttribute `builtin_kentry_parser ``Category.kentry
  registerBuiltinParserAttribute `builtin_kcase_parser ``Category.kcase
  registerBuiltinParserAttribute `builtin_kcon_parser ``Category.kcon
  registerBuiltinParserAttribute `builtin_kcmd_parser ``Category.kcmd

end Kleenextt.Syntax
