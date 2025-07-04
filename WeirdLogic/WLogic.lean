
import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog

import WeirdLogic.Gram

section WTriple

variable {α : Type}


local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

/- Triple-/
abbrev wtriple (t : htrm) (H : hhProp) (g : ctx_grammar) (Q : hval → hhProp): Prop :=
  ∀ p ∈ expandSymbol g 10 g.start, ∃ s,
  ∀ hh, H hh → heval s hh t Q



end WTriple
