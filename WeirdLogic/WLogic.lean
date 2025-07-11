
import Lgtm.Unary.Lang
import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog

import WeirdLogic.Gram

section WTriple

variable {α : Type} (s : Set α)

def hgram (α : Type) := α -> trm

local notation "hheap"  => @hheap α
local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α
local notation "hgram" => hgram α

inductive payload_base : Type where
  | pld_bool : Bool → payload_base
  | pld_nat : ℕ → payload_base

inductive payload : Type where
  | pld_one : payload_base → payload
  | pld_cons : payload_base → payload → payload

def wtrm (α : Type) := α -> trm /- α is payload later-/

local notation "wtrm" => wtrm α

/- Eval -/
def weval_nonrel (s : Set α) (hh : hheap) (ht : htrm) (hQ : α -> val -> hProp) : Prop :=
  ∀ a ∈ s, eval (hh a) (ht a) (hQ a)

/- TODO: insert grammar, cannot add it into htrm -/
def weval (s : Set α) (hh : hheap) (wt : wtrm) (hg : hgram) (hQ : hval -> hhProp) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    heval_nonrel s hh wt hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv')

/- Triple -/
abbrev wtriple (t : htrm) (hg : hgram) (H : hhProp) (Q : hval → hhProp): Prop :=
  ∀ hh, H hh → weval s hh t hg Q


def epimorphism {A B : Type} (f : A → B) : Prop :=
  ∀ b : B, ∃ a : A, f a = b ∧ ∀ b' : B, (f a = b' → b = b') ∧ ∀ a : A, ∃ b : B, f a = b


def epimorphism_wm (epi: htrm → hgram) : Prop :=
  epimorphism epi

/- Structural Rules -/
/- Can reuse them from LGTM directly? -/
lemma wtriple_conseq_frame:
  wtriple s t hg H₁ Q₁ →
  H ==> H₁ ∗ H₂ →
  Q₁ ∗ H₂ ===> Q →
  wtriple s t hg H Q := by
  sorry

/- symbol for surjection ↠ -/

end WTriple
