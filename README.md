# weird-logic

# Infinitary Relational Logic

## 1. Overview

This repository contains **Weird Logic**, a security-focused extension of
[Infinitary Relational Logic (IRL)](https://github.com/verse-lab/irl), mechanised in Lean 4.

Weird Logic applies IRL to **Weird Machine Realisability (WMR)**: given a
vulnerable program and a grammar describing the attacks an adversary can
express (a *weird machine*), it lets you prove that every attack in the grammar
can actually be realised by some input payload to the program.

It is used as a submodule of IRL, but can also be built and used on its own.

## 2. Getting Started

### Requirements

- Lean 4 **v4.20.0** (pinned in `lean-toolchain`)
- Internet access on first build (Lake fetches Mathlib and other dependencies)

Supported platforms are those of [elan](https://github.com/leanprover/elan) / Lean 4 (Linux, macOS, and Windows, where WSL is recommended).

To build Weird Logic as a standalone project:
```lean
git clone https://github.com/verse-lab/weird-logic.git
cd weird-logic
lake build
```
Do not modify `lakefile.lean` or `lean-toolchain`.

This will take a while (~20 minutes on a MacBook Pro with an M3 Pro chip and 32 GB of RAM).

This builds `Lgtm` (IRL and the case studies) and `WeirdLogic` (the WM rules and the WMR case study).

Expected: `Build completed successfully` with no errors.

## 3. Mapping of Rules

A successful `lake build` without "sorry" in warning messages already establishes the reproducibility of the IRL metatheory and of every lemma, rule, example, and case study claimed in the paper. 

Detailed guidelines from the paper to the artifact are shown below:

### IRL Rules

|       Name   | Paper | Location | Lemma |
|-------------:|------:|---------:|---------:|
`SeqU1` | Page 7, Figure 3 | `WeirdLogic/LgtmMisc.lean` | `LGTM.triple_sequ1`
`SeqU2` | Page 7, Figure 3 | `WeirdLogic/LgtmMisc.lean` | `LGTM.triple_sequ2`
`Focus` | Page 7, Figure 3 | `Lgtm/Hyper/ProofMode.lean` | `yfocus_set_lemma`
`For` | Page 9, Figure 5 | `Lgtm/Hyper/Loops/YLemmas.lean` | `yfor_lemma`
`InfInfProd` | Page 8, Figure 4 | `WeirdLogic/InfInfProd.lean` | `htriple_htriple_partition`
`InfProd` | Page 8, Figure 4 | `Lgtm/Hyper/SepLog.lean` | `htriple_prod`
`LetU` | Page 10, Figure 6| `Lgtm/Hyper/ProofMode.lean` | `ylet_lemma`
`Merge` | Page 10, Figure 6| `Lgtm/Hyper/Merge.lean` | `ymerge_lemma`
`While` | Page 17, Figure 8| `Lgtm/Hyper/Loops/YLemmas.lean` | `ywhile_lemma`
`Expand` | Converse of Merge rule| `WeirdLogic/LgtmMisc.lean` | `hsubst_htriple_gen`

### WM Rules 

|       Name   | Paper | Location | Lemma |
|-------------:|------:|---------:|---------:|
`Weaken` |  Page 20, Figure 10| `WeirdLogic/WLogic.lean` | `weird_weaken_lemma`
`GrmDisj` |  Page 20, Figure 10| `WeirdLogic/GramDisjStandard.lean` | `weird_grmdisj_lemma_standard`
`Payload` |  Page 20, Figure 10| `WeirdLogic/WLogic.lean` | `weird_payload_index_lemma` `weird_payload_index_lemma2`
`GrmSeq` |  Page 20, Figure 10| `WeirdLogic/GramSeq.lean` | `weird_gram_seq_full_prod`


## 4. Case Studies  

| Name   |           Paper   | Location | Lemma |
|-----|:----------------------:|---------:|---------:|
| Overall Example   | triple (25) |  `WeirdLogic/Examples/VulnWM.lean`   | `vulnwm_spec` | 
| Part 1   | triple (29)   |  `WeirdLogic/Examples/ForWM.lean`   | `forwm_spec`    | 
| Part 2   | triple (30) |  `WeirdLogic/Examples/IfWM.lean`   | `ifwm_spec` | 


## 5. Using IRL / Reusability

`WeirdLogic/Examples/` shows how to write programs, state Hoare-style specifications, and prove them in IRL. A typical workflow:

1. **Define programs** with `lang_def` / `lang_def'` (see `Lgtm/Experiments/Comparison/Code.lean`). The syntax is Imp-like; binders use `⸨x:Loc⸩` / `⸨x:Val⸩`.
2. **State a specification** as an IRL triple. 

WP form:
```lean
WP [ℓ | i in s => prog(...)] { v, Q }
```

Triple form:

```lean
{ H }
[ℓ₁ | i in s₁ => prog₁(...)]
[ℓ₂ | i in s₂ => prog₂(...)]
{ v, Q }
```

Here `H` / `Q` are hyper-heaps (separating conjunction `∗`, pure facts `⌜_⌝`, arrays `arr⟨s⟩(...)`). The underlying proposition is `htriple` / `hwp` from `Lgtm/Hyper/SepLog.lean` and `Lgtm/Hyper/WP.lean`.

3. **Prove the triple** in the IRL proof mode (`import Lgtm.Hyper.ProofMode`). Common tactics:

   | Tactic | Role |
   |--------|------|
   | `ywp` / `ytriple` | enter weakest-precondition / triple mode |
   | `yapp` / `ystep` | apply a registered spec or take one step |
   | `yfocus` / `yunfocus` | restrict or restore a component's index set (`Focus`) |
   | `ylet` / `yseq` / `yif` / `yref` | structural rules for `let`, sequencing, `if`, `ref` |
   | `yfor` / `ywhile` | loop rules (`For`, `While`) |
   | `ysimp` / `ypull` | simplify / pull pure facts from the precondition |
   | `yin ℓ: ...` | apply tactics under a selected label |

   Register reusable specs with `@[yapp]` or `#hint_yapp` so `yapp` can apply them automatically.
4. **Start from an existing case study.** For a concrete end-to-end proof, see `linearInterp_spec` in `Lgtm/Experiments/Comparison/Hyper/BilinInterp.lean`. For WM-style reasoning, see `WeirdLogic/Examples/VulnWM.lean`.
