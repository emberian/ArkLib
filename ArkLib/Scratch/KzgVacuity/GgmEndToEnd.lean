/-
THE CAPSTONE: the single end-to-end t-SDH GGM soundness theorem about ArkLib's REAL
`tSdhExperiment`. Composes the four prerequisite files (A/B/C/D + transport) into ONE named
theorem, `tSdh_ggm_sound`, and its companion `tSdh_ggm_sound_lt_one`.

NOT part of ArkLib. Scratch research file supporting
`docs/reference/arklib-kzg-vacuity/END-TO-END-PLAN.md` (task E). Built against ArkLib @
`d72f8392` (Lean v4.31.0); imports ArkLib's REAL `Groups.tSdhExperiment` and our A/B/C/D files
— nothing is restated.

WHY THIS ESCAPES VACUITY (END-TO-END-PLAN §1a). `∀ A : tSdhAdversary D, tSdhExperiment D A ≤ ε`
is FALSE for small ε: a `Classical.choice`-definable adversary inverts the encoding and wins
t-SDH with probability 1. So the target does NOT quantify over all `tSdhAdversary`. It quantifies
over generic **strategies** `strat : Strat p` and applies the embedding `GgmEmbed.embed`; the
"generic-restricted adversary class" is the IMAGE of `embed`. `embed strat` receives only equality
booleans (`strat : List Bool → …`) — no group element is ever in scope for it to invert — so it can
only realize `g₁ ^ (f τ)` with `deg f ≤ D`, which is exactly what the counting bound bounds.

THE COMPOSITION CHAIN (END-TO-END-PLAN §2d).
  tSdhExperiment D (embed strat)
    = ((univ.filter (winPred (stratResult …) g₁)).card : ℝ≥0∞) / (p−1)   -- C: experiment_eq_count
                                                                          --    (hdet from D: embed_run_correspondence)
    ≤ ((realWinSet strat (srsSt D) fuel).card : ℝ≥0∞) / (p−1)             -- reindex Fin (p−1) ↪ groupWinSet
                                                                          --    + transport: groupWinSet_eq_realWinSet
    ≤ ((C(fuel+D+4,2)·D + (D+1) : ℕ) : ℝ≥0∞) / (p−1)                      -- A: card_realWinSet_le_encoding_D @ Δ=D
                                                                          --    (degrees discharged by B's _of_run)

Every gluing lemma is the REAL one: the degree discharge is B's theorems about the actual
`runTable` (not the `buildPaired` peer); the count is C's `experiment_eq_count` about ArkLib's
`tSdhExperiment`; the correspondence is D's `embed_run_correspondence` about ArkLib's SRS. No peer
model or restated definition is swapped into any socket.

HONEST SIDE-CONDITIONS. `1 ≤ D` (the meaningful KZG regime; at `D = 0` the pairing-free G₁
adversary genuinely cannot form `g₁^τ`, see GgmEmbed's SCOPE note), `2 ≤ p` (so `p − 1 ≥ 1`), and
`orderOf g₁ = p` (the base is a generator — used by the encoding injectivity). The `∀ i,
SampleableType (unifSpec.Range i)` instance is ArkLib's OWN assumption on `tSdhExperiment`, carried
verbatim. `tSdh_ggm_sound_lt_one` adds the standard regime hypothesis `C(fuel+D+4,2)·D + (D+1) <
p − 1` and delivers a genuine `< 1`.
-/
import ArkLib.Scratch.KzgVacuity.GgmEmbed
import ArkLib.Scratch.KzgVacuity.GgmProbThreading
import ArkLib.Scratch.KzgVacuity.GgmDegreeDischarge

open Polynomial Groups OracleSpec OracleComp
open scoped Classical NNReal ENNReal

namespace GgmEndToEnd

open GgmCandidate GgmAdaptive GgmRandomEncoding GgmArkLibTransport GgmEmbed Ggm.ProbThreading
open GgmDegreeDischarge

variable {p : ℕ} [Fact (Nat.Prime p)]
  [∀ i, SampleableType (unifSpec.Range i)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {D : ℕ}

/-! ## 1. The deterministic output of `embed strat`, and `embed`'s determinism. -/

/-- The (deterministic-given-τ) `Option`-output of `embed strat` on the SRS generated from `τ`: the
committed offset of the symbolic run realized in the group. This is the RHS of D's
`embed_run_correspondence`, packaged as the `resultOf` that C's `experiment_eq_count` consumes. -/
noncomputable def stratResult (g₁ : G₁) (D fuel : ℕ) (strat : Strat p) :
    ZMod p → Option (ZMod p × G₁) :=
  fun τ => some ((runOutput (realAns τ) strat fuel (srsSt D)).1,
    g₁ ^ ((runOutput (realAns τ) strat fuel (srsSt D)).2.eval τ).val)

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- **`embed strat` is deterministic-given-τ from the empty cache**, with output `stratResult`.
`embed strat srs = pure (runEmbed … srs)`, so `.run' ∅ = pure (runEmbed …)`, and D's
`embed_run_correspondence` identifies `runEmbed …` on `PowerSrs.generate D τ` with `stratResult τ`.
This is the exact `hdet` hypothesis of C's `game_collapse` / `experiment_eq_count`. -/
theorem embed_det (hord₁ : orderOf g₁ = p) (hD : 1 ≤ D) (strat : Strat p) (fuel : ℕ) :
    ∀ τ, (embed g₁ g₂ D fuel strat
        (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).run' ∅
      = pure (stratResult g₁ D fuel strat τ) := by
  intro τ
  simp only [embed, StateT.run'_pure', stratResult]
  rw [embed_run_correspondence hord₁ D hD τ strat fuel]

/-! ## 2. The reindex `Fin (p−1) ↪ groupWinSet`: the winning-index count is ≤ the winning-set card. -/

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- The nonzero-trapdoor index `i : Fin (p−1)` maps to a genuine nonzero residue `(i+1 : ZMod p)`
(matching `winPred`'s `((i : ℕ) + 1 : ZMod p)` — the ZMod-level `+`). -/
lemma index_ne_zero (hp : 2 ≤ p) (i : Fin (p - 1)) : ((i : ℕ) + 1 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hlt : (i : ℕ) + 1 < p := by have := i.isLt; omega
  have hcast : ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
  rw [hcast]
  intro h
  have h2 : (((i : ℕ) + 1 : ℕ) : ZMod p).val = 0 := by rw [h]; exact ZMod.val_zero
  rw [ZMod.val_natCast_of_lt hlt] at h2
  omega

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- **The reindex bound.** The number of winning nonzero-trapdoor indices `i : Fin (p−1)` (those on
which `embed strat`'s deterministic output `stratResult` wins ArkLib's `tSdhCondition`) is at most
the cardinality of the field-level winning set `realWinSet`. Proved by an injection
`i ↦ (i+1 : ZMod p)` into `realWinSet`, transporting each winning index through the condition
equivalence `tSdhCondition_iff_field` (the pointwise fact that `groupWinSet_eq_realWinSet` packages
as a set identity). Only the `≤` direction is needed, so no surjectivity is required. -/
theorem winIndex_card_le (hord₁ : orderOf g₁ = p) (hp : 2 ≤ p)
    (strat : Strat p) (fuel : ℕ) :
    (Finset.univ.filter (winPred (stratResult g₁ D fuel strat) g₁)).card
      ≤ (realWinSet strat (srsSt D) fuel).card := by
  refine Finset.card_le_card_of_injOn (fun i => ((i : ℕ) + 1 : ZMod p)) ?_ ?_
  · -- maps winning indices into `realWinSet`
    intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    have hw := hi.2
    simp only [winPred] at hw
    obtain ⟨ch, hres, hcond⟩ := hw
    -- `stratResult … (i+1) = some (offset, encoded output)` pins `ch`
    rw [stratResult, Option.some.injEq] at hres
    rw [← hres] at hcond
    -- transport ArkLib's group condition to the field predicate `realWinSet` filters by
    rw [Finset.mem_coe, realWinSet, Finset.mem_filter]
    refine ⟨?_, (tSdhCondition_iff_field hord₁ _ _ _).mp hcond⟩
    rw [nonzeroPoints, Finset.mem_erase]
    exact ⟨index_ne_zero hp i, Finset.mem_univ _⟩
  · -- `i ↦ (i+1 : ZMod p)` is injective on `Fin (p−1)`
    intro i _ j _ hij
    simp only at hij
    have hi : (i : ℕ) + 1 < p := by have := i.isLt; omega
    have hj : (j : ℕ) + 1 < p := by have := j.isLt; omega
    have hci : ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
    have hcj : ((j : ℕ) + 1 : ZMod p) = (((j : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
    rw [hci, hcj] at hij
    have := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
    exact Fin.ext (by omega)

/-! ## 3. ⚑ THE CAPSTONE. -/

/-- **`tSdh_ggm_sound` — the single end-to-end t-SDH GGM soundness theorem.** For every generic
strategy `strat : Strat p`, the embedded ArkLib adversary `embed strat` wins ArkLib's REAL t-SDH
experiment with probability at most the Shoup random-encoding number
`(C(fuel+D+4, 2)·D + (D+1)) / (p − 1)`. The whole argument is wired through ONE socket:

* `experiment_eq_count` (C) turns ArkLib's `tSdhExperiment` into a `Finset` count over `Fin (p−1)`,
  its determinism hypothesis discharged by `embed_det` (which rests on D's `embed_run_correspondence`);
* the count is bounded by `realWinSet.card` via the injection `winIndex_card_le` + the transport
  `groupWinSet_eq_realWinSet`;
* `realWinSet.card` is bounded by `card_realWinSet_le_encoding_D` (A) at Δ = D, with BOTH degree
  hypotheses discharged by B's `_of_run` theorems about the real `runTable`.

The theorem is about the IMAGE of `embed`, a genuinely rich strategy space — NOT the full
`tSdhAdversary` type (over which the statement is false). -/
theorem tSdh_ggm_sound
    (hg₁ : g₁ ≠ 1) (hord₁ : orderOf g₁ = p) (hg₂ : g₂ ≠ 1)
    (hp : 2 ≤ p) (hD : 1 ≤ D) (strat : Strat p) (fuel : ℕ) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embed g₁ g₂ D fuel strat)
      ≤ (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℝ≥0∞) / ((p - 1 : ℕ) : ℝ≥0∞) := by
  -- (C) collapse the experiment to a count over `Fin (p−1)`
  rw [experiment_eq_count D (embed g₁ g₂ D fuel strat) (stratResult g₁ D fuel strat)
    (embed_det hord₁ hD strat fuel)]
  -- the numerator is bounded, in ℕ, by the Shoup number
  have hcard : (Finset.univ.filter (winPred (stratResult g₁ D fuel strat) g₁)).card
      ≤ (fuel + D + 4).choose 2 * D + (D + 1) := by
    refine (winIndex_card_le hord₁ hp strat fuel).trans ?_
    -- (A) the δ = D random-encoding card bound, with (B)'s degree discharge on the real runTable
    exact card_realWinSet_le_encoding_D strat (srsSt D) fuel D (fuel + D + 4)
      (hdeg_out_of_run strat (srsSt D) fuel D (srsSt_table_natDegree_le D hD))
      (hdeg_handles_of_run strat (srsSt D) fuel D (srsSt_table_natDegree_le D hD))
      (by rw [srsSt_table_length]; omega)
  -- lift the ℕ count bound through the ℝ≥0∞ division
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-! ## 4. Real content: the bound is `< 1` in the standard regime. -/

/-- **`tSdh_ggm_sound_lt_one`.** Under the standard security regime
`C(fuel+D+4, 2)·D + (D+1) < p − 1`, the t-SDH advantage of `embed strat` is a genuine `< 1` — the
theorem has real content (it is not a restated `≤ 1`). Composing with `tSdh_ggm_sound` gives
`tSdhExperiment D (embed strat) < 1`. -/
theorem tSdh_ggm_sound_lt_one
    (hg₁ : g₁ ≠ 1) (hord₁ : orderOf g₁ = p) (hg₂ : g₂ ≠ 1)
    (hp : 2 ≤ p) (hD : 1 ≤ D) (strat : Strat p) (fuel : ℕ)
    (hreg : (fuel + D + 4).choose 2 * D + (D + 1) < p - 1) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embed g₁ g₂ D fuel strat) < 1 := by
  refine lt_of_le_of_lt (tSdh_ggm_sound hg₁ hord₁ hg₂ hp hD strat fuel) ?_
  have hb0 : ((p - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; omega
  have hbtop : ((p - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbtop), one_mul]
  exact_mod_cast hreg

/-! ## Axiom hygiene — the capstone rests on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms tSdh_ggm_sound
#print axioms tSdh_ggm_sound_lt_one

end GgmEndToEnd
