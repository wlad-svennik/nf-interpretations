module

public import NFURank
public import MHRankZ
public import MGraphRank
public import ZermeloTC
public import MHLRank

@[expose] public section

set_option autoImplicit false

/-!
# NF with the Axiom of Counting and Zermelo set theory with the rank axioms

Collected from `MHRankSupply.lean`, `NFURank.lean`, `MHRankZ.lean`, `MHLRank.lean`,
`ZermeloTC.lean` and `MGraphRank.lean`. `𝗥` after a theory means: with the rank axioms.

* `Con(𝗡𝗙𝗖) ↔ Con(𝗠𝗛𝗥)` (`consistent_nfc_iff_consistent_mhr`, `NFURank.lean`).
* `Con(𝗠𝗛𝗥) → Con(𝗭𝗖𝗥)`: a level of the constructible sets of a model of `𝗠𝗛𝗥`
  (`MHLRank.lean`). `Con(𝗠𝗛𝗥) → Con(𝗭𝗧𝗥)`: a rank of a model of `𝗠𝗛𝗥` (`MHRankZ.lean`).
* `Con(𝗭𝗥) → Con(𝗠𝗥)`: the sets included in a transitive set (`ZermeloTC.lean`).
* `Con(𝗠𝗥) → Con(𝗠𝗛𝗥)`: the pointed graphs of a model of `𝗠` (`MGraphRank.lean`).
* **`consistent_nfc_iff_consistent_zcr : Con(𝗡𝗙𝗖) ↔ Con(𝗭𝗖𝗥)`**: NF with the Axiom of
  Counting is consistent exactly when Zermelo set theory with Choice and the rank axioms is.
* **`consistent_nfc_iff_consistent_zr : Con(𝗡𝗙𝗖) ↔ Con(𝗭𝗥)`**, the same without Choice; and
  the same for `𝗭𝗧𝗥` and `𝗠𝗥`.
-/

namespace FFL.FirstOrder.SetTheory

/-- **If NF with the Axiom of Counting is consistent, so is Zermelo set theory with transitive
containment and the rank axioms.** -/
theorem consistent_ztr_of_consistent_nfc (h : Entailment.Consistent 𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭𝗧𝗥 :=
  consistent_ztr_of_consistent_mhr (consistent_nfc_iff_consistent_mhr.mp h)

/-- **If NF with the Axiom of Counting is consistent, so is Zermelo set theory with the rank
axioms.** -/
theorem consistent_zr_of_consistent_nfc (h : Entailment.Consistent 𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭𝗥 :=
  consistent_zr_of_consistent_mhr (consistent_nfc_iff_consistent_mhr.mp h)

/-- If NFU + Infinity + the Axiom of Counting is consistent, so is `𝗭𝗧𝗥`. -/
theorem consistent_ztr_of_consistent_nfuic (h : Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖) :
    Entailment.Consistent 𝗭𝗧𝗥 :=
  consistent_ztr_of_consistent_mhr (consistent_nfuic_iff_consistent_mhr.mp h)

/-! ### The converse, from theories with transitive containment -/

/-- Every axiom of `𝗠𝗥` is an axiom of `𝗭𝗧𝗥`. -/
theorem mr_subset_ztr : 𝗠𝗥 ⊆ 𝗭𝗧𝗥 := by
  rintro φ (hφ | hφ)
  · rcases hφ with (hφ | hφ) | hφ
    · exact Or.inl (Or.inl (Or.inl hφ))
    · exact Or.inl (Or.inl (Or.inr (boundedSeparation_subset hφ)))
    · exact Or.inl (Or.inr hφ)
  · exact Or.inr hφ

/-- Every axiom of `𝗠𝗥` is an axiom of `𝗠𝗛𝗥`. -/
theorem mr_subset_mhr : 𝗠𝗥 ⊆ 𝗠𝗛𝗥 := by
  rintro φ (hφ | hφ)
  · exact Or.inl (Or.inl hφ)
  · exact Or.inr hφ

/-- **If Zermelo set theory with transitive containment and the rank axioms is consistent, so
is NF with the Axiom of Counting.** -/
theorem consistent_nfc_of_consistent_ztr (h : Entailment.Consistent 𝗭𝗧𝗥) :
    Entailment.Consistent 𝗡𝗙𝗖 :=
  consistent_nfc_iff_consistent_mhr.mpr
    (consistent_mhr_of_consistent_mr (h.of_subset mr_subset_ztr))

/-- **NF with the Axiom of Counting is consistent exactly when Zermelo set theory with
transitive containment and the rank axioms is.** -/
theorem consistent_nfc_iff_consistent_ztr :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗭𝗧𝗥 :=
  ⟨consistent_ztr_of_consistent_nfc, consistent_nfc_of_consistent_ztr⟩

/-- **NF with the Axiom of Counting is consistent exactly when Mathias's `𝗠` with the rank
axioms is.** -/
theorem consistent_nfc_iff_consistent_mr :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗠𝗥 :=
  ⟨fun h => (consistent_nfc_iff_consistent_mhr.mp h).of_subset mr_subset_mhr,
    fun h => consistent_nfc_iff_consistent_mhr.mpr (consistent_mhr_of_consistent_mr h)⟩

/-- `𝗠` with the rank axioms is consistent exactly when `𝗠𝗛` with the rank axioms is. -/
theorem consistent_mr_iff_consistent_mhr :
    Entailment.Consistent 𝗠𝗥 ↔ Entailment.Consistent 𝗠𝗛𝗥 :=
  ⟨consistent_mhr_of_consistent_mr, fun h => h.of_subset mr_subset_mhr⟩

/-- NFU + Infinity + the Axiom of Counting is consistent exactly when `𝗭𝗧𝗥` is. -/
theorem consistent_nfuic_iff_consistent_ztr :
    Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖 ↔ Entailment.Consistent 𝗭𝗧𝗥 :=
  ⟨consistent_ztr_of_consistent_nfuic, fun h => consistent_nfuic_iff_consistent_mhr.mpr
    (consistent_mhr_of_consistent_mr (h.of_subset mr_subset_ztr))⟩

/-! ### Zermelo set theory without transitive containment, and with Choice -/

/-- **If Zermelo set theory with the rank axioms is consistent, so is NF with the Axiom of
Counting.** -/
theorem consistent_nfc_of_consistent_zr (h : Entailment.Consistent 𝗭𝗥) :
    Entailment.Consistent 𝗡𝗙𝗖 :=
  consistent_nfc_iff_consistent_mhr.mpr
    (consistent_mhr_of_consistent_mr (consistent_mr_of_consistent_zr h))

/-- **NF with the Axiom of Counting is consistent exactly when Zermelo set theory with the
rank axioms is.** -/
theorem consistent_nfc_iff_consistent_zr :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗭𝗥 :=
  ⟨consistent_zr_of_consistent_nfc, consistent_nfc_of_consistent_zr⟩

/-- NFU + Infinity + the Axiom of Counting is consistent exactly when `𝗭𝗥` is. -/
theorem consistent_nfuic_iff_consistent_zr :
    Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖 ↔ Entailment.Consistent 𝗭𝗥 :=
  ⟨fun h => consistent_zr_of_consistent_mhr (consistent_nfuic_iff_consistent_mhr.mp h),
    fun h => consistent_nfuic_iff_consistent_mhr.mpr
      (consistent_mhr_of_consistent_mr (consistent_mr_of_consistent_zr h))⟩

/-- Every axiom of `𝗭𝗥` is an axiom of `𝗭𝗖𝗥`. -/
theorem zr_subset_zcr : 𝗭𝗥 ⊆ 𝗭𝗖𝗥 := by
  rintro φ (hφ | hφ)
  · exact Or.inl (Or.inl hφ)
  · exact Or.inr hφ

/-- **If Zermelo set theory with Choice and the rank axioms is consistent, so is NF with the
Axiom of Counting.** -/
theorem consistent_nfc_of_consistent_zcr (h : Entailment.Consistent 𝗭𝗖𝗥) :
    Entailment.Consistent 𝗡𝗙𝗖 :=
  consistent_nfc_of_consistent_zr (h.of_subset zr_subset_zcr)

/-- **If NF with the Axiom of Counting is consistent, so is Zermelo set theory with Choice
and the rank axioms.** -/
theorem consistent_zcr_of_consistent_nfc (h : Entailment.Consistent 𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭𝗖𝗥 :=
  consistent_zcr_of_consistent_mhr (consistent_nfc_iff_consistent_mhr.mp h)

/-- **NF with the Axiom of Counting is consistent exactly when Zermelo set theory with Choice
and the rank axioms is.** -/
theorem consistent_nfc_iff_consistent_zcr :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗭𝗖𝗥 :=
  ⟨consistent_zcr_of_consistent_nfc, consistent_nfc_of_consistent_zcr⟩

/-- NFU + Infinity + the Axiom of Counting is consistent exactly when `𝗭𝗖𝗥` is. -/
theorem consistent_nfuic_iff_consistent_zcr :
    Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖 ↔ Entailment.Consistent 𝗭𝗖𝗥 :=
  ⟨fun h => consistent_zcr_of_consistent_mhr (consistent_nfuic_iff_consistent_mhr.mp h),
    fun h => consistent_nfuic_iff_consistent_zr.mpr (h.of_subset zr_subset_zcr)⟩

/-- Zermelo set theory with the rank axioms is consistent exactly when it is consistent with
Choice. -/
theorem consistent_zr_iff_consistent_zcr :
    Entailment.Consistent 𝗭𝗥 ↔ Entailment.Consistent 𝗭𝗖𝗥 :=
  ⟨fun h => consistent_zcr_of_consistent_nfc (consistent_nfc_of_consistent_zr h),
    fun h => h.of_subset zr_subset_zcr⟩

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_iff_consistent_zcr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfuic_iff_consistent_zcr
#print axioms FFL.FirstOrder.SetTheory.consistent_zr_iff_consistent_zcr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_iff_consistent_zr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_of_consistent_zcr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_iff_consistent_ztr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_iff_consistent_mr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfuic_iff_consistent_ztr
#print axioms FFL.FirstOrder.SetTheory.consistent_ztr_of_consistent_nfc
#print axioms FFL.FirstOrder.SetTheory.consistent_zr_of_consistent_nfc
