module

public import NFUCountZ

@[expose] public section

set_option autoImplicit false

/-!
# `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭`: the interpretation

The translation of the language of set theory into `𝗡𝗙𝗨𝗜𝗖`, Jensen's NFU + Infinity + the Axiom
of Counting: the domain is `HinU.InX` (the types of well-founded pointed graphs that belong to
a level `Pⁿ(Ω)`), membership is `Hin.EE`, and equality is equality.

* `zModel_models`: in a model of `𝗡𝗙𝗨𝗜𝗖`, the interpreted structure is a model of `𝗭`.
* **`nfuicInterpretsZ : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭`.**
* By composition with the interpretations of `FnCount.lean`, `FnCountNFU.lean` and
  `NFInterpretsFnCount.lean`: `fncInterpretsZ : 𝗙𝗡𝗙𝗖 ⊳ 𝗭`, `fnkInterpretsZ : 𝗙𝗡𝗙𝗞 ⊳ 𝗭`,
  `nfcInterpretsZ : 𝗡𝗙𝗖 ⊳ 𝗭`.
* `consistent_z_of_consistent_nfuic`, `consistent_z_of_consistent_fnc`,
  `consistent_z_of_consistent_nfc`.

Every derivation here is obtained from the completeness theorem of the library and a theorem
about models, as in `NFInterpretsMac.lean`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula DirectTranslation

/-- A model of `𝗡𝗙𝗨𝗜𝗖` is a model of `𝗡𝗙𝗨𝗜` and satisfies the Axiom of Counting. -/
lemma nfuic_models {M : Type} [SetStructure M] [Nonempty M] (hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖) :
    M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 ∧ JensenNFU.Counting (fun a b : M => a ∈ b) :=
  ⟨models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hT φ (Or.inl hφ),
    models_counting_iff.mp (models_theory_iff.mp hT _ (Or.inr rfl))⟩

section

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

omit [Nonempty M] hT in
lemma zDomain_val_iff (x : M) :
    (⟨HinU.inXD.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] ↔ HinU.InX x :=
  HinU.inXD.eval M ![x]

/-- The type without members belongs to the level `0`. -/
theorem exists_inX : ∃ x : M, HinU.InX x := by
  obtain ⟨W, hW⟩ := HinU.exists_W (V := M)
  obtain ⟨z, hz⟩ := HinU.exists_zeroN (V := M)
  obtain ⟨o, ho⟩ := HinU.exists_zero (V := M)
  exact ⟨o, W, z, hW, HinU.natN_zero hz, HinU.lev_zero hW hz (HinU.om_zero ho)⟩

end

/-- **The translation of `ℒₛₑₜ` into `𝗡𝗙𝗨𝗜𝗖`**: the domain is `HinU.InX`, membership is `Hin.EE`,
and equality is equality. -/
def zTranslation : DirectTranslation 𝗡𝗙𝗨𝗜𝗖 ℒₛₑₜ where
  domain := ⟨HinU.inXD.φ⟩
  rel := macRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    have : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := (nfuic_models hTC).1
    obtain ⟨x, hx⟩ := exists_inX (M := M)
    suffices ∃ x : M, (⟨HinU.inXD.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨x, (zDomain_val_iff x).mpr hx⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : macRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖]

/-- The membership relation of the interpreted structure. -/
instance zModel_setStructure : SetStructure (zTranslation.Model M) :=
  ⟨fun y x ↦ Hin.EE (x : M) (y : M)⟩

omit [Nonempty M] hTC in
lemma zModel_mem_iff (a b : zTranslation.Model M) : a ∈ b ↔ Hin.EE (a : M) (b : M) := Iff.rfl

instance zModel_mem : Tarski.Structure.Mem ℒₛₑₜ (zTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : zTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact macMem_val_iff _ _

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the interpreted structure is a model of `𝗭`.** -/
theorem zModel_models : (zTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗭 := by
  obtain ⟨hU, hC⟩ := nfuic_models hTC
  have := hU
  obtain ⟨hbase, hsep⟩ := HinU.base_of_embed hC (fun a : zTranslation.Model M ↦ (a : M))
    (fun a b h => by cases a; cases b; cases h; rfl)
    (fun x => ⟨fun hx => ⟨⟨x, (zDomain_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (zDomain_val_iff _).mp w.dom⟩)
    zModel_mem_iff
  exact models_z_of_base hbase hsep

end model

/-- **NFU + Infinity + the Axiom of Counting interprets Zermelo set theory** (with separation
for all formulas and without choice). The source theory is Jensen's NFU in the language of
membership and equality, with no axiom of choice and no type-level pair. -/
instance nfuicInterpretsZ : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭 where
  trln := zTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp zModel_models φ hφ)

/-- **FunctionNF with count interprets Zermelo set theory**, through `𝗙𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance fncInterpretsZ : 𝗙𝗡𝗙𝗖 ⊳ 𝗭 := DirectInterpretation.comp nfuicInterpretsZ FNF.fncInterpretsNFUIC

/-- **FunctionNF with count′ interprets Zermelo set theory**, through `𝗙𝗡𝗙𝗞 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance fnkInterpretsZ : 𝗙𝗡𝗙𝗞 ⊳ 𝗭 := DirectInterpretation.comp nfuicInterpretsZ FNF.fnkInterpretsNFUIC

/-- **NF with the Axiom of Counting interprets Zermelo set theory**, through `𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance nfcInterpretsZ : 𝗡𝗙𝗖 ⊳ 𝗭 := DirectInterpretation.comp nfuicInterpretsZ nfcInterpretsNFUIC

/-- **The syntactic transformation.** The translation of a theorem of `𝗭` is a theorem of
`𝗡𝗙𝗨𝗜𝗖`. -/
theorem nfuic_provable_translate_of_z {σ : Sentence ℒₛₑₜ} (h : 𝗭 ⊢ σ) :
    𝗡𝗙𝗨𝗜𝗖 ⊢ nfuicInterpretsZ σ :=
  DirectInterpretation.sound nfuicInterpretsZ h

/-- If NFU + Infinity + the Axiom of Counting is consistent then so is Zermelo set theory. -/
theorem consistent_z_of_consistent_nfuic (h : Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖) :
    Entailment.Consistent 𝗭 := by
  by_contra hZ
  have hbot : 𝗭 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  have := nfuic_provable_translate_of_z hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simp at this)) h

/-- If FunctionNF with count is consistent then so is Zermelo set theory. -/
theorem consistent_z_of_consistent_fnc (h : Entailment.Consistent 𝗙𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭 := by
  by_contra hZ
  have hbot : 𝗭 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  have := DirectInterpretation.sound fncInterpretsZ hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simpa using this)) h

/-- If NF with the Axiom of Counting is consistent then so is Zermelo set theory. -/
theorem consistent_z_of_consistent_nfc (h : Entailment.Consistent 𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭 := by
  by_contra hZ
  have hbot : 𝗭 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  have := DirectInterpretation.sound nfcInterpretsZ hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (by simp at this)) h

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.HinU.lev_theta
#print axioms FFL.FirstOrder.SetTheory.zModel_models
#print axioms FFL.FirstOrder.SetTheory.nfuicInterpretsZ
#print axioms FFL.FirstOrder.SetTheory.fncInterpretsZ
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsZ
#print axioms FFL.FirstOrder.SetTheory.consistent_z_of_consistent_nfuic
