module

public import NFUAleph
public import NFUInterpretsZ

@[expose] public section

set_option autoImplicit false

/-!
# `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭𝗔 n`: Zermelo set theory with "`ℵₙ` exists"

For each `n`, the translation of the language of set theory into `𝗡𝗙𝗨𝗜𝗖` whose domain is
`HinU.InXA n`: the types in the levels over the `(n + 1)`-st iterate of Hartogs' set over the
finite ordinals. Membership is `Hin.EE` and equality is equality.

* `alephModel_models`: in a model of `𝗡𝗙𝗨𝗜𝗖`, the interpreted structure is a model of `𝗭𝗔 n`,
  Zermelo set theory with the sentence "`ℵₙ` exists" of `AlephTheory.lean`.
* **`nfuicInterpretsZA n : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭𝗔 n`**, and by composition `fncInterpretsZA`,
  `fnkInterpretsZA`, `nfcInterpretsZA`.
* `za_provable_aleph`: `𝗭𝗔 n` proves "`ℵₖ` exists" for every `k ≤ n`.
* **`consistent_zaω_of_consistent_nfuic`**: if `𝗡𝗙𝗨𝗜𝗖` is consistent then so is `𝗭𝗔ω`, Zermelo set
  theory with "`ℵₙ` exists" for every `n`. The domain of the interpretation depends on `n`, so
  this is obtained from the interpretations of the theories `𝗭𝗔 n` and the compactness of
  derivations; there is no single interpretation of `𝗭𝗔ω` here.

This is Proposition 17.8 of the draft *Choice and Consistency Strength in NF and NFU* (v15), for
the membership language. The draft's target theory has in addition symbols for the rank and
the cumulative hierarchy; these are not in the theories of this file.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula DirectTranslation

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

section defs

variable {V : Type} [SetStructure V]

/-- `x` belongs to a level over the `(n + 1)`-st iterate of Hartogs' set. -/
def InXA (n : ℕ) (x : V) : Prop :=
  ∃ B RH W : V, IsB (n + 1) B ∧ IsRH B RH ∧ IsWG B RH W ∧ InXG B W x

end defs

def inXAD (n : ℕ) : SDef ![6] (fun _ _ v ↦ InXA n (v 0)) :=
  (SDef.ex 7 (SDef.ex 9 (SDef.ex 9 (((isBD (n + 1)).comp ![2] 0).and
    ((isRHD.comp ![2, 1] 0).and ((isWGD.comp ![2, 1, 0] 0).and
      (inXGD.comp ![2, 0, 3] 0))))))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

omit [Nonempty V] hT in
theorem closedG_congr {A A' R R' C : V} (hA : ∀ x, x ∈ A ↔ x ∈ A') (hR : ∀ p, p ∈ R ↔ p ∈ R')
    (h : ClosedG A R C) : ClosedG A' R' C := by
  intro a x p ha hx hh hp
  refine h a x p ((hA a).mpr ha) hx (hh.imp id fun hu u hux => ?_) hp
  obtain ⟨b, ⟨q, hq, hqop⟩, hl⟩ := hu u hux
  exact ⟨b, ⟨q, (hR q).mpr hq, hqop⟩, hl⟩

omit [Nonempty V] hT in
/-- The set of the levels depends only on the members of the index set and of the relation. -/
theorem wg_congr {A A' R R' W W' : V} (hA : ∀ x, x ∈ A ↔ x ∈ A') (hR : ∀ p, p ∈ R ↔ p ∈ R')
    (hW : IsWG A R W) (hW' : IsWG A' R' W') (p : V) : p ∈ W ↔ p ∈ W' := by
  have e : (∀ C : V, ClosedG A R C → p ∈ C) ↔ ∀ C : V, ClosedG A' R' C → p ∈ C :=
    ⟨fun h C hC => h C (closedG_congr (fun x => (hA x).symm) (fun q => (hR q).symm) hC),
      fun h C hC => h C (closedG_congr hA hR hC)⟩
  exact (hW p).trans (e.trans (hW' p).symm)

omit [Nonempty V] hT in
theorem rh_congr {A A' RH RH' : V} (hA : ∀ x, x ∈ A ↔ x ∈ A') (h : IsRH A RH)
    (h' : IsRH A' RH') (p : V) : p ∈ RH ↔ p ∈ RH' := by
  have e : (∃ b a : V, IsOp p b a ∧ b ∈ A ∧ a ∈ A ∧ EE b a) ↔
      ∃ b a : V, IsOp p b a ∧ b ∈ A' ∧ a ∈ A' ∧ EE b a :=
    ⟨fun ⟨b, a, hp, hb, ha, he⟩ => ⟨b, a, hp, (hA b).mp hb, (hA a).mp ha, he⟩,
      fun ⟨b, a, hp, hb, ha, he⟩ => ⟨b, a, hp, (hA b).mpr hb, (hA a).mpr ha, he⟩⟩
  exact (h p).trans (e.trans (h' p).symm)

omit [Nonempty V] hT in
/-- The domain does not depend on the choice of the sets. -/
theorem inXA_iff {n : ℕ} {B RH W : V} (hB : IsB (n + 1) B) (hRH : IsRH B RH)
    (hW : IsWG B RH W) (x : V) : InXA n x ↔ InXG B W x := by
  constructor
  · rintro ⟨B', RH', W', hB', hRH', hW', a, ha, p, hp, hpW⟩
    have hA := isB_ext (n + 1) hB' hB
    exact ⟨a, (hA a).mp ha, p, hp, (wg_congr hA (rh_congr hA hRH' hRH) hW' hW p).mp hpW⟩
  · exact fun h => ⟨B, RH, W, hB, hRH, hW, h⟩

/-- The domain has an element. -/
theorem exists_inXA (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (n : ℕ) :
    ∃ x : V, InXA n x := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  obtain ⟨A, hA⟩ := exists_B (V := V) (n + 1)
  obtain ⟨RH, hRH⟩ := exists_isRH A
  obtain ⟨W, hW⟩ := exists_WG A RH
  obtain ⟨o, ho⟩ := exists_zero (V := V)
  have hoA : o ∈ A := (isB_good hC hg (n + 1) hA).om o (om_zero ho)
  exact ⟨o, A, RH, W, hA, hRH, hW, o, hoA, levG_intro hW hoA ho.1 (Or.inl (om_zero ho))⟩

/-- **The structure of the types in the domain satisfies the conditions for a model of `𝗭`, and
"`ℵₙ` exists" holds in it.** -/
theorem aleph_of_embed (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (n : ℕ) {D : Type}
    [SetStructure D] (i : D → V) (hi : Function.Injective i)
    (hdom : ∀ x : V, InXA n x ↔ ∃ w, i w = x) (hmem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b)) :
    (IsMacBase D ∧ ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → D) (t : D),
      ∃ y : D, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := D) ![z] ε ψ) ∧ ∃ y : D, IsAleph n y := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  obtain ⟨A, hA⟩ := exists_B (V := V) (n + 1)
  obtain ⟨RH, hRH⟩ := exists_isRH A
  obtain ⟨W, hW⟩ := exists_WG A RH
  have hdom' : ∀ x : V, InXG A W x ↔ ∃ w, i w = x := fun x =>
    (inXA_iff hA hRH hW x).symm.trans (hdom x)
  have hA' : ∃ B : V, IsB n B ∧ ∀ α : V, α ∈ A ↔ InH B α := hA
  obtain ⟨B, hB, hAH⟩ := hA'
  have M := levModel_of hg (isB_good hC hg n hB) (isB_good hC hg (n + 1) hA) hAH hRH hW hi
    hdom' hmem
  exact ⟨base_of_levelsG hg M.ok hW i hi hdom' hmem, aleph_in_levels hC M hA⟩

end model

end HinU

/-- A structure that satisfies the conditions and "`ℵₙ` exists" is a model of `𝗭𝗔 n`. -/
theorem models_za_of_base {W : Type} [SetStructure W] [Nonempty W] (n : ℕ) (h : IsMacBase W)
    (hsep : ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W),
      ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ)
    (hal : ∃ y : W, IsAleph n y)
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W] :
    W↓[ℒₛₑₜ] ⊧* 𝗭𝗔 n := by
  rcases standardStructure_unique W s
  have hZ : W↓[ℒₛₑₜ] ⊧* 𝗭 := models_z_of_base h hsep
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp hZ φ hφ
  · rw [Set.mem_singleton_iff.mp hφ]
    exact models_aleph_iff.mpr hal

section

variable {M : Type} [SetStructure M]

lemma alephDomain_val_iff (n : ℕ) (x : M) :
    (⟨(HinU.inXAD n).φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] ↔ HinU.InXA n x :=
  (HinU.inXAD n).eval M ![x]

end

/-- **The translation of `ℒₛₑₜ` into `𝗡𝗙𝗨𝗜𝗖` for `ℵₙ`**: the domain is `HinU.InXA n`, membership
is `Hin.EE`, and equality is equality. -/
def alephTranslation (n : ℕ) : DirectTranslation 𝗡𝗙𝗨𝗜𝗖 ℒₛₑₜ where
  domain := ⟨(HinU.inXAD n).φ⟩
  rel := macRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    obtain ⟨hU, hC⟩ := nfuic_models hTC
    have := hU
    obtain ⟨x, hx⟩ := HinU.exists_inXA (V := M) hC n
    suffices ∃ x : M, (⟨(HinU.inXAD n).φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨x, (alephDomain_val_iff n x).mpr hx⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : macRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖] (n : ℕ)

/-- The membership relation of the interpreted structure. -/
instance alephModel_setStructure : SetStructure ((alephTranslation n).Model M) :=
  ⟨fun y x ↦ Hin.EE (x : M) (y : M)⟩

omit [Nonempty M] hTC in
lemma alephModel_mem_iff (a b : (alephTranslation n).Model M) :
    a ∈ b ↔ Hin.EE (a : M) (b : M) := Iff.rfl

instance alephModel_mem : Tarski.Structure.Mem ℒₛₑₜ ((alephTranslation n).Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : (alephTranslation n).Model M) : M)) =
        ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact macMem_val_iff _ _

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the interpreted structure is a model of `𝗭𝗔 n`.** -/
theorem alephModel_models : ((alephTranslation n).Model M)↓[ℒₛₑₜ] ⊧* 𝗭𝗔 n := by
  obtain ⟨hU, hC⟩ := nfuic_models hTC
  have := hU
  obtain ⟨⟨hbase, hsep⟩, hal⟩ := HinU.aleph_of_embed hC n
    (fun a : (alephTranslation n).Model M ↦ (a : M))
    (fun a b h => by cases a; cases b; cases h; rfl)
    (fun x => ⟨fun hx => ⟨⟨x, (alephDomain_val_iff n x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (alephDomain_val_iff n _).mp w.dom⟩)
    (alephModel_mem_iff n)
  exact models_za_of_base n hbase hsep hal

end model

/-- **NFU + Infinity + the Axiom of Counting interprets Zermelo set theory with "`ℵₙ` exists"**,
for each `n`. The source theory is Jensen's NFU in the language of membership and equality,
with no axiom of choice and no type-level pair. -/
instance nfuicInterpretsZA (n : ℕ) : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭𝗔 n where
  trln := alephTranslation n
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp (alephModel_models n) φ hφ)

/-- **FunctionNF with count interprets `𝗭𝗔 n`**, through `𝗙𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance fncInterpretsZA (n : ℕ) : 𝗙𝗡𝗙𝗖 ⊳ 𝗭𝗔 n :=
  DirectInterpretation.comp (nfuicInterpretsZA n) FNF.fncInterpretsNFUIC

/-- **FunctionNF with count′ interprets `𝗭𝗔 n`**, through `𝗙𝗡𝗙𝗞 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance fnkInterpretsZA (n : ℕ) : 𝗙𝗡𝗙𝗞 ⊳ 𝗭𝗔 n :=
  DirectInterpretation.comp (nfuicInterpretsZA n) FNF.fnkInterpretsNFUIC

/-- **NF with the Axiom of Counting interprets `𝗭𝗔 n`**, through `𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖`. -/
instance nfcInterpretsZA (n : ℕ) : 𝗡𝗙𝗖 ⊳ 𝗭𝗔 n :=
  DirectInterpretation.comp (nfuicInterpretsZA n) nfcInterpretsNFUIC

/-! ### All the alephs: compactness -/

/-- If "`ℵₙ` exists" holds then "`ℵₖ` exists" holds for `k ≤ n`. -/
theorem isAleph_down {N : Type} [SetStructure N] :
    ∀ (j : ℕ) {k : ℕ} {y : N}, IsAleph (k + j) y → ∃ x : N, IsAleph k x
  | 0, _, y, h => ⟨y, h⟩
  | j + 1, _, _, ⟨_, hx, _⟩ => isAleph_down j hx

/-- `𝗭𝗔 n` proves "`ℵₖ` exists" for `k ≤ n`. -/
theorem za_provable_aleph {n k : ℕ} (h : k ≤ n) : 𝗭𝗔 n ⊢ Axiom.aleph k := by
  apply SetTheory.complete.{0}
  intro M _ _ hM
  obtain ⟨y, hy⟩ := models_aleph_iff.mp (models_theory_iff.mp hM _ (Or.inr rfl))
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact models_aleph_iff.mpr (isAleph_down j hy)

/-- **Compactness.** If every `𝗭𝗔 n` is consistent then `𝗭𝗔ω` is consistent. -/
theorem consistent_zaω_of_forall (h : ∀ n, Entailment.Consistent (𝗭𝗔 n)) :
    Entailment.Consistent 𝗭𝗔ω := by
  by_contra hZ
  have hbot : 𝗭𝗔ω ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  obtain ⟨𝓕, h𝓕, hfin, hF⟩ := Entailment.Compact.finite_provable hbot
  have key : ∀ S : Set (Sentence ℒₛₑₜ), S.Finite → S ⊆ 𝗭𝗔ω →
      ∃ N : ℕ, ∀ φ ∈ S, φ ∈ 𝗭 ∨ ∃ k, k ≤ N ∧ φ = Axiom.aleph k := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0, fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩
    | @insert ψ S _ _ ih =>
      intro hsub
      obtain ⟨N, hN⟩ := ih fun φ hφ => hsub (Set.mem_insert_of_mem _ hφ)
      rcases hsub (Set.mem_insert ψ S) with hψ | ⟨k, rfl⟩
      · refine ⟨N, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inl hψ
        · exact hN φ hφ
      · refine ⟨max N k, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inr ⟨k, le_max_right _ _, rfl⟩
        · rcases hN φ hφ with h' | ⟨j, hj, rfl⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, le_trans hj (le_max_left _ _), rfl⟩
  obtain ⟨N, hN⟩ := key 𝓕 ((Set.adjunctiveSet_finite_iff 𝓕).mp hfin) h𝓕
  have hle : 𝓕 ⪯ 𝗭𝗔 N := Entailment.WeakerThan.ofAxm! fun {φ} hφ => by
    rcases hN φ hφ with h' | ⟨k, hk, rfl⟩
    · exact Entailment.by_axm (Or.inl h')
    · exact za_provable_aleph hk
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (hle.pbl hF)) (h N)

/-- An interpretation transfers consistency. -/
theorem consistent_of_interprets {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]
    {U : Theory L₂} (I : T ⊳ U) (h : Entailment.Consistent T) : Entailment.Consistent U := by
  by_contra hU
  have hbot : U ⊢ (⊥ : Sentence L₂) := Entailment.not_consistent_iff_inconsistent.mp hU ⊥
  have hbot' : T ⊢ (⊥ : Sentence L₁) := by simpa using DirectInterpretation.sound I hbot
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable hbot') h

/-- If NFU + Infinity + the Axiom of Counting is consistent then so is `𝗭𝗔 n`. -/
theorem consistent_za_of_consistent_nfuic (h : Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖) (n : ℕ) :
    Entailment.Consistent (𝗭𝗔 n) := consistent_of_interprets (nfuicInterpretsZA n) h

/-- **If NFU + Infinity + the Axiom of Counting is consistent then so is Zermelo set theory with
"`ℵₙ` exists" for every `n`.** -/
theorem consistent_zaω_of_consistent_nfuic (h : Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖) :
    Entailment.Consistent 𝗭𝗔ω :=
  consistent_zaω_of_forall fun n => consistent_za_of_consistent_nfuic h n

/-- If FunctionNF with count is consistent then so is `𝗭𝗔ω`. -/
theorem consistent_zaω_of_consistent_fnc (h : Entailment.Consistent 𝗙𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭𝗔ω :=
  consistent_zaω_of_forall fun n => consistent_of_interprets (fncInterpretsZA n) h

/-- If FunctionNF with count′ is consistent then so is `𝗭𝗔ω`. -/
theorem consistent_zaω_of_consistent_fnk (h : Entailment.Consistent 𝗙𝗡𝗙𝗞) :
    Entailment.Consistent 𝗭𝗔ω :=
  consistent_zaω_of_forall fun n => consistent_of_interprets (fnkInterpretsZA n) h

/-- If NF with the Axiom of Counting is consistent then so is `𝗭𝗔ω`. -/
theorem consistent_zaω_of_consistent_nfc (h : Entailment.Consistent 𝗡𝗙𝗖) :
    Entailment.Consistent 𝗭𝗔ω :=
  consistent_zaω_of_forall fun n => consistent_of_interprets (nfcInterpretsZA n) h

end FFL.FirstOrder.SetTheory
