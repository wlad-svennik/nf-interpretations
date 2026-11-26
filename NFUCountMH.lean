module

public import NFUInterpretsAleph
public import NFUDirectMH
public import MHAleph

@[expose] public section

set_option autoImplicit false

/-!
# `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗛𝗔ω`: one interpretation for all the alephs

`NFUDirectMH.lean` interprets `𝗠𝗛` in `𝗡𝗙𝗨𝗜` on the types that belong to a stable transitive set
(`Hin.Dom`). `NFUInterpretsAleph.lean` interprets `𝗭𝗔 n` in `𝗡𝗙𝗨𝗜𝗖` on the types in the levels over
the `(n + 1)`-st iterate of Hartogs' set; that domain depends on `n`.

With the Axiom of Counting the levels are stable transitive sets, so every one of those domains
is included in `Hin.Dom`. The structure on `Hin.Dom` therefore satisfies `𝗠𝗛` and "`ℵₙ` exists"
for every `n` at once.

* `dom_of_levG`: the types in the levels over an index set of fixed types are in `Hin.Dom`.
* `dom_sub`: every set of members of an element of `Hin.Dom` is the extension of an element of
  `Hin.Dom`. `emb_of_dom`: the structure on `Hin.Dom` is embedded in the sense of `NFUAleph.lean`.
* `aleph_in_dom`: with the Axiom of Counting, "`ℵₙ` exists" holds in the structure on `Hin.Dom`,
  for every `n`.
* `𝗠𝗛𝗔ω` (`MHAleph.lean`): `𝗠𝗛` with "`ℵₙ` exists" for every `n`.
* **`nfuicInterpretsMHA : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗛𝗔ω`**; `fncInterpretsMHA`, `fnkInterpretsMHA`, `nfcInterpretsMHA`
  by composition.
* **`nfuicInterpretsMACA : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗔𝗖𝗔ω`**, through `mhaInterpretsMACA` of `MHAleph.lean`; the same
  for `𝗙𝗡𝗙𝗖`, `𝗙𝗡𝗙𝗞`, `𝗡𝗙𝗖`.

The Axiom of Counting is not needed for these sentences: `𝗠𝗛` proves "`ℵₙ` exists" for every `n`
(`mh_provable_aleph` in `MHAleph.lean`, by Hartogs' theorem and the collapse axiom), so
**`nfuiInterpretsMACA : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖𝗔ω`** holds too. `aleph_in_dom` is a second proof, through the
levels of `NFUAleph.lean`.

`𝗠𝗛` has separation for bounded formulas only, so `𝗠𝗛𝗔ω` does not include `𝗭𝗔ω`. The structure
is the one in which the constructible sets are to be taken for the hosts of
`docs/ordinal_towers_2026-11-23.md`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula DirectTranslation

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD Dom)

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-- The types in the levels over an index set of fixed types are in the domain of the
interpretation of `𝗠𝗛`: the levels are stable transitive sets. -/
theorem dom_of_levG {g A R W x : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W)
    (h : InXG A W x) : Dom x := by
  obtain ⟨a, ha, hx⟩ := h
  obtain ⟨L, hL⟩ := exists_slice W a
  exact ⟨g, L, hg, levG_stable hg ok hW ha hL,
    fun y hy v hv => (hL v).mpr (levG_trans hW ok.trans ((hL y).mp hy) hv), (hL x).mpr hx⟩

/-- **Every set of members of an element of the domain is the extension of an element of the
domain.** -/
theorem dom_sub {x S : V} (hx : Dom x) (hS : ∀ s, s ∈ S → EE s x) :
    ∃ w, Dom w ∧ InZ w ∧ ∀ v, EE v w ↔ v ∈ S := by
  obtain ⟨g, X, hg, hX, hXt, hxX⟩ := hx
  obtain ⟨w, hwZ, hw⟩ := stable_full hg hX S fun s hs => hXt x hxX s (hS s hs)
  obtain ⟨P, hP⟩ := exists_pow X
  refine ⟨w, ⟨g, P, hg, pow_stable hg hX hP, fun y hy v hv => ?_,
    (hP w).mpr ⟨hwZ, fun u hu => hXt x hxX u (hS u ((hw u).mp hu))⟩⟩, hwZ, hw⟩
  have hvX := ((hP y).mp hy).2 v hv
  exact (hP v).mpr ⟨hX.1 v hvX, fun u hu => hXt v hvX u hu⟩

/-- The structure on the domain is embedded in the sense of `NFUAleph.lean`. -/
theorem emb_of_dom {D : Type} [SetStructure D] (i : D → V) (hi : Function.Injective i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (hmem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b)) :
    Emb i := by
  have base := isMacBase_of_embed i hi hdom hmem
  have hd : ∀ w : D, Dom (i w) := fun w => (hdom _).mpr ⟨w, rfl⟩
  have hup : ∀ a b : D, ∃ z : D, IsUp z a b := by
    intro a b
    obtain ⟨p, hap, hbp⟩ := base.pair a b
    obtain ⟨S, hS⟩ := exists_up (i a) (i b)
    obtain ⟨w, hwD, -, hw⟩ := dom_sub (hd p) (S := S) fun s hs => by
      rcases (hS s).mp hs with h | h
      · rw [h]; exact (hmem a p).mp hap
      · rw [h]; exact (hmem b p).mp hbp
    obtain ⟨z, rfl⟩ := (hdom w).mp hwD
    refine ⟨z, fun c => (hmem c z).trans ((hw (i c)).trans ((hS (i c)).trans ?_))⟩
    exact or_congr ⟨fun h => hi h, fun h => congrArg i h⟩ ⟨fun h => hi h, fun h => congrArg i h⟩
  refine ⟨hi, hmem, fun w => ?_, fun w v hv => ?_, fun a => ?_, hup⟩
  · obtain ⟨g, X, -, hX, -, hx⟩ := hd w
    exact hX.1 _ hx
  · obtain ⟨g, X, hg, hX, hXt, hx⟩ := hd w
    exact (hdom v).mp ⟨g, X, hg, hX, hXt, hXt _ hx v hv⟩
  · obtain ⟨z, hz⟩ := hup a a
    exact ⟨z, fun c => (hz c).trans ⟨fun h => h.elim id id, Or.inl⟩⟩

/-- **With the Axiom of Counting, "`ℵₙ` exists" holds in the structure on the domain, for every
`n`.** -/
theorem aleph_in_dom (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {D : Type}
    [SetStructure D] (i : D → V) (hi : Function.Injective i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (hmem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b))
    (n : ℕ) : ∃ y : D, IsAleph n y := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  obtain ⟨A, hA⟩ := exists_B (V := V) (n + 1)
  obtain ⟨RH, hRH⟩ := exists_isRH A
  obtain ⟨W, hW⟩ := exists_WG A RH
  have hA' : ∃ B : V, IsB n B ∧ ∀ α : V, α ∈ A ↔ InH B α := hA
  obtain ⟨B, hB, hAH⟩ := hA'
  have good := isB_good hC hg n hB
  have goodA := isB_good hC hg (n + 1) hA
  have ok : IdxOK g A RH := hart_idxOK hg good.fixed good.om hAH (rl_isRH hRH)
  have M : LevModel g A RH W i := ⟨hg, ok, hRH, hW, emb_of_dom i hi hdom hmem,
    fun x hx => (hdom x).mp (dom_of_levG hg ok hW hx), goodA.ord, goodA.down⟩
  exact aleph_in_levels hC M hA

end model

end HinU

/-- A structure that satisfies the conditions, the collapse axiom and "`ℵₙ` exists" for every `n`
is a model of `𝗠𝗛𝗔ω`. -/
theorem models_mha_of_base {W : Type} [SetStructure W] [Nonempty W] (h : IsMacBase W)
    (hc : MH.HC W) (hal : ∀ n : ℕ, ∃ y : W, IsAleph n y)
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W] :
    W↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗔ω := by
  have hMH : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := MH.models' h hc
  rcases standardStructure_unique W s
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | ⟨n, rfl⟩
  · exact models_theory_iff.mp hMH φ hφ
  · exact models_aleph_iff.mpr (hal n)

/-! ### The translation -/

/-- **The translation of `ℒₛₑₜ` into `𝗡𝗙𝗨𝗜𝗖` on the types**: the domain is `Hin.Dom`, membership is
`Hin.EE`, and equality is equality. -/
def macTranslationC : DirectTranslation 𝗡𝗙𝗨𝗜𝗖 ℒₛₑₜ where
  domain := ⟨Hin.domU.φ⟩
  rel := macRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    obtain ⟨hU, -⟩ := nfuic_models hTC
    have := hU
    obtain ⟨x, hx⟩ := HinU.exists_dom (V := M)
    suffices ∃ x : M, (⟨Hin.domU.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨x, (macDomainU_val_iff x).mpr hx⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : macRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖]

/-- The membership relation of the interpreted structure. -/
instance macModelC_setStructure : SetStructure (macTranslationC.Model M) :=
  ⟨fun y x ↦ Hin.EE (x : M) (y : M)⟩

omit [Nonempty M] hTC in
lemma macModelC_mem_iff (a b : macTranslationC.Model M) : a ∈ b ↔ Hin.EE (a : M) (b : M) :=
  Iff.rfl

instance macModelC_mem : Tarski.Structure.Mem ℒₛₑₜ (macTranslationC.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : macTranslationC.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact macMem_val_iff _ _

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the structure of the types in the domain is a model of `𝗠𝗛𝗔ω`.** -/
theorem macModelC_models : (macTranslationC.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗔ω := by
  obtain ⟨hU, hC⟩ := nfuic_models hTC
  have := hU
  have hi : Function.Injective (fun a : macTranslationC.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hdom : ∀ x : M, Hin.Dom x ↔ ∃ w : macTranslationC.Model M, (w : M) = x := fun x =>
    ⟨fun hx => ⟨⟨x, (macDomainU_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (macDomainU_val_iff _).mp w.dom⟩
  exact models_mha_of_base
    (HinU.isMacBase_of_embed _ hi hdom macModelC_mem_iff)
    (HinU.hc_of_embed _ hi hdom macModelC_mem_iff)
    (HinU.aleph_in_dom hC _ hi hdom macModelC_mem_iff)

end model

/-- **NFU + Infinity + the Axiom of Counting interprets `𝗠𝗛` with "`ℵₙ` exists" for every `n`**,
by one translation. -/
instance nfuicInterpretsMHA : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗛𝗔ω where
  trln := macTranslationC
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp macModelC_models φ hφ)

/-- FunctionNF with count interprets `𝗠𝗛𝗔ω`. -/
instance fncInterpretsMHA : 𝗙𝗡𝗙𝗖 ⊳ 𝗠𝗛𝗔ω :=
  DirectInterpretation.comp nfuicInterpretsMHA FNF.fncInterpretsNFUIC

/-- FunctionNF with count′ interprets `𝗠𝗛𝗔ω`. -/
instance fnkInterpretsMHA : 𝗙𝗡𝗙𝗞 ⊳ 𝗠𝗛𝗔ω :=
  DirectInterpretation.comp nfuicInterpretsMHA FNF.fnkInterpretsNFUIC

/-- NF with the Axiom of Counting interprets `𝗠𝗛𝗔ω`. -/
instance nfcInterpretsMHA : 𝗡𝗙𝗖 ⊳ 𝗠𝗛𝗔ω :=
  DirectInterpretation.comp nfuicInterpretsMHA nfcInterpretsNFUIC

/-- **NFU + Infinity + the Axiom of Counting interprets Mac Lane set theory with Choice and
"`ℵₙ` exists" for every `n`**: the constructible sets of the structure on the types. -/
instance nfuicInterpretsMACA : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhaInterpretsMACA nfuicInterpretsMHA

/-- **NFU + Infinity interprets Mac Lane set theory with Choice and "`ℵₙ` exists" for every
`n`**, without the Axiom of Counting: `𝗠𝗛` proves that the alephs exist (`mh_provable_aleph`). -/
instance nfuiInterpretsMACA : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhInterpretsMACA nfuiDirectMH

/-- If NFU + Infinity is consistent, so is `𝗠𝗔𝗖𝗔ω`. -/
theorem consistent_maca_of_consistent_nfui (h : Entailment.Consistent 𝗡𝗙𝗨𝗜) :
    Entailment.Consistent 𝗠𝗔𝗖𝗔ω := consistent_of_interprets nfuiInterpretsMACA h

/-- FunctionNF with count interprets `𝗠𝗔𝗖𝗔ω`. -/
instance fncInterpretsMACA : 𝗙𝗡𝗙𝗖 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhaInterpretsMACA fncInterpretsMHA

/-- FunctionNF with count′ interprets `𝗠𝗔𝗖𝗔ω`. -/
instance fnkInterpretsMACA : 𝗙𝗡𝗙𝗞 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhaInterpretsMACA fnkInterpretsMHA

/-- NF with the Axiom of Counting interprets `𝗠𝗔𝗖𝗔ω`. -/
instance nfcInterpretsMACA : 𝗡𝗙𝗖 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhaInterpretsMACA nfcInterpretsMHA

end FFL.FirstOrder.SetTheory
