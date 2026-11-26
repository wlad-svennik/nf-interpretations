module

public import NFUSupply
public import MHRankSupply

@[expose] public section

set_option autoImplicit false

/-!
# The rank axioms in a model of `𝗡𝗙𝗨𝗜𝗖`, and the equiconsistency of `𝗡𝗙𝗖` and `𝗠𝗛𝗥`

`MHRank.lean` states the rank axioms and the theory `𝗠𝗛𝗥`; `MHRankSupply.lean` proves
`Con(𝗠𝗛𝗥) → Con(𝗡𝗙𝗖)`. Here the rank axioms are proved in the model of `𝗠𝗛` on the types of a
model of `𝗡𝗙𝗨𝗜𝗖` (`NFUCountMH.lean`).

* `exists_levels`: for a set `T` of the structure whose members are fixed types, with `ρ` the
  least ordinal of the structure that does not map one-to-one into `T`, the structure has a
  sequence of sets on the ordinals up to `ρ`, each including `ω`, with every subset of an
  earlier one a member of each later one. The sets are the levels (`NFULevels.lean`) over the
  pairs of an ordinal up to `ρ` and zero, as in `exists_supply`.
* `pw_fixed`: with the Axiom of Counting, the members of the iterated power sets of `ω` of the
  structure are fixed types.
* `rank_in_dom`: the rank axiom for every `n` holds in the structure
  (`MH.hasRank_of_levels`).
* **`nfuicInterpretsMHR : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗛𝗥`**, by the translation `macTranslationC`, and
  **`nfcInterpretsMHR : 𝗡𝗙𝗖 ⊳ 𝗠𝗛𝗥`**.
* **`consistent_nfc_iff_consistent_mhr : Con(𝗡𝗙𝗖) ↔ Con(𝗠𝗛𝗥)`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula DirectTranslation

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD Dom)

section levels

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] [Nonempty D] [hH : D↓[ℒₛₑₜ] ⊧* 𝗠𝗛] {i : D → V}

/-- **A sequence of levels on the ordinals up to Hartogs' ordinal of a set of fixed types.** -/
theorem exists_levels (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (T : D)
    (hfix : ∀ g : V, IsEg g → ∀ z : D, z ∈ T → Fixed g (i z)) :
    ∃ ρ Sq : D, NextS T ρ ∧
      ((∀ α, α ∈ MH.sc ρ → ∃ S, MH.Pr Sq α S) ∧
      ((∀ α S S', MH.Pr Sq α S → MH.Pr Sq α S' → S = S') ∧
      ((∀ α S, α ∈ MH.sc ρ → MH.Pr Sq α S → ∀ n, n ∈ (MH.om : D) → n ∈ S) ∧
      (∀ α β S S', α ∈ β → β ∈ MH.sc ρ → MH.Pr Sq α S → MH.Pr Sq β S' →
        (∀ z, z ∈ S → z ∈ S') ∧ ∀ x, (∀ z, z ∈ x → z ∈ S) → x ∈ S')))) := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  -- Hartogs' ordinal of `T`, in the structure
  obtain ⟨ρ, hρ⟩ := MH.next_exists T
  have hρO : MH.Ord ρ := MH.ord_of_ordS hρ.1
  have hρinj : ∀ ζ : D, ζ ∈ ρ → MH.VInj ζ T := fun ζ hζ => hρ.2.2 ζ hζ
  -- the types that are members of `T`, and the members of `ρ`
  obtain ⟨B, hB⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehensionU ![i T]
  have hB' : ∀ v, v ∈ B ↔ EE v (i T) := hB
  have hBfix : ∀ b, b ∈ B → Fixed g b := fun b hb => by
    obtain ⟨z, rfl⟩ := E.down _ _ ((hB' b).mp hb)
    exact hfix g hg z ((E.mem _ _).mpr ((hB' _).mp hb))
  have hρfix : ∀ ζ : D, ζ ∈ ρ → Fixed g (i ζ) := fun ζ hζ =>
    hart_fixed hg hBfix (inH_of_vinj E (MH.ord_mem hρO hζ) (hρinj ζ hζ)
      fun v hv => (hB' v).mpr hv)
  obtain ⟨B₂, hB₂⟩ := ((eeD.comp (τ' := ![6, 6, 6]) ![0, 1] 0).or
    (eeD.comp ![0, 2] 0)).comprehensionU ![i T, i ρ]
  have hB₂' : ∀ v, v ∈ B₂ ↔ EE v (i T) ∨ EE v (i ρ) := hB₂
  have hB₂fix : ∀ b, b ∈ B₂ → Fixed g b := fun b hb => by
    rcases (hB₂' b).mp hb with h | h
    · exact hBfix b ((hB' b).mpr h)
    · obtain ⟨ζ, rfl⟩ := E.down _ _ h
      exact hρfix ζ ((E.mem _ _).mpr h)
  obtain ⟨H, hHs⟩ := exists_H B₂
  have hinH : ∀ ξ : D, MH.Ord ξ → (∀ ζ, ζ ∈ ξ → ζ ∈ ρ) → i ξ ∈ H := fun ξ hξ hsub =>
    (hHs _).mpr (inH_of_sub (isOrd_of_ord E hξ) fun u hu => by
      obtain ⟨ζ, rfl⟩ := E.down _ _ hu
      exact (hB₂' _).mpr (Or.inr ((E.mem _ _).mp (hsub ζ ((E.mem _ _).mpr hu)))))
  have hρH : i ρ ∈ H := hinH ρ hρO fun ζ h => h
  have hsH : ∀ ξ : D, ξ ∈ MH.sc ρ → i ξ ∈ H := fun ξ hξ => by
    rcases MH.mem_sc.mp hξ with e | e
    · rw [e]
      exact hρH
    · exact hinH ξ (MH.ord_mem hρO e) fun ζ hζ => hρO.1 ξ e ζ hζ
  have lo : LexOK g H := ⟨fun a ha => hart_fixed hg hB₂fix ((hHs a).mp ha),
    fun a ha => ((hHs a).mp ha).1, fun a u ha hu => (hHs u).mpr (hart_down ((hHs a).mp ha) hu),
    ⟨i ρ, hρH⟩⟩
  -- the index set and the levels
  obtain ⟨A₂, hA₂⟩ := (lexAD.comp (τ' := ![6, 7]) ![1, 0] 0).comprehensionU ![H]
  have hA₂' : ∀ p, p ∈ A₂ ↔ LexA H p := hA₂
  obtain ⟨R₂, hR₂⟩ := exists_rel 6 lexRD ![H]
  have hR₂' : ∀ p p', Rl R₂ p p' ↔ LexR p p' H := hR₂
  have ok : IdxOK g A₂ R₂ := lex_idxOK hC hg lo hA₂' hR₂'
  obtain ⟨W, hW⟩ := exists_WG A₂ R₂
  obtain ⟨z₀, hz₀⟩ := exists_zero (V := V)
  have hn₀ : InOm z₀ := om_zero hz₀
  have pair : ∀ a : V, a ∈ H → ∃ p, EOp p a z₀ ∧ p ∈ A₂ := fun a ha => by
    obtain ⟨p, hp, -⟩ := eop_of_fixed hg (lo.fixed a ha) (om_fixed hC hg hn₀)
    exact ⟨p, hp, (hA₂' p).mpr ⟨a, z₀, ha, hn₀, hp⟩⟩
  have inA : ∀ {p a : V}, a ∈ H → EOp p a z₀ → p ∈ A₂ :=
    fun ha hp => (hA₂' _).mpr ⟨_, _, ha, hn₀, hp⟩
  have lexlt : ∀ {p p' a a' : V}, EOp p a z₀ → EOp p' a' z₀ → a ∈ H → a' ∈ H → EE a a' →
      Rl R₂ p p' :=
    fun hp hp' ha ha' h => (hR₂' _ _).mpr ⟨_, _, _, _, hp, hp', ha, ha', hn₀, hn₀, Or.inl h⟩
  -- the top level
  obtain ⟨pt, hpt, hptA⟩ := pair (i ρ) hρH
  obtain ⟨Lt, hLt⟩ := exists_lv (i := i) hg ok hW hdom hptA
  -- the sequence
  obtain ⟨SS, hSS⟩ := (SDef.ex (τ := ![6, 6, 9]) 6 (SDef.ex 6 (SDef.ex 6
    ((eOpD.comp ![3, 2, 1] 0).and ((eOpD.comp ![0, 2, 4] 0).and
      (SDef.all 6 ((eeD.comp ![0, 2] 0).iff
        (inLevD.comp ![6, 1, 0] 0)))))))).comprehensionU ![z₀, W]
  have hSS' : ∀ q, q ∈ SS ↔
      ∃ a w p, EOp q a w ∧ (EOp p a z₀ ∧ ∀ v, (EE v w ↔ InLev W p v)) := hSS
  obtain ⟨Sq, hSq⟩ := dom_sep E hdom (MH.prodS (MH.sc ρ) (℘ Lt)) SS
  have hop : ∀ ξ S : D, EOp (i (MH.kp ξ S)) (i ξ) (i S) := fun ξ S =>
    (emb_op_iff E _ ξ S).mp (MH.hin_isOp_iff.mpr rfl)
  have sq_intro : ∀ (ξ S : D) (p : V), ξ ∈ MH.sc ρ → (∀ z, z ∈ S → z ∈ Lt) →
      EOp p (i ξ) z₀ → IsLv i W p S → MH.Pr Sq ξ S := fun ξ S p hξ hsub hp hS =>
    MH.pr_iff.mpr ((hSq _).mpr ⟨MH.mem_prodS.mpr ⟨ξ, hξ, S, mem_power_iff.mpr hsub, rfl⟩,
      (hSS' _).mpr ⟨i ξ, i S, p, hop ξ S, hp, hS⟩⟩)
  have sq_elim : ∀ ξ S : D, MH.Pr Sq ξ S →
      ξ ∈ MH.sc ρ ∧ ∃ p, EOp p (i ξ) z₀ ∧ IsLv i W p S := by
    intro ξ S h
    obtain ⟨hX, hS⟩ := (hSq _).mp (MH.pr_iff.mp h)
    obtain ⟨ξ', hξ', S', -, e⟩ := MH.mem_prodS.mp hX
    obtain ⟨e1, -⟩ := MH.kp_inj e
    obtain ⟨a, w, p, hq, hp, hlv⟩ := (hSS' _).mp hS
    obtain ⟨e3, e4⟩ := eop_inj hq (hop ξ S)
    subst e3
    subst e4
    refine ⟨?_, p, hp, hlv⟩
    rw [e1]
    exact hξ'
  refine ⟨ρ, Sq, hρ, fun α hα => ?_, fun α S S' hS hS' => ?_, fun α S hα hS n hn => ?_,
    fun α β S S' hαβ hβ hS hS' => ?_⟩
  · obtain ⟨p, hp, hpA⟩ := pair (i α) (hsH α hα)
    obtain ⟨L, hL⟩ := exists_lv (i := i) hg ok hW hdom hpA
    refine ⟨L, sq_intro α L p hα ?_ hp hL⟩
    rcases MH.mem_sc.mp hα with e | e
    · rw [e] at hp
      rw [eop_unique hp hpt] at hL
      exact fun z hz => (E.mem z Lt).mpr ((hLt _).mpr ((hL _).mp ((E.mem z L).mp hz)))
    · exact lv_mono ok hW E hL hLt hptA (lexlt hp hpt (hsH α hα) hρH ((E.mem _ _).mp e))
  · obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    obtain ⟨-, p', hp', hlv'⟩ := sq_elim α S' hS'
    rw [eop_unique hp' hp] at hlv'
    exact mem_ext fun z => (E.mem z S).trans
      (((hlv (i z)).trans (hlv' (i z)).symm).trans (E.mem z S').symm)
  · obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    exact lv_om hW E hlv (inA (hsH α hα) hp) n hn
  · have hα : α ∈ MH.sc ρ := (MH.ord_sc hρO).1 β hβ α hαβ
    obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    obtain ⟨-, p', hp', hlv'⟩ := sq_elim β S' hS'
    have hp'A := inA (hsH β hβ) hp'
    have hlt : Rl R₂ p p' := lexlt hp hp' (hsH α hα) (hsH β hβ) ((E.mem _ _).mp hαβ)
    exact ⟨lv_mono ok hW E hlv hlv' hp'A hlt, lv_pow hW E hlv hlv' hp'A hlt⟩

/-- **With the Axiom of Counting, the members of the iterated power sets of `ω` of the
structure are fixed types.** -/
theorem pw_fixed (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i) {g : V}
    (hg : IsEg g) : ∀ (k : ℕ) (x : D), x ∈ (MH.pw k : D) → Fixed g (i x)
  | 0, x, hx => om_fixed hC hg ((emb_om_iff E _).mp ((E.mem _ _).mp hx))
  | k + 1, x, hx =>
    fixed_of_dmem E hg fun z hz => pw_fixed hC E hg k z (mem_power_iff.mp hx z hz)

/-- **With the Axiom of Counting, the rank axioms hold in the structure on the domain.** -/
theorem rank_in_dom (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (n : ℕ) : MH.HasRank n D := by
  obtain ⟨ρ, Sq, hρ, htot, hfn, hom, hmono⟩ :=
    exists_levels hC E hdom (MH.pw n : D) (fun g hg => pw_fixed hC E hg n)
  exact MH.hasRank_of_levels n hρ htot hfn hom hmono

end levels

end HinU

/-! ### The interpretation -/

/-- The rank axioms, for a structure on the types given with any structure for the
language. -/
theorem rank_of_struc {M : Type} [SetStructure M] [Nonempty M] [hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
    (hC : JensenNFU.Counting (fun a b : M => a ∈ b))
    {W : Type} [SetStructure W] [Nonempty W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛) {i : W → M} (E : HinU.Emb i)
    (hdom : ∀ x : M, Hin.Dom x ↔ ∃ w, i w = x) : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥 := by
  rcases standardStructure_unique W s
  exact models_mhr_of h fun n => HinU.rank_in_dom (hH := h) hC E hdom n

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖]

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the structure of the types in the domain is a model of `𝗠𝗛𝗥`.** -/
theorem macModelC_models_mhr : (macTranslationC.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥 := by
  obtain ⟨hU, hC⟩ := nfuic_models hTC
  have := hU
  have hi : Function.Injective (fun a : macTranslationC.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hdom : ∀ x : M, Hin.Dom x ↔ ∃ w : macTranslationC.Model M, (w : M) = x := fun x =>
    ⟨fun hx => ⟨⟨x, (macDomainU_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (macDomainU_val_iff _).mp w.dom⟩
  have hMH : (macTranslationC.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp macModelC_models φ (Or.inl hφ)
  have E := HinU.emb_of_dom _ hi hdom macModelC_mem_iff
  exact rank_of_struc hC hMH E hdom

end model

/-- **NFU + Infinity + the Axiom of Counting interprets `𝗠𝗛` with the rank axioms**, by the
translation `macTranslationC`: the domain is `Hin.Dom`, membership is `Hin.EE`. -/
instance nfuicInterpretsMHR : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗠𝗛𝗥 where
  trln := macTranslationC
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp macModelC_models_mhr φ hφ)

/-- **NF with the Axiom of Counting interprets `𝗠𝗛` with the rank axioms.** -/
instance nfcInterpretsMHR : 𝗡𝗙𝗖 ⊳ 𝗠𝗛𝗥 :=
  DirectInterpretation.comp nfuicInterpretsMHR nfcInterpretsNFUIC

/-- **NF with the Axiom of Counting and `𝗠𝗛` with the rank axioms are equiconsistent.** One
direction is the interpretation `nfcInterpretsMHR`; the other is
`consistent_nfc_of_consistent_mhr` (`MHRankSupply.lean`). -/
theorem consistent_nfc_iff_consistent_mhr :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗠𝗛𝗥 :=
  ⟨consistent_of_interprets nfcInterpretsMHR, consistent_nfc_of_consistent_mhr⟩

/-- **NFU + Infinity + the Axiom of Counting and `𝗠𝗛` with the rank axioms are
equiconsistent.** -/
theorem consistent_nfuic_iff_consistent_mhr :
    Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖 ↔ Entailment.Consistent 𝗠𝗛𝗥 :=
  ⟨consistent_of_interprets nfuicInterpretsMHR,
    fun h => consistent_of_interprets nfcInterpretsNFUIC (consistent_nfc_of_consistent_mhr h)⟩

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.HinU.rank_in_dom
#print axioms FFL.FirstOrder.SetTheory.nfuicInterpretsMHR
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsMHR
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_iff_consistent_mhr
#print axioms FFL.FirstOrder.SetTheory.consistent_nfuic_iff_consistent_mhr
