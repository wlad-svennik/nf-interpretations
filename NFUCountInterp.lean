module

public import NFUInternal
public import MHArith
public import CutTrans
public import FnCount

@[expose] public section

set_option autoImplicit false

/-!
# NFU + Infinity + the Axiom of Counting interprets NF + the Axiom of Counting

In a model of `𝗡𝗙𝗨𝗜𝗖` the types in `Hin.Dom` are a model `D` of `𝗠𝗛` (`NFUCountMH.lean`). The
numbers of `D` with the sets of `D` and the cut `CutK` are a structure in the sense of
`CutTerm.lean` (`cutSys`): soundness on the cut is `HinU.sound_K`. So the least terms of the cut
of the terms, with the interpreted membership, are a model of NF and of the Axiom of Counting
(`CutSys.dm_isNF`, `CutSys.dm_counting`).

The domain and the membership of that model are given by formulas of the two-sorted language
(`minTmX`, `epsX2` of `CutFml.lean`), and these are translated into `ℒₛₑₜ` over the model of
`𝗡𝗙𝗨𝗜𝗖` (`CutTrans.lean`) with the following formulas for the atoms:

* the domain is `Hin.Dom` and membership is `Hin.EE`;
* "is a number", the graphs of `+` and `×` and the numerals are the formulas of `MHArith.lean`
  about `D`, translated by `macTranslationC`;
* the cut is `CutK`: the cut `InJ0` (a formula that is not stratified, `inJ0U`), shortened.

Results: `nfcTranslation`, `nfcModel_models`, and

**`nfuicInterpretsNFC : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula NFUCut

/-- A formula that defines a relation in every structure defines it in a structure given with
any structure for the language. -/
theorem FDef.eval_struc {k : ℕ} {R : MRel k} (d : FDef R) {W : Type} [SetStructure W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (e : Fin k → W) : W ⊧/e d.φ ↔ R W e := by
  rcases standardStructure_unique W s
  exact d.eval W e

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD Dom)

/-! ### The formulas -/

/-- **The cut `InJ0`, by a formula.** It is not stratified. -/
def inJ0U : UDef (k := 1) (fun _ _ v ↦ InJ0 (v 0)) :=
  (((UDef.ofS inOmD).comp (m := 1) ![0]).and
    (UDef.all (UDef.all (UDef.all (UDef.all (UDef.all
      (((UDef.ofS isEgD).comp (m := 6) ![4]).imp (((UDef.ofS (isBD 0)).comp (m := 6) ![3]).imp
        ((UDef.all ((UDef.mem (k := 7) 0 3).iff ((UDef.ofS inHD).comp (m := 7) ![4, 0]))).imp
          (((UDef.ofS isRHD).comp (m := 6) ![2, 1]).imp
            (((UDef.ofS isWGD).comp (m := 6) ![2, 1, 0]).imp
              (UDef.all (((UDef.ofS inLevD).comp (m := 7) ![1, 6, 0]).imp
                ((UDef.ofS isTypeD).comp (m := 7) ![0, 5, 0])))))))))))))).congr
    fun _ _ _ => Iff.rfl

/-- The translation of a formula about the structure on the domain. -/
def trC {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : Semisentence ℒₛₑₜ k := macTranslationC.translate φ

/-- The formulas for the atoms, with the cut `InJ0`. -/
def ops₁ : Ops where
  dom := Hin.domU.φ
  num := trC MH.numB.φ
  cut := inJ0U.φ
  add := trC MH.addRF.φ
  mul := trC MH.mulRF.φ
  mem := Hin.eeD.φ
  numl := fun k => trC (MH.isNumB k).φ

def k1B (m : BTm) : BFml :=
  .all 140 (BFml.imp (.inKt (.var 140)) (.inKt (.add (.var 140) m)))

/-- "The number `0` is in the shortening of the cut", as a formula of `L₂`. -/
def cutKB : BFml := .all 141 (BFml.imp (k1B (.var 141)) (k1B (.mul (.var 141) (.var 0))))

/-- The cut `CutK`, by a formula. -/
def cutS : Semisentence ℒₛₑₜ 1 := trM ops₁ cutKB 1 (fun _ => #0) (fun _ => #0)

/-- The formulas for the atoms, with the cut `CutK`. -/
def ops₂ : Ops := { ops₁ with cut := cutS }

/-- **The domain of the interpretation**: the least terms. -/
def nfcDomF : Semisentence ℒₛₑₜ 1 :=
  (ops₁.dom ⋏ ops₁.num) ⋏ trM ops₂ minTmX 1 (fun _ => #0) (fun _ => #0)

/-- **The membership of the interpretation.** -/
def nfcMemF : Semisentence ℒₛₑₜ 2 :=
  trM ops₂ epsX2 2 (fun j => if j = 1 then #1 else #0) (fun _ => #0)

theorem bholdsR_cutKB {N W : Type} [CommSemiring N] [PartialOrder N] [IsOrderedRing N]
    [CanonicallyOrderedAdd N] (mem : N → W → Prop) (cut : N → Prop) (e : ℕ → N) (s : ℕ → W) :
    bholdsR mem cut cutKB e s ↔ Shortening.K cut (fun n : N => n) (e 0) := by
  simp [cutKB, k1B, bholdsR, bholdsR_imp, evalG, Function.update_apply, Shortening.K,
    Shortening.K₁, Shortening.C₂]

/-! ### The structure of numbers and sets -/

section sem

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] [Nonempty D] [hH : D↓[ℒₛₑₜ] ⊧* 𝗠𝗛] {i : D → V}

/-- **The numbers and the sets of the structure on the domain, with the cut `CutK`.** -/
noncomputable def cutSys (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) {κ₀ : D} (h₀ : MH.Full κ₀) :
    CutSys (MH.levHost h₀).Nm D where
  mem a s := MH.hval h₀ a.val ∈ s
  cut := CutK i h₀
  cut_zero := Shortening.K_zero
  cut_one := Shortening.K_one
  cut_add := fun ha hb => Shortening.K_add ha hb
  cut_down := fun hab hb => Shortening.K_down (cutJ_hyp hC E h₀) hab hb
  eq_or_succ_le := fun {a b} h => Host.Nm.eq_or_succ_le a b h
  not_succ_le := Host.Nm.not_succ_le
  le_of_succ_le_succ := fun h => (Host.Nm.nfacts (H := MH.levHost h₀)).le_of_succ_le_succ h
  le_total := Host.Nm.total
  emp := ∅
  adj s k := s ∪ {MH.hval h₀ k.val}
  mem_adj := fun {s k j} => by
    rw [mem_union_iff, mem_singleton_iff]
    exact or_congr Iff.rfl ⟨fun h => MH.nv_inj h₀ h, fun h => by rw [h]⟩
  rem s k := MH.sepB (k := 1) (BDef.eq 0 1).not s ![MH.hval h₀ k.val]
  mem_rem := fun {s k j} =>
    (MH.mem_sepB _ _ _ _).trans (and_congr Iff.rfl
      (not_congr ⟨fun h => MH.nv_inj h₀ h, fun h => by subst h; rfl⟩))
  agree_ind := MH.nm_agree_ind h₀
  least := MH.nm_least h₀
  sound := fun q hq => sound_K hC E hdom h₀ q hq

/-! ### The meaning of the formulas -/

/-- The relativisation property of `trC`, as a hypothesis: it holds for the structure on the
domain of a model of `𝗡𝗙𝗨𝗜𝗖`. -/
def IsTr (i : D → V) : Prop :=
  ∀ {k : ℕ} {R : MRel k} (d : FDef R) (e : Fin k → D),
    V ⊧/(fun j => i (e j)) (trC d.φ) ↔ R D e

omit [Nonempty V] hT [Nonempty D] hH in
theorem tr1 (htr : IsTr i) {R : MRel 1} (d : FDef R) (w : D) :
    V ⊧/![i w] (trC d.φ) ↔ R D ![w] := by
  have e : (fun j => i ((![w] : Fin 1 → D) j)) = ![i w] := by
    funext j
    fin_cases j
    rfl
  rw [← e]
  exact htr d ![w]

omit [Nonempty V] hT [Nonempty D] hH in
theorem tr3 (htr : IsTr i) {R : MRel 3} (d : FDef R) (a b c : D) :
    V ⊧/![i a, i b, i c] (trC d.φ) ↔ R D ![a, b, c] := by
  have e : (fun j => i ((![a, b, c] : Fin 3 → D) j)) = ![i a, i b, i c] := by
    funext j
    fin_cases j <;> rfl
  rw [← e]
  exact htr d ![a, b, c]

/-- The formulas for the atoms mean what they should. -/
theorem spec₁ (E : Emb i) (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) {κ₀ : D}
    (h₀ : MH.Full κ₀) :
    Spec ops₁ (fun (a : (MH.levHost h₀).Nm) (s : D) => MH.hval h₀ a.val ∈ s)
      (fun a => i (MH.hval h₀ a.val)) i where
  inj := fun a b h => MH.nv_inj h₀ (E.inj h)
  num := fun x => by
    constructor
    · rintro ⟨hd, hn⟩
      obtain ⟨w, rfl⟩ := (hdom x).mp ((Hin.domU.eval V ![x]).mp hd)
      have h2 : MH.NumR w := (tr1 htr MH.numB.toFDef w).mp hn
      obtain ⟨a, ha⟩ := MH.nv_surj h₀ (MH.numR_iff.mp h2)
      exact ⟨a, by rw [ha]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(Hin.domU.eval V ![_]).mpr ((hdom _).mpr ⟨_, rfl⟩),
        (tr1 htr MH.numB.toFDef _).mpr (MH.numR_iff.mpr (MH.nv_om h₀ a))⟩
  set := fun x => (Hin.domU.eval V ![x]).trans ((hdom x).trans
    ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩)
  mem := fun a w => (Hin.eeD.eval V ![_, _]).trans (E.mem _ _).symm
  le := fun a b => by
    rw [Host.Nm.le_def]
    exact or_congr ((Hin.eeD.eval V ![_, _]).trans (E.mem _ _).symm)
      ⟨fun h => Subtype.ext (E.inj h), fun h => by rw [h]⟩
  numl := fun k x => by
    constructor
    · rintro ⟨hd, hn⟩
      obtain ⟨w, rfl⟩ := (hdom x).mp ((Hin.domU.eval V ![x]).mp hd)
      have h2 : MH.IsNum k w := (tr1 htr (MH.isNumB k).toFDef w).mp hn
      rw [(MH.isNum_nv_iff h₀ k w).mp h2]
    · rintro rfl
      exact ⟨(Hin.domU.eval V ![_]).mpr ((hdom _).mpr ⟨_, rfl⟩),
        (tr1 htr (MH.isNumB k).toFDef _).mpr ((MH.isNum_nv_iff h₀ k _).mpr rfl)⟩
  add := fun p q z => by
    constructor
    · rintro ⟨hd, hn⟩
      obtain ⟨w, rfl⟩ := (hdom z).mp ((Hin.domU.eval V ![z]).mp hd)
      have h2 : MH.AddR (MH.hval h₀ p.val) (MH.hval h₀ q.val) w := (tr3 htr MH.addRF _ _ w).mp hn
      rw [(MH.addR_iff h₀).mp h2]
    · rintro rfl
      exact ⟨(Hin.domU.eval V ![_]).mpr ((hdom _).mpr ⟨_, rfl⟩),
        (tr3 htr MH.addRF _ _ _).mpr ((MH.addR_iff h₀).mpr rfl)⟩
  mul := fun p q z => by
    constructor
    · rintro ⟨hd, hn⟩
      obtain ⟨w, rfl⟩ := (hdom z).mp ((Hin.domU.eval V ![z]).mp hd)
      have h2 : MH.MulR (MH.hval h₀ p.val) (MH.hval h₀ q.val) w := (tr3 htr MH.mulRF _ _ w).mp hn
      rw [(MH.mulR_iff h₀).mp h2]
    · rintro rfl
      exact ⟨(Hin.domU.eval V ![_]).mpr ((hdom _).mpr ⟨_, rfl⟩),
        (tr3 htr MH.mulRF _ _ _).mpr ((MH.mulR_iff h₀).mpr rfl)⟩

/-- The formula `cutS` defines the cut `CutK`. -/
theorem eval_cutS (E : Emb i) (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) {κ₀ : D}
    (h₀ : MH.Full κ₀) (a : (MH.levHost h₀).Nm) :
    V ⊧/![i (MH.hval h₀ a.val)] cutS ↔ CutK i h₀ a := by
  have h := eval_trM (spec₁ E hdom htr h₀) (cut := CutJ i h₀) (fun b => inJ0U.eval V ![_])
    cutKB 1 (fun _ => #0) (fun _ => #0) ![i (MH.hval h₀ a.val)] (fun _ => a)
    (fun _ => MH.hval h₀ a.val) (fun _ => rfl) (fun _ => rfl)
  exact h.trans (bholdsR_cutKB _ _ _ _)

theorem spec₂ (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) {κ₀ : D} (h₀ : MH.Full κ₀) :
    Spec ops₂ (cutSys hC E hdom h₀).mem (fun a => i (MH.hval h₀ a.val)) i :=
  let s := spec₁ E hdom htr h₀
  ⟨s.inj, s.num, s.set, s.mem, s.le, s.numl, s.add, s.mul⟩

/-- **The formula for the domain defines the least terms.** -/
theorem eval_nfcDomF (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) {κ₀ : D} (h₀ : MH.Full κ₀) (x : V) :
    V ⊧/![x] nfcDomF ↔ ∃ a : (MH.levHost h₀).Nm,
      x = i (MH.hval h₀ a.val) ∧ (cutSys hC E hdom h₀).MinTm a := by
  have key : ∀ a : (MH.levHost h₀).Nm,
      V ⊧/![i (MH.hval h₀ a.val)] (trM ops₂ minTmX 1 (fun _ => #0) (fun _ => #0)) ↔
        (cutSys hC E hdom h₀).MinTm a := fun a =>
    (eval_trM (spec₂ hC E hdom htr h₀) (cut := (cutSys hC E hdom h₀).cut)
      (fun b => eval_cutS E hdom htr h₀ b) minTmX 1 (fun _ => #0) (fun _ => #0)
      ![i (MH.hval h₀ a.val)] (fun _ => a) (fun _ => MH.hval h₀ a.val) (fun _ => rfl)
      (fun _ => rfl)).trans
      ((((cutSys hC E hdom h₀).bholds_iff_bholdsR minTmX _ _).symm).trans
        ((cutSys hC E hdom h₀).bholds_minTmX _ _))
  have h0 : V ⊧/![x] nfcDomF ↔ (V ⊧/![x] ops₁.dom ∧ V ⊧/![x] ops₁.num) ∧
      V ⊧/![x] (trM ops₂ minTmX 1 (fun _ => #0) (fun _ => #0)) := by
    unfold nfcDomF
    simp
  rw [h0, (spec₁ E hdom htr h₀).num x]
  constructor
  · rintro ⟨⟨a, rfl⟩, h⟩
    exact ⟨a, rfl, (key a).mp h⟩
  · rintro ⟨a, rfl, h⟩
    exact ⟨⟨a, rfl⟩, (key a).mpr h⟩

/-- **The formula for membership defines the interpreted membership.** -/
theorem eval_nfcMemF (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) {κ₀ : D} (h₀ : MH.Full κ₀)
    (a b : (MH.levHost h₀).Nm) :
    V ⊧/![i (MH.hval h₀ a.val), i (MH.hval h₀ b.val)] nfcMemF ↔
      (cutSys hC E hdom h₀).Eps a b := by
  have h := eval_trM (spec₂ hC E hdom htr h₀) (cut := (cutSys hC E hdom h₀).cut)
    (fun b => eval_cutS E hdom htr h₀ b) epsX2 2 (fun j => if j = 1 then #1 else #0)
    (fun _ => #0) ![i (MH.hval h₀ a.val), i (MH.hval h₀ b.val)]
    (fun j => if j = 1 then b else a) (fun _ => MH.hval h₀ a.val)
    (fun j => by
      by_cases hj : j = 1
      · subst hj
        rfl
      · simp only [if_neg hj]
        rfl)
    (fun _ => rfl)
  exact h.trans ((((cutSys hC E hdom h₀).bholds_iff_bholdsR epsX2 _ _).symm).trans
    ((cutSys hC E hdom h₀).bholds_epsX2 _ _))

/-- **The model of NF with the Axiom of Counting, and the formulas that define it.** -/
theorem interp_sem (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (htr : IsTr i) :
    ∃ (A : Type) (memA : A → A → Prop) (f : A → V), Nonempty A ∧ ConNF.NF.IsNF A memA ∧
      JensenNFU.Counting memA ∧ Function.Injective f ∧
      (∀ x : V, V ⊧/![x] nfcDomF ↔ ∃ a, f a = x) ∧
      ∀ a b : A, V ⊧/![f a, f b] nfcMemF ↔ memA a b := by
  obtain ⟨κ₀, h₀, -⟩ := MH.exists_full_above (V := D) MH.ord_empty
  refine ⟨(cutSys hC E hdom h₀).Dm, fun a b => (cutSys hC E hdom h₀).Eps a.1 b.1,
    fun a => i (MH.hval h₀ a.1.val), (cutSys hC E hdom h₀).dm_nonempty,
    (cutSys hC E hdom h₀).dm_isNF, (cutSys hC E hdom h₀).dm_counting,
    fun a b h => Subtype.ext (MH.nv_inj h₀ (E.inj h)), fun x => ?_,
    fun a b => eval_nfcMemF hC E hdom htr h₀ a.1 b.1⟩
  rw [eval_nfcDomF hC E hdom htr h₀]
  exact ⟨fun ⟨a, hx, hm⟩ => ⟨⟨a, hm⟩, hx.symm⟩, fun ⟨a, hx⟩ => ⟨a.1, hx.symm, a.2⟩⟩

end sem

end HinU

/-- `HinU.interp_sem`, for a structure on the types given with any structure for the
language. -/
theorem interp_of_struc {M : Type} [SetStructure M] [Nonempty M] [hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
    (hC : JensenNFU.Counting (fun a b : M => a ∈ b))
    {W : Type} [SetStructure W] [Nonempty W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛) {i : W → M} (E : HinU.Emb i)
    (hdom : ∀ x : M, Hin.Dom x ↔ ∃ w, i w = x)
    (htr : ∀ {k : ℕ} (φ : Semisentence ℒₛₑₜ k) (e : Fin k → W),
      M ⊧/(fun j => i (e j)) (HinU.trC φ) ↔ W ⊧/e φ) :
    ∃ (A : Type) (memA : A → A → Prop) (f : A → M), Nonempty A ∧ ConNF.NF.IsNF A memA ∧
      JensenNFU.Counting memA ∧ Function.Injective f ∧
      (∀ x : M, M ⊧/![x] HinU.nfcDomF ↔ ∃ a, f a = x) ∧
      ∀ a b : A, M ⊧/![f a, f b] HinU.nfcMemF ↔ memA a b := by
  rcases standardStructure_unique W s
  exact HinU.interp_sem (hH := h) hC E hdom (fun d e => (htr d.φ e).trans (d.eval W e))

/-! ### The translation -/

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖]

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the formulas `nfcDomF` and `nfcMemF` define a model of NF with the
Axiom of Counting.** -/
theorem nfc_sem :
    ∃ (A : Type) (memA : A → A → Prop) (f : A → M), Nonempty A ∧ ConNF.NF.IsNF A memA ∧
      JensenNFU.Counting memA ∧ Function.Injective f ∧
      (∀ x : M, M ⊧/![x] HinU.nfcDomF ↔ ∃ a, f a = x) ∧
      ∀ a b : A, M ⊧/![f a, f b] HinU.nfcMemF ↔ memA a b := by
  obtain ⟨hUI, hC⟩ := nfuic_models hTC
  have := hUI
  have hi : Function.Injective (fun a : macTranslationC.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hdom : ∀ x : M, Hin.Dom x ↔ ∃ w : macTranslationC.Model M, (w : M) = x := fun x =>
    ⟨fun hx => ⟨⟨x, (macDomainU_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (macDomainU_val_iff _).mp w.dom⟩
  have hMH : (macTranslationC.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp macModelC_models φ (Or.inl hφ)
  have E := HinU.emb_of_dom _ hi hdom macModelC_mem_iff
  exact interp_of_struc hC hMH E hdom
    (fun φ e => DirectTranslation.Model.evalb_translate_iff)

end model

/-- The interpretation of the relation symbols: equality is itself, and membership is the
interpreted membership of the least terms. -/
def nfcRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => ⟨HinU.nfcMemF⟩

/-- **The translation of `ℒₛₑₜ` into `𝗡𝗙𝗨𝗜𝗖`** whose domain is the least terms of the cut of the
terms. Equality is equality. -/
def nfcTranslation : DirectTranslation 𝗡𝗙𝗨𝗜𝗖 ℒₛₑₜ where
  domain := ⟨HinU.nfcDomF⟩
  rel := nfcRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    obtain ⟨A, memA, f, ⟨a⟩, -, -, -, hd, -⟩ := nfc_sem (M := M)
    suffices ∃ x : M, (⟨HinU.nfcDomF⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨f a, (hd _).mpr ⟨a, rfl⟩⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : nfcRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTC : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖]

/-- The membership relation of the interpreted structure. -/
instance nfcModel_setStructure : SetStructure (nfcTranslation.Model M) :=
  ⟨fun y x ↦ M ⊧/![(x : M), (y : M)] HinU.nfcMemF⟩

omit [Nonempty M] hTC in
lemma nfcModel_mem_iff (a b : nfcTranslation.Model M) :
    a ∈ b ↔ M ⊧/![(a : M), (b : M)] HinU.nfcMemF := Iff.rfl

lemma nfcModel_rel_iff (a b : nfcTranslation.Model M) :
    Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] ↔ a ∈ b := by
  rw [DirectTranslation.Model.rel_iff]
  have h2 : (fun i ↦ ((![a, b] i : nfcTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  rw [h2]
  exact Iff.rfl

instance nfcModel_mem : Tarski.Structure.Mem ℒₛₑₜ (nfcTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1]
    exact nfcModel_rel_iff a b

/-- **In a model of `𝗡𝗙𝗨𝗜𝗖`, the interpreted structure is a model of `𝗡𝗙𝗖`.** -/
theorem nfcModel_models : (nfcTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗖 := by
  obtain ⟨A, memA, f, hne, hnf, hcount, hinj, hd, hm⟩ := nfc_sem (M := M)
  have hx : ∀ x : nfcTranslation.Model M, ∃ a, f a = (x : M) := fun x => (hd _).mp x.dom
  choose g hg using hx
  have hbij : Function.Bijective g := by
    refine ⟨fun x y h => ?_, fun a => ⟨⟨f a, (hd _).mpr ⟨a, rfl⟩⟩, hinj (hg _)⟩⟩
    have e : (x : M) = (y : M) := by rw [← hg x, ← hg y, h]
    cases x
    cases y
    cases e
    rfl
  have hmem : ∀ x y : nfcTranslation.Model M, x ∈ y ↔ memA (g x) (g y) := fun x y => by
    rw [← hm, hg, hg]
    exact Iff.rfl
  have hc' : JensenNFU.Counting (fun a b : nfcTranslation.Model M => a ∈ b) :=
    JensenNFU.Counting.of_bijective g hbij hmem hcount
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp (models_nf_of_isNF (ConNF.NF.IsNF.of_bijective g hbij
      (fun x y => (nfcModel_rel_iff x y).trans (hmem x y)) hnf)) φ hφ
  · rw [show φ = Axiom.counting from hφ]
    exact FNF.models_counting' hc'

end model

/-- **NFU + Infinity + the Axiom of Counting interprets NF + the Axiom of Counting.** The
domain is a definable set of natural numbers of the model of `𝗠𝗛` on the types: the least codes
of the closed terms, in a cut on which the axioms N and the clauses for the Axiom of Counting
have truth assignments. Equality is interpreted by equality. -/
instance nfuicInterpretsNFC : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖 where
  trln := nfcTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp nfcModel_models φ hφ)

/-- **`𝗡𝗙𝗨𝗜𝗖` and `𝗡𝗙𝗖` are mutually interpretable.** -/
instance nfuicNFCMutual : 𝗡𝗙𝗨𝗜𝗖 ⋈ 𝗡𝗙𝗖 where
  r := nfuicInterpretsNFC
  l := nfcInterpretsNFUIC

/-- **The syntactic transformation.** The translation of a theorem of `𝗡𝗙𝗖` is a theorem of
`𝗡𝗙𝗨𝗜𝗖`. -/
theorem nfuic_provable_translate_of_nfc {σ : Sentence ℒₛₑₜ} (h : 𝗡𝗙𝗖 ⊢ σ) :
    𝗡𝗙𝗨𝗜𝗖 ⊢ nfuicInterpretsNFC σ :=
  DirectInterpretation.sound nfuicInterpretsNFC h

end FFL.FirstOrder.SetTheory
