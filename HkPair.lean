module

public import MHArith

@[expose] public section

/-!
# A pairing function on the finite ordinals of a model of `𝗠𝗛`

For the Henkin construction of `HkTree.lean` the terms and the atomic sentences are finite
ordinals of the model, and they are built with one function of two arguments:
`pr a b = (a + b)² + a + 1`, where the operations are those of `MHArith.lean`.

* `PrR a b c`: the graph of the function, by a formula without parameters (`prRF`).
* `pr_mem_om`, `mem_pr_left`, `mem_pr_right`, `pr_inj`: the value is a finite ordinal, both
  arguments are members of it, and the function is one-to-one.
* `CanP P`: `P` is the set of the triples of the graph. `exists_canP`, `canP_unique`.
  `PG P a b c`: `P` relates `a`, `b` to `c`, by a bounded formula (`pgB`); `pg_iff`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `c = (a + b)² + a + 1`. -/
def PrR (a b c : V) : Prop :=
  ∃ s q r : V, AddR a b s ∧ (MulR s s q ∧ (AddR q a r ∧ SuccR c r))

/-- `P` relates `a`, `b` to `c`. -/
def PG (P a b c : V) : Prop :=
  ∃ t, t ∈ P ∧ ∃ u, u ∈ t ∧ ∃ w, w ∈ u ∧ (IsOp t w c ∧ IsOp w a b)

/-- `P` is the set of the triples of the pairing function. -/
def CanP (P : V) : Prop :=
  ∀ t : V, t ∈ P ↔ ∃ a b c w : V, NumR a ∧ (NumR b ∧ (PrR a b c ∧ (IsOp w a b ∧ IsOp t w c)))

/-- The condition that defines the set of the triples, with the graphs of addition and
multiplication as parameters. -/
def PGdef (z o SS GA GM : V) : Prop :=
  ∃ a, a ∈ o ∧ ∃ b, b ∈ o ∧ ∃ c, c ∈ o ∧ ∃ w, w ∈ SS ∧ ((IsOp w a b ∧ IsOp z w c) ∧
    ∃ s, s ∈ o ∧ ∃ q, q ∈ o ∧ ∃ r, r ∈ o ∧
      (Pt GA SS s a b ∧ (Pt GM SS q s s ∧ (Pt GA SS r q a ∧ SuccR c r))))

end defs

def prRF : FDef (k := 3) (fun V _ v ↦ PrR (v 0) (v 1) (v 2)) :=
  (FDef.ex (FDef.ex (FDef.ex ((addRF.comp ![3, 4, 2]).and ((mulRF.comp ![2, 2, 1]).and
    ((addRF.comp ![1, 3, 0]).and (succB.toFDef.comp ![5, 0]))))))).congr fun _ _ _ => Iff.rfl

def pgB : BDef (k := 4) (fun V _ v ↦ PG (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 0, 6]).and
    (isOpB.comp ![0, 4, 5]))))).congr fun _ _ _ => Iff.rfl

def canPF : FDef (k := 1) (fun V _ v ↦ CanP (v 0)) :=
  (FDef.all ((BDef.mem 0 1).toFDef.iff (FDef.ex (FDef.ex (FDef.ex (FDef.ex
    ((numB.toFDef.comp ![3]).and ((numB.toFDef.comp ![2]).and ((prRF.comp ![3, 2, 1]).and
      ((isOpB.toFDef.comp ![0, 3, 2]).and (isOpB.toFDef.comp ![4, 0, 1]))))))))))).congr
    fun _ _ _ => Iff.rfl

def pgdefB : BDef (k := 5) (fun V _ v ↦ PGdef (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 1 (BDef.bex 2 (BDef.bex 3 (BDef.bex 5
    (((isOpB.comp ![0, 3, 2]).and (isOpB.comp ![4, 0, 1])).and
      (BDef.bex 5 (BDef.bex 6 (BDef.bex 7 ((ptB.comp ![10, 9, 2, 6, 5]).and
        ((ptB.comp ![11, 9, 1, 2, 2]).and ((ptB.comp ![10, 9, 0, 1, 6]).and
          (succB.comp ![4, 0])))))))))))).congr fun _ _ _ => Iff.rfl

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem prR_host {κ₀ : V} (h₀ : Full κ₀) (x y : (levHost h₀).Nm) (c : V) :
    PrR (hval h₀ x.val) (hval h₀ y.val) c ↔
      c = hval h₀ ((x + y) * (x + y) + x + 1).val := by
  constructor
  · rintro ⟨s, q, r, hs, hq, hr, hc⟩
    rw [addR_iff h₀] at hs
    subst hs
    rw [mulR_iff h₀] at hq
    subst hq
    rw [addR_iff h₀] at hr
    subst hr
    rw [succR_iff_sc.mp hc, nv_succ]
  · rintro rfl
    exact ⟨_, _, _, (addR_iff h₀).mpr rfl, (mulR_iff h₀).mpr rfl, (addR_iff h₀).mpr rfl,
      succR_iff_sc.mpr (nv_succ h₀ _)⟩

theorem exists_prR {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    ∃ c, c ∈ (om : V) ∧ PrR a b c ∧ a ∈ c ∧ b ∈ c := by
  obtain ⟨κ₀, h₀, -⟩ := exists_full_above (ord_om (V := V))
  obtain ⟨x, rfl⟩ := nv_surj h₀ ha
  obtain ⟨y, rfl⟩ := nv_surj h₀ hb
  refine ⟨_, nv_om h₀ _, (prR_host h₀ x y _).mpr rfl, (nv_mem h₀).mpr ?_, (nv_mem h₀).mpr ?_⟩
  · exact (Host.Nm.le_iff _ _).mpr ⟨(x + y) * (x + y), by ring⟩
  · obtain ⟨d, hd⟩ := (Host.Nm.le_iff _ _).mp (Host.Nm.nfacts.le_mul_self (x + y))
    exact (Host.Nm.le_iff _ _).mpr ⟨x + d + x, by rw [← hd]; ring⟩

theorem prR_fn {a b c c' : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) (h : PrR a b c)
    (h' : PrR a b c') : c = c' := by
  obtain ⟨κ₀, h₀, -⟩ := exists_full_above (ord_om (V := V))
  obtain ⟨x, rfl⟩ := nv_surj h₀ ha
  obtain ⟨y, rfl⟩ := nv_surj h₀ hb
  rw [(prR_host h₀ x y _).mp h, (prR_host h₀ x y _).mp h']

theorem prR_inj {a b a' b' c : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V))
    (ha' : a' ∈ (om : V)) (hb' : b' ∈ (om : V)) (h : PrR a b c) (h' : PrR a' b' c) :
    a = a' ∧ b = b' := by
  obtain ⟨κ₀, h₀, -⟩ := exists_full_above (ord_om (V := V))
  obtain ⟨x, rfl⟩ := nv_surj h₀ ha
  obtain ⟨y, rfl⟩ := nv_surj h₀ hb
  obtain ⟨x', rfl⟩ := nv_surj h₀ ha'
  obtain ⟨y', rfl⟩ := nv_surj h₀ hb'
  have e := nv_inj h₀ (((prR_host h₀ x y _).mp h).symm.trans ((prR_host h₀ x' y' _).mp h'))
  have e' := Host.Nm.cancel _ _ _ e
  obtain ⟨e1, e2⟩ := Host.Nm.pair_inj x y x' y' e'
  exact ⟨by rw [e1], by rw [e2]⟩

/-- **The pairing function.** -/
noncomputable def pr (a b : V) : V := by
  classical exact if h : ∃ c : V, PrR a b c then Classical.choose h else ∅

theorem prR_iff {a b c : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    PrR a b c ↔ c = pr a b := by
  obtain ⟨c₀, -, hc₀, -, -⟩ := exists_prR ha hb
  have hex : ∃ c : V, PrR a b c := ⟨c₀, hc₀⟩
  have hpr : PrR a b (pr a b) := by
    unfold pr
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact ⟨fun h => prR_fn ha hb h hpr, fun h => h ▸ hpr⟩

theorem pr_mem_om {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) : pr a b ∈ (om : V) := by
  obtain ⟨c, hc, h, -, -⟩ := exists_prR ha hb
  exact (prR_iff ha hb).mp h ▸ hc

theorem mem_pr_left {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) : a ∈ pr a b := by
  obtain ⟨c, -, h, h1, -⟩ := exists_prR ha hb
  exact (prR_iff ha hb).mp h ▸ h1

theorem mem_pr_right {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) : b ∈ pr a b := by
  obtain ⟨c, -, h, -, h2⟩ := exists_prR ha hb
  exact (prR_iff ha hb).mp h ▸ h2

theorem pr_inj {a b a' b' : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V))
    (ha' : a' ∈ (om : V)) (hb' : b' ∈ (om : V)) (h : pr a b = pr a' b') : a = a' ∧ b = b' :=
  prR_inj ha hb ha' hb' ((prR_iff ha hb).mpr rfl) ((prR_iff ha' hb').mpr h)

theorem pr_ne_empty {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) : pr a b ≠ ∅ := by
  intro h
  have := mem_pr_left ha hb
  rw [h] at this
  exact absurd this (by simp)

/-! ### The set of the triples -/

theorem pg_iff_kp {P a b c : V} : PG P a b c ↔ kp (kp a b) c ∈ P := by
  constructor
  · rintro ⟨t, ht, u, -, w, -, h1, h2⟩
    rw [isOp_iff.mp h2] at h1
    rw [isOp_iff.mp h1] at ht
    exact ht
  · intro h
    obtain ⟨u, hu, hw⟩ := pr_fst_mem (isOp_kp (kp a b) c)
    exact ⟨_, h, u, hu, _, hw, isOp_kp _ _, isOp_kp _ _⟩

theorem canP_pg {P : V} (hP : CanP P) {a b c : V} :
    PG P a b c ↔ a ∈ (om : V) ∧ (b ∈ (om : V) ∧ c = pr a b) := by
  rw [pg_iff_kp, hP]
  constructor
  · rintro ⟨a', b', c', w, ha, hb, hpr, hw, ht⟩
    rw [isOp_iff.mp hw] at ht
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp ht)
    obtain ⟨e3, e4⟩ := kp_inj e1
    subst e2 e3 e4
    exact ⟨numR_iff.mp ha, numR_iff.mp hb, (prR_iff (numR_iff.mp ha) (numR_iff.mp hb)).mp hpr⟩
  · rintro ⟨ha, hb, rfl⟩
    exact ⟨a, b, _, kp a b, numR_iff.mpr ha, numR_iff.mpr hb, (prR_iff ha hb).mpr rfl,
      isOp_kp _ _, isOp_kp _ _⟩

theorem canP_unique {P P' : V} (h : CanP P) (h' : CanP P') : P = P' :=
  mem_ext fun t => (h t).trans (h' t).symm

theorem exists_canP : ∃ P : V, CanP P := by
  obtain ⟨κ₀, h₀, -⟩ := exists_full_above (ord_om (V := V))
  let SS : V := prodS (om : V) om
  let GA : V := hval h₀ (levHost h₀).addG
  let GM : V := hval h₀ (levHost h₀).mulG
  have hGA : AddG GA := addG_true h₀
  have hGM : MulG GM GA := mulG_true h₀
  have hadd : ∀ (x y : (levHost h₀).Nm) (c : V),
      Pt GA SS c (hval h₀ x.val) (hval h₀ y.val) ↔ AddR (hval h₀ x.val) (hval h₀ y.val) c :=
    fun x y c => (tr3_pt (nv_om h₀ x) (nv_om h₀ y)).symm.trans
      ((addG_iff h₀ hGA).trans (addR_iff h₀).symm)
  have hmul : ∀ (x y : (levHost h₀).Nm) (c : V),
      Pt GM SS c (hval h₀ x.val) (hval h₀ y.val) ↔ MulR (hval h₀ x.val) (hval h₀ y.val) c :=
    fun x y c => (tr3_pt (nv_om h₀ x) (nv_om h₀ y)).symm.trans
      (Iff.trans ⟨fun h => hGM.2.2 _ _ _ _ h (mulG_sub h₀ hGA hGM x y),
        fun h => h ▸ mulG_sub h₀ hGA hGM x y⟩ (mulR_iff h₀).symm)
  let P : V := sepB pgdefB (prodS SS (om : V)) ![(om : V), SS, GA, GM]
  have hPm : ∀ z, z ∈ P ↔ z ∈ prodS SS (om : V) ∧ PGdef z (om : V) SS GA GM :=
    fun z => mem_sepB pgdefB _ _ z
  refine ⟨P, fun t => (hPm t).trans ⟨?_, ?_⟩⟩
  · rintro ⟨-, a, ha, b, hb, c, -, w, -, ⟨hw, ht⟩, s, hs, q, hq, r, -, h1, h2, h3, h4⟩
    obtain ⟨x, rfl⟩ := nv_surj h₀ ha
    obtain ⟨y, rfl⟩ := nv_surj h₀ hb
    obtain ⟨s', rfl⟩ := nv_surj h₀ hs
    obtain ⟨q', rfl⟩ := nv_surj h₀ hq
    exact ⟨_, _, c, w, numR_iff.mpr (nv_om h₀ x), numR_iff.mpr (nv_om h₀ y),
      ⟨_, _, r, (hadd x y _).mp h1, (hmul s' s' _).mp h2, (hadd q' x _).mp h3, h4⟩, hw, ht⟩
  · rintro ⟨a, b, c, w, ha, hb, ⟨s, q, r, h1, h2, h3, h4⟩, hw, ht⟩
    have ha' := numR_iff.mp ha
    have hb' := numR_iff.mp hb
    obtain ⟨x, rfl⟩ := nv_surj h₀ ha'
    obtain ⟨y, rfl⟩ := nv_surj h₀ hb'
    have es := (addR_iff h₀).mp h1
    subst es
    have eq := (mulR_iff h₀).mp h2
    subst eq
    have er := (addR_iff h₀).mp h3
    subst er
    have ec : c = hval h₀ ((x + y) * (x + y) + x + 1).val := by
      rw [succR_iff_sc.mp h4, nv_succ]
    have hc : c ∈ (om : V) := ec ▸ nv_om h₀ _
    have hwS : w ∈ SS := mem_prodS.mpr ⟨_, ha', _, hb', isOp_iff.mp hw⟩
    refine ⟨mem_prodS.mpr ⟨w, hwS, c, hc, isOp_iff.mp ht⟩, _, ha', _, hb', c, hc, w, hwS,
      ⟨hw, ht⟩, _, nv_om h₀ _, _, nv_om h₀ _, _, nv_om h₀ _, (hadd x y _).mpr h1,
      (hmul _ _ _).mpr h2, (hadd _ x _).mpr h3, h4⟩

end model

end MH

end FFL.FirstOrder.SetTheory
