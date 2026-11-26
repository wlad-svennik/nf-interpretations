module

public import NFUCountLev

@[expose] public section

set_option autoImplicit false

/-!
# Types fixed by the type-raising map, in a model of `𝗡𝗙𝗨𝗜`

`Fixed g x` says `θ x = x`: the type `x` is the type of the graph `g` of membership between
types, pointed at `x`. The statement uses `x` at two types, so it is not stratified.

* `fixed_of_members`: a type all of whose members are fixed is fixed.
  `exists_type_of_fixed`: every set of fixed types is the extension of a fixed type.
* `fixed_of_nodes`: the type of a well-founded pointed graph whose point and whose nodes with
  an outgoing edge are fixed types is fixed. The relation `{⟨θ a, type of (r, a)⟩}` has a
  stratified definition, and when the nodes are fixed it is a bisimulation between `(r, t)` and
  `g` pointed at the type of `(r, t)`.
* **`om_fixed`**: with the Axiom of Counting, every finite ordinal is fixed. `IsC C` says that
  `C` is the least set of pairs `⟨n, a⟩`, `n` a natural number of Frege and `a` a finite
  ordinal, that contains `⟨0, 0⟩` and with `⟨n, a⟩` contains `⟨n + 1, a + 1⟩`. It is the graph of
  a function (`c_fun`) defined on all finite ordinals (`c_total`), and `θ` sends the ordinal at
  `n` to the ordinal at `T⁶ n` (`c_shift`, a stratified statement proved by induction).
-/

namespace FFL.FirstOrder.SetTheory

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `θ x = x`. -/
def Fixed (g x : V) : Prop := IsType x g x

/-- `C` is closed under the two rules that count the finite ordinals. -/
def ClosedC (C : V) : Prop :=
  (∀ z o p : V, ZeroN z → IsZero o → IsOp p z o → p ∈ C) ∧
  (∀ n n' a a' p : V, NatN n → SuccN n n' → InLev C n a → Succ a a' → IsOp p n' a' → p ∈ C)

/-- `C` is the least set closed under the two rules. -/
def IsC (C : V) : Prop := ∀ p : V, p ∈ C ↔ ∀ D : V, ClosedC D → p ∈ D

/-- The condition under which a pair is in `C`. -/
def GoodC (C k b : V) : Prop :=
  (ZeroN k ∧ IsZero b) ∨ ∃ n a : V, NatN n ∧ SuccN n k ∧ InLev C n a ∧ Succ a b

/-- `θ` sends the ordinal at `n` to the ordinal at `T⁶ n`. -/
def PsiC (n C₁ C₂ g : V) : Prop := ∀ m : V, NatN m → R6 n m →
  ∀ a : V, InLev C₁ n a → ∀ a' : V, IsType a' g a → InLev C₂ m a'

end defs

section sdefs

def closedCD : SDef ![9] (fun _ _ v ↦ ClosedC (v 0)) :=
  ((SDef.all 6 (SDef.all 6 (SDef.all 8 ((zeroND.comp ![2] 4).imp ((isZeroD.comp ![1] 0).imp
      ((isOpD.comp ![0, 2, 1] 6).imp (SDef.mem 0 3))))))).and
    (SDef.all 6 (SDef.all 6 (SDef.all 6 (SDef.all 6 (SDef.all 8 ((natND.comp ![4] 4).imp
      ((succND.comp ![4, 3] 4).imp ((inLevD.comp ![5, 4, 2] 0).imp ((succD.comp ![2, 1] 0).imp
        ((isOpD.comp ![0, 3, 1] 6).imp (SDef.mem 0 5)))))))))))).congr fun _ _ _ => Iff.rfl

def isCD : SDef ![9] (fun _ _ v ↦ IsC (v 0)) :=
  (SDef.all 8 ((SDef.mem 0 1).iff
    (SDef.all 9 ((closedCD.comp ![0] 0).imp (SDef.mem 1 0))))).congr fun _ _ _ => Iff.rfl

def goodCD : SDef ![9, 6, 6] (fun _ _ v ↦ GoodC (v 0) (v 1) (v 2)) :=
  (((zeroND.comp ![1] 4).and (isZeroD.comp ![2] 0)).or
    (SDef.ex 6 (SDef.ex 6 ((natND.comp ![1] 4).and ((succND.comp ![1, 3] 4).and
      ((inLevD.comp ![2, 1, 0] 0).and (succD.comp ![0, 4] 0))))))).congr fun _ _ _ => Iff.rfl

def psiCD : SDef ![6, 9, 15, 9] (fun _ _ v ↦ PsiC (v 0) (v 1) (v 2) (v 3)) :=
  (SDef.all 12 ((natND.comp ![0] 10).imp ((r6D.comp ![1, 0] 4).imp
    (SDef.all 6 ((inLevD.comp ![3, 2, 0] 0).imp (SDef.all 12
      ((isTypeD.comp ![0, 6, 1] 6).imp (inLevD.comp ![5, 2, 0] 6)))))))).congr
    fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-! ### Closure of the fixed types -/

/-- **A type all of whose members are fixed is fixed.** -/
theorem fixed_of_members {g w : V} (hg : IsEg g) (hw : InZ w) (h : ∀ u, EE u w → Fixed g u) :
    Fixed g w := by
  obtain ⟨y, hy⟩ := exists_type g w
  have e : y = w := ee_ext (theta_inZ hg hy) hw fun v => (theta_mem hg hy).trans
    ⟨fun ⟨u, hu, hvu⟩ => by rw [type_unique (wf_eg hg) hvu (h u hu)]; exact hu,
      fun hv => ⟨v, hv, h v hv⟩⟩
  rw [e] at hy
  exact hy

/-- **Every set of fixed types is the extension of a fixed type.** -/
theorem exists_type_of_fixed {g S : V} (hg : IsEg g) (hS : ∀ s, s ∈ S → Fixed g s) :
    ∃ w, InZ w ∧ Fixed g w ∧ ∀ v, EE v w ↔ v ∈ S := by
  obtain ⟨w, hwZ, hw⟩ := theta_sup hg S fun s hs => theta_inZ hg (hS s hs)
  have hw' : ∀ v, EE v w ↔ v ∈ S := fun v => (hw v).trans
    ⟨fun ⟨s, hs, hvs⟩ => by rw [type_unique (wf_eg hg) hvs (hS s hs)]; exact hs,
      fun hv => ⟨v, hv, hS v hv⟩⟩
  exact ⟨w, hwZ, fixed_of_members hg hwZ fun u hu => hS u ((hw' u).mp hu), hw'⟩

/-- **The type of a well-founded pointed graph on fixed nodes is fixed.** It is enough that the
point and the nodes with an outgoing edge are fixed types. -/
theorem fixed_of_nodes {g r t x : V} (hg : IsEg g) (hr : WF r) (hx : IsType x r t)
    (ht : Fixed g t) (hn : ∀ a b, Rl r a b → Fixed g a) : Fixed g x := by
  obtain ⟨B, hB⟩ := exists_rel 6 (SDef.ex (τ := ![6, 6, 3, 3, 0]) 0
    ((isTypeD.comp ![1, 3, 0] 0).and ((isTypeD.comp ![2, 4, 0] 0).and
      ((SDef.eq 0 5).or (SDef.ex 0 (rlD.comp ![5, 1, 0] 0)))))) ![g, r, t]
  have hB' : ∀ a' y, Rl B a' y ↔
      ∃ a, IsType a' g a ∧ IsType y r a ∧ (a = t ∨ ∃ b, Rl r a b) := hB
  have hfa : ∀ a, (a = t ∨ ∃ b, Rl r a b) → Fixed g a := by
    rintro a (rfl | ⟨b, hb⟩)
    · exact ht
    · exact hn a b hb
  have hin : ∀ a y, IsType y r a → (a = t ∨ ∃ b, Rl r a b) → Rl B a y := fun a y hy ha =>
    (hB' a y).mpr ⟨a, hfa a ha, hy, ha⟩
  have key : ∀ a' y, Rl B a' y → IsType y r a' := by
    intro a' y h
    obtain ⟨a, h1, h2, h3⟩ := (hB' a' y).mp h
    rw [type_unique (wf_eg hg) h1 (hfa a h3)]
    exact h2
  have hbis : IsBis B r g := by
    intro a y hay
    have hy : IsType y r a := key a y hay
    refine ⟨fun b hb => ?_, fun y' hy' => ?_⟩
    · obtain ⟨y', hy'⟩ := exists_type r b
      exact ⟨y', (rl_eg hg y' y).mpr ((ee_iff hr hy).mpr ⟨b, hb, hy'⟩),
        hin b y' hy' (Or.inr ⟨a, hb⟩)⟩
    · obtain ⟨b, hb, hyb⟩ := (ee_iff hr hy).mp ((rl_eg hg y' y).mp hy')
      exact ⟨b, hb, hin b y' hyb (Or.inr ⟨a, hb⟩)⟩
  exact isType_of_bis hx ⟨B, hbis, hin t x hx (Or.inl rfl)⟩

/-! ### Counting the finite ordinals -/

theorem exists_C : ∃ C : V, IsC C :=
  (SDef.all (τ := ![8]) 9 ((closedCD.comp ![0] 0).imp (SDef.mem 1 0))).comprehensionU
    (![] : Fin 0 → V)

omit [Nonempty V] hT in
theorem c_closed {C : V} (hC : IsC C) : ClosedC C := by
  refine ⟨fun z o p hz ho hp => (hC p).mpr fun D hD => hD.1 z o p hz ho hp,
    fun n n' a a' p hn hs ha hsa hp => (hC p).mpr fun D hD => hD.2 n n' a a' p hn hs ?_ hsa hp⟩
  obtain ⟨q, hq, hqC⟩ := ha
  exact ⟨q, hq, (hC q).mp hqC D hD⟩

theorem c_zero {C z o : V} (hC : IsC C) (hz : ZeroN z) (ho : IsZero o) : InLev C z o := by
  obtain ⟨p, hp⟩ := exists_op z o
  exact ⟨p, hp, (c_closed hC).1 z o p hz ho hp⟩

theorem c_succ {C n n' a a' : V} (hC : IsC C) (hn : NatN n) (hs : SuccN n n')
    (ha : InLev C n a) (hsa : Succ a a') : InLev C n' a' := by
  obtain ⟨p, hp⟩ := exists_op n' a'
  exact ⟨p, hp, (c_closed hC).2 n n' a a' p hn hs ha hsa hp⟩

theorem c_inv {C k b : V} (hC : IsC C) (h : InLev C k b) : GoodC C k b := by
  obtain ⟨C', hC'⟩ := ((SDef.mem (τ := ![8, 9]) 0 1).and (SDef.ex 6 (SDef.ex 6
    ((isOpD.comp ![2, 1, 0] 6).and (goodCD.comp ![3, 1, 0] 0))))).comprehensionU ![C]
  have hC'' : ∀ p, p ∈ C' ↔ p ∈ C ∧ ∃ k b, IsOp p k b ∧ GoodC C k b := hC'
  have hcl : ClosedC C' := by
    refine ⟨fun z o p hz ho hp => (hC'' p).mpr ⟨(c_closed hC).1 z o p hz ho hp, z, o, hp,
      Or.inl ⟨hz, ho⟩⟩, fun n n' a a' p hn hs ha hsa hp => ?_⟩
    have ha' : InLev C n a := let ⟨q, hq, hqC⟩ := ha; ⟨q, hq, ((hC'' q).mp hqC).1⟩
    exact (hC'' p).mpr ⟨(c_closed hC).2 n n' a a' p hn hs ha' hsa hp, n', a', hp,
      Or.inr ⟨n, a, hn, hs, ha', hsa⟩⟩
  obtain ⟨p, hp, hpC⟩ := h
  obtain ⟨-, k₂, b₂, hp₂, hgood⟩ := (hC'' p).mp ((hC p).mp hpC C' hcl)
  obtain ⟨rfl, rfl⟩ := op_inj hp hp₂
  exact hgood

/-- `C` is the graph of a function. -/
theorem c_fun {C : V} (hC : IsC C) :
    ∀ n, NatN n → ∀ a b, InLev C n a → InLev C n b → a = b := by
  refine natN_ind 4 (SDef.all (τ := ![6, 9]) 6 (SDef.all 6 ((inLevD.comp ![3, 2, 1] 0).imp
    ((inLevD.comp ![3, 2, 0] 0).imp (SDef.eq 1 0))))) ![C] (fun z hz => ?_)
    (fun n hn ih n' hs => ?_)
  · show ∀ a b, InLev C z a → InLev C z b → a = b
    intro a b ha hb
    rcases c_inv hC ha with ⟨-, ha0⟩ | ⟨n, _, -, hs, -, -⟩
    · rcases c_inv hC hb with ⟨-, hb0⟩ | ⟨n, _, -, hs, -, -⟩
      · exact zero_unique ha0 hb0
      · exact (zero_not_succ hz hs).elim
    · exact (zero_not_succ hz hs).elim
  · show ∀ a b, InLev C n' a → InLev C n' b → a = b
    have ih' : ∀ a b, InLev C n a → InLev C n b → a = b := ih
    intro a' b' ha' hb'
    rcases c_inv hC ha' with ⟨hz, -⟩ | ⟨n₁, a, hn₁, hs₁, ha, hsa⟩
    · exact (zero_not_succ hz hs).elim
    · rcases c_inv hC hb' with ⟨hz, -⟩ | ⟨n₂, b, hn₂, hs₂, hb, hsb⟩
      · exact (zero_not_succ hz hs).elim
      · obtain rfl := succN_inj hn₁ hn hs₁ hs
        obtain rfl := succN_inj hn₂ hn₁ hs₂ hs
        obtain rfl := ih' a b ha hb
        exact succ_unique hsa hsb

/-- `C` is defined on every finite ordinal. -/
theorem c_total {C : V} (hC : IsC C) : ∀ a, InOm a → ∃ n, NatN n ∧ InLev C n a := by
  refine om_ind 0 (SDef.ex (τ := ![6, 9]) 6 ((natND.comp ![0] 4).and
    (inLevD.comp ![2, 0, 1] 0))) ![C] (fun o ho => ?_) (fun y _ ih w hw => ?_)
  · show ∃ n, NatN n ∧ InLev C n o
    obtain ⟨z, hz⟩ := exists_zeroN (V := V)
    exact ⟨z, natN_zero hz, c_zero hC hz ho⟩
  · show ∃ n, NatN n ∧ InLev C n w
    have ih' : ∃ n, NatN n ∧ InLev C n y := ih
    obtain ⟨n, hn, h⟩ := ih'
    obtain ⟨n', hs⟩ := exists_succN n
    exact ⟨n', natN_succ hn hs, c_succ hC hn hs h hw⟩

/-- **`θ` sends the finite ordinal at `n` to the finite ordinal at `T⁶ n`.** -/
theorem c_shift {C g : V} (hC : IsC C) (hg : IsEg g) : ∀ n, NatN n → PsiC n C C g := by
  refine natN_ind 4 psiCD ![C, C, g] (fun z hz => ?_) (fun n hn ih n' hs => ?_)
  · show PsiC z C C g
    intro m hm h6 a ha a' ha'
    rcases c_inv hC ha with ⟨-, ha0⟩ | ⟨n, _, -, hs, -, -⟩
    · exact c_zero hC (r6_zero hz hm h6) (zero_theta hg ha0 ha')
    · exact (zero_not_succ hz hs).elim
  · show PsiC n' C C g
    have ih' : PsiC n C C g := ih
    intro m' hm' h6' b hb b' hb'
    obtain ⟨m, hm, hsm, h6⟩ := r6_succ hs hm' h6'
    rcases c_inv hC hb with ⟨hz, -⟩ | ⟨n₁, a, hn₁, hs₁, ha, hsa⟩
    · exact (zero_not_succ hz hs).elim
    · obtain rfl := succN_inj hn₁ hn hs₁ hs
      obtain ⟨a', ha'⟩ := exists_type g a
      exact c_succ hC hm hsm (ih' m hm h6 a ha a' ha') (succ_theta hg ha' hb' hsa)

/-- **With the Axiom of Counting, every finite ordinal is fixed by `θ`.** -/
theorem om_fixed (hCt : JensenNFU.Counting (fun a b : V => a ∈ b)) {g a : V} (hg : IsEg g)
    (ha : InOm a) : Fixed g a := by
  obtain ⟨C, hC⟩ := exists_C (V := V)
  obtain ⟨n, hn, hna⟩ := c_total hC a ha
  obtain ⟨a', ha'⟩ := exists_type g a
  have h := c_shift hC hg n hn n hn (r6_self hCt hn) a hna a' ha'
  have e : a = a' := c_fun hC n hn a a' hna h
  rw [← e] at ha'
  exact ha'

end model

end HinU

end FFL.FirstOrder.SetTheory
