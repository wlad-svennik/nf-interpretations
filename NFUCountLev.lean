module

public import NFUNat

@[expose] public section

set_option autoImplicit false

/-!
# The levels `Pⁿ(Ω)` in a model of `𝗡𝗙𝗨𝗜` with the Axiom of Counting

Work in a model of Jensen's NFU + Infinity. `Ω` is the set of the finite ordinals among the
types of well-founded pointed graphs (`NFUBF.lean`), `E` is membership between types and `θ` is
the type-raising map. For a set `A` of types, `P(A)` is the set of the types all of whose
members are in `A`; it has the type of `A`.

* `IsW W`: `W` is the least set of pairs `⟨n, x⟩` such that `⟨0, x⟩ ∈ W` for `x ∈ Ω`, and
  `⟨n + 1, x⟩ ∈ W` when `n` is a natural number, `x` is a type and `⟨n, u⟩ ∈ W` for every member
  `u` of `x`. The natural numbers are Frege's (`NFUNat.lean`). `InLev W n x` says `⟨n, x⟩ ∈ W`,
  that is, `x ∈ Pⁿ(Ω)`.
* `lev_zero_iff`, `lev_succ_iff`: `P⁰(Ω) = Ω` and `Pⁿ⁺¹(Ω) = P(Pⁿ(Ω))`.
* `R6 n m`: `m` is `T⁶ n`, where `T n` is the natural number that contains the set of the
  singletons of the members of a member of `n`. With the Axiom of Counting, `R6 n n` (`r6_self`).
* **`lev_theta`**: for all natural numbers `n` and `m` with `R6 n m`, `θ` maps `Pⁿ(Ω)` onto
  `Pᵐ(Ω)`. This is a stratified statement, proved by induction on `n`; the induction step uses
  the Axiom of Counting, to know that `Pⁿ(Ω)` is mapped onto itself and hence that each of its
  subsets is the extension of a type.
* `lev_stable`: with the Axiom of Counting every `Pⁿ(Ω)` is stable.
* `lev_trans`, `lev_mono`, `lev_total`: the levels are transitive and form a chain.
* `InX x`: `x` belongs to some level. This is the domain of the interpretation of Zermelo set
  theory, and it is a set.
-/

namespace FFL.FirstOrder.SetTheory

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `y` is the set of the singletons of the members of `x`. -/
def SImg (y x : V) : Prop := ∀ s : V, s ∈ y ↔ ∃ a : V, a ∈ x ∧ ∀ z : V, z ∈ s ↔ z = a

/-- `m` contains the set of the singletons of the members of some member of `n`: `m = T n`. -/
def R1 (n m : V) : Prop := ∃ x y : V, x ∈ n ∧ SImg y x ∧ y ∈ m

/-- `m = T⁶ n`, through five natural numbers. -/
def R6 (n m : V) : Prop := ∃ m₁ m₂ m₃ m₄ m₅ : V, NatN m₁ ∧ NatN m₂ ∧ NatN m₃ ∧ NatN m₄ ∧ NatN m₅ ∧
  R1 n m₁ ∧ R1 m₁ m₂ ∧ R1 m₂ m₃ ∧ R1 m₃ m₄ ∧ R1 m₄ m₅ ∧ R1 m₅ m

/-- `⟨n, x⟩ ∈ W`. -/
def InLev (W n x : V) : Prop := ∃ p : V, IsOp p n x ∧ p ∈ W

/-- `C` is closed under the two rules that generate the levels. -/
def ClosedW (C : V) : Prop :=
  (∀ z x p : V, ZeroN z → InOm x → IsOp p z x → p ∈ C) ∧
  (∀ n n' x p : V, NatN n → SuccN n n' → InZ x → (∀ u : V, EE u x → InLev C n u) →
    IsOp p n' x → p ∈ C)

/-- `W` is the least set closed under the two rules. -/
def IsW (W : V) : Prop := ∀ p : V, p ∈ W ↔ ∀ C : V, ClosedW C → p ∈ C

/-- **The domain**: `x` belongs to some level. -/
def InX (x : V) : Prop := ∃ W n : V, IsW W ∧ NatN n ∧ InLev W n x

/-- The condition under which a pair is in `W`. -/
def GoodW (W k x : V) : Prop :=
  (ZeroN k ∧ InOm x) ∨ ∃ n : V, NatN n ∧ SuccN n k ∧ InZ x ∧ ∀ u : V, EE u x → InLev W n u

/-- `θ` maps the level `n` of `W₁` onto the level `m` of `W₂`. -/
def Phi (W₁ W₂ g n m : V) : Prop :=
  (∀ x : V, InLev W₁ n x → ∀ y : V, IsType y g x → InLev W₂ m y) ∧
  (∀ y : V, InLev W₂ m y → ∃ x : V, InLev W₁ n x ∧ IsType y g x)

/-- The statement proved by induction on `n`. -/
def QQ (n W₁ W₂ g : V) : Prop := ∀ m : V, NatN m → R6 n m → Phi W₁ W₂ g n m

end defs

section sdefs

def sImgD : SDef ![2, 1] (fun _ _ v ↦ SImg (v 0) (v 1)) :=
  (SDef.all 1 ((SDef.mem 0 1).iff (SDef.ex 0 ((SDef.mem 0 3).and
    (SDef.all 0 ((SDef.mem 0 2).iff (SDef.eq 0 1))))))).congr fun _ _ _ => Iff.rfl

def r1D : SDef ![2, 3] (fun _ _ v ↦ R1 (v 0) (v 1)) :=
  (SDef.ex 1 (SDef.ex 2 ((SDef.mem 1 2).and ((sImgD.comp ![0, 1] 0).and
    (SDef.mem 0 3))))).congr fun _ _ _ => Iff.rfl

def r6D : SDef ![2, 8] (fun _ _ v ↦ R6 (v 0) (v 1)) :=
  (SDef.ex 3 (SDef.ex 4 (SDef.ex 5 (SDef.ex 6 (SDef.ex 7
    ((natND.comp ![4] 1).and ((natND.comp ![3] 2).and ((natND.comp ![2] 3).and
      ((natND.comp ![1] 4).and ((natND.comp ![0] 5).and
        ((r1D.comp ![5, 4] 0).and ((r1D.comp ![4, 3] 1).and ((r1D.comp ![3, 2] 2).and
          ((r1D.comp ![2, 1] 3).and ((r1D.comp ![1, 0] 4).and
            (r1D.comp ![0, 6] 5)))))))))))))))).congr fun _ _ _ => Iff.rfl

def inLevD : SDef ![9, 6, 6] (fun _ _ v ↦ InLev (v 0) (v 1) (v 2)) :=
  (SDef.ex 8 ((isOpD.comp ![0, 2, 3] 6).and (SDef.mem 0 1))).congr fun _ _ _ => Iff.rfl

def closedWD : SDef ![9] (fun _ _ v ↦ ClosedW (v 0)) :=
  ((SDef.all 6 (SDef.all 6 (SDef.all 8 ((zeroND.comp ![2] 4).imp ((inOmD.comp ![1] 0).imp
      ((isOpD.comp ![0, 2, 1] 6).imp (SDef.mem 0 3))))))).and
    (SDef.all 6 (SDef.all 6 (SDef.all 6 (SDef.all 8 ((natND.comp ![3] 4).imp
      ((succND.comp ![3, 2] 4).imp ((inZD.comp ![1] 0).imp
        ((SDef.all 6 ((eeD.comp ![0, 2] 0).imp (inLevD.comp ![5, 4, 0] 0))).imp
          ((isOpD.comp ![0, 2, 1] 6).imp (SDef.mem 0 4))))))))))).congr fun _ _ _ => Iff.rfl

def isWD : SDef ![9] (fun _ _ v ↦ IsW (v 0)) :=
  (SDef.all 8 ((SDef.mem 0 1).iff
    (SDef.all 9 ((closedWD.comp ![0] 0).imp (SDef.mem 1 0))))).congr fun _ _ _ => Iff.rfl

def inXD : SDef ![6] (fun _ _ v ↦ InX (v 0)) :=
  (SDef.ex 9 (SDef.ex 6 ((isWD.comp ![1] 0).and ((natND.comp ![0] 4).and
    (inLevD.comp ![1, 0, 2] 0))))).congr fun _ _ _ => Iff.rfl

def goodWD : SDef ![9, 6, 6] (fun _ _ v ↦ GoodW (v 0) (v 1) (v 2)) :=
  (((zeroND.comp ![1] 4).and (inOmD.comp ![2] 0)).or
    (SDef.ex 6 ((natND.comp ![0] 4).and ((succND.comp ![0, 2] 4).and ((inZD.comp ![3] 0).and
      (SDef.all 6 ((eeD.comp ![0, 4] 0).imp (inLevD.comp ![2, 1, 0] 0)))))))).congr
    fun _ _ _ => Iff.rfl

def phiD : SDef ![9, 15, 9, 6, 12] (fun _ _ v ↦ Phi (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((SDef.all 6 ((inLevD.comp ![1, 4, 0] 0).imp (SDef.all 12
      ((isTypeD.comp ![0, 4, 1] 6).imp (inLevD.comp ![3, 6, 0] 6))))).and
    (SDef.all 12 ((inLevD.comp ![2, 5, 0] 6).imp (SDef.ex 6
      ((inLevD.comp ![2, 5, 0] 0).and (isTypeD.comp ![1, 4, 0] 6)))))).congr
    fun _ _ _ => Iff.rfl

def qqD : SDef ![6, 9, 15, 9] (fun _ _ v ↦ QQ (v 0) (v 1) (v 2) (v 3)) :=
  (SDef.all 12 ((natND.comp ![0] 10).imp ((r6D.comp ![1, 0] 4).imp
    (phiD.comp ![2, 3, 4, 1, 0] 0)))).congr fun _ _ _ => Iff.rfl

end sdefs

/-! ### The operation `T` and the Axiom of Counting -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

theorem exists_sImg (x : V) : ∃ y : V, SImg y x :=
  (SDef.ex (τ := ![1, 1]) 0 ((SDef.mem 0 2).and
    (SDef.all 0 ((SDef.mem 0 2).iff (SDef.eq 0 1))))).comprehensionU ![x]

/-- With the Axiom of Counting, `T n = n`. -/
theorem r1_self (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {n : V} (hn : NatN n) :
    R1 n n := by
  obtain ⟨x, hx⟩ := natN_nonempty hn
  obtain ⟨y, hy1, hy2⟩ := hC n hn x hx
  exact ⟨x, y, hx, hy2, hy1⟩

/-- `T 0 = 0`. -/
theorem r1_zero {z m : V} (hz : ZeroN z) (hm : NatN m) (h : R1 z m) : ZeroN m := by
  obtain ⟨x, y, hx, hy, hym⟩ := h
  have hx0 : ∀ w, ¬ w ∈ x := (hz x).mp hx
  refine zeroN_of_mem_empty hm (fun s hs => ?_) hym
  obtain ⟨a, ha, -⟩ := (hy s).mp hs
  exact hx0 a ha

/-- `T (n + 1) = T n + 1`: if `m' = T (n + 1)` then `m'` is the successor of some `m = T n`. -/
theorem r1_succ {n n' m' : V} (hs : SuccN n n') (hm' : NatN m') (h : R1 n' m') :
    ∃ m, NatN m ∧ SuccN m m' ∧ R1 n m := by
  obtain ⟨x', y', hx', hy', hym⟩ := h
  obtain ⟨x, hx, b, hb, hxx'⟩ := (hs x').mp hx'
  have hxx : ∀ w, w ∈ x' ↔ w ∈ x ∨ w = b := hxx'
  obtain ⟨y, hy⟩ := exists_sImg x
  obtain ⟨sb, hsb⟩ := exists_sing b
  have hsby' : sb ∈ y' := (hy' sb).mpr ⟨b, (hxx b).mpr (Or.inr rfl), hsb⟩
  rcases natN_cases hm' with hz | ⟨m, hmn, hsm⟩
  · exact absurd hsby' ((hz y').mp hym sb)
  · refine ⟨m, hmn, hsm, x, y, hx, hy, natN_rem hmn hsm hym hsby' fun s => ⟨fun hs' => ?_, ?_⟩⟩
    · obtain ⟨a, ha, hsa⟩ := (hy s).mp hs'
      refine ⟨(hy' s).mpr ⟨a, (hxx a).mpr (Or.inl ha), hsa⟩, fun e => hb ?_⟩
      have hab : a = b := sing_inj (e ▸ hsa : IsSing sb a) hsb
      exact hab ▸ ha
    · rintro ⟨hs', hne⟩
      obtain ⟨a, ha, hsa⟩ := (hy' s).mp hs'
      rcases (hxx a).mp ha with h | h
      · exact (hy s).mpr ⟨a, h, hsa⟩
      · exact absurd (sing_unique (h ▸ hsa : IsSing s b) hsb) hne

theorem r6_self (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {n : V} (hn : NatN n) :
    R6 n n :=
  ⟨n, n, n, n, n, hn, hn, hn, hn, hn, r1_self hC hn, r1_self hC hn, r1_self hC hn,
    r1_self hC hn, r1_self hC hn, r1_self hC hn⟩

theorem r6_zero {z m : V} (hz : ZeroN z) (hm : NatN m) (h : R6 z m) : ZeroN m := by
  obtain ⟨m₁, m₂, m₃, m₄, m₅, h1, h2, h3, h4, h5, r1, r2, r3, r4, r5, r6⟩ := h
  exact r1_zero (r1_zero (r1_zero (r1_zero (r1_zero (r1_zero hz h1 r1) h2 r2) h3 r3) h4 r4) h5 r5)
    hm r6

theorem r6_succ {n n' m' : V} (hs : SuccN n n') (hm' : NatN m') (h : R6 n' m') :
    ∃ m, NatN m ∧ SuccN m m' ∧ R6 n m := by
  obtain ⟨m₁', m₂', m₃', m₄', m₅', h1, h2, h3, h4, h5, r1, r2, r3, r4, r5, r6⟩ := h
  obtain ⟨m₁, k1, s1, q1⟩ := r1_succ hs h1 r1
  obtain ⟨m₂, k2, s2, q2⟩ := r1_succ s1 h2 r2
  obtain ⟨m₃, k3, s3, q3⟩ := r1_succ s2 h3 r3
  obtain ⟨m₄, k4, s4, q4⟩ := r1_succ s3 h4 r4
  obtain ⟨m₅, k5, s5, q5⟩ := r1_succ s4 h5 r5
  obtain ⟨m, k6, s6, q6⟩ := r1_succ s5 hm' r6
  exact ⟨m, k6, s6, m₁, m₂, m₃, m₄, m₅, k1, k2, k3, k4, k5, q1, q2, q3, q4, q5, q6⟩

/-! ### The least closed set -/

theorem exists_W : ∃ W : V, IsW W :=
  (SDef.all (τ := ![8]) 9 ((closedWD.comp ![0] 0).imp (SDef.mem 1 0))).comprehensionU
    (![] : Fin 0 → V)

omit [Nonempty V] hT in
theorem w_closed {W : V} (hW : IsW W) : ClosedW W := by
  refine ⟨fun z x p hz hx hp => (hW p).mpr fun C hC => hC.1 z x p hz hx hp,
    fun n n' x p hn hs hx hu hp => (hW p).mpr fun C hC => hC.2 n n' x p hn hs hx (fun u hux => ?_) hp⟩
  obtain ⟨q, hq, hqW⟩ := hu u hux
  exact ⟨q, hq, (hW q).mp hqW C hC⟩

theorem lev_zero {W z x : V} (hW : IsW W) (hz : ZeroN z) (hx : InOm x) : InLev W z x := by
  obtain ⟨p, hp⟩ := exists_op z x
  exact ⟨p, hp, (w_closed hW).1 z x p hz hx hp⟩

theorem lev_succ {W n n' x : V} (hW : IsW W) (hn : NatN n) (hs : SuccN n n') (hx : InZ x)
    (hu : ∀ u, EE u x → InLev W n u) : InLev W n' x := by
  obtain ⟨p, hp⟩ := exists_op n' x
  exact ⟨p, hp, (w_closed hW).2 n n' x p hn hs hx hu hp⟩

/-- **Inversion**: a pair in `W` got there by one of the two rules. -/
theorem lev_inv {W k x : V} (hW : IsW W) (h : InLev W k x) : GoodW W k x := by
  obtain ⟨W', hW'⟩ := ((SDef.mem (τ := ![8, 9]) 0 1).and (SDef.ex 6 (SDef.ex 6
    ((isOpD.comp ![2, 1, 0] 6).and (goodWD.comp ![3, 1, 0] 0))))).comprehensionU ![W]
  have hW'' : ∀ p, p ∈ W' ↔ p ∈ W ∧ ∃ k x, IsOp p k x ∧ GoodW W k x := hW'
  have hcl : ClosedW W' := by
    refine ⟨fun z x p hz hx hp => (hW'' p).mpr ⟨(w_closed hW).1 z x p hz hx hp, z, x, hp,
      Or.inl ⟨hz, hx⟩⟩, fun n n' x p hn hs hx hu hp => ?_⟩
    have hu' : ∀ u, EE u x → InLev W n u := fun u hux =>
      let ⟨q, hq, hqW⟩ := hu u hux; ⟨q, hq, ((hW'' q).mp hqW).1⟩
    exact (hW'' p).mpr ⟨(w_closed hW).2 n n' x p hn hs hx hu' hp, n', x, hp,
      Or.inr ⟨n, hn, hs, hx, hu'⟩⟩
  obtain ⟨p, hp, hpW⟩ := h
  obtain ⟨-, k₂, x₂, hp₂, hgood⟩ := (hW'' p).mp ((hW p).mp hpW W' hcl)
  obtain ⟨rfl, rfl⟩ := op_inj hp hp₂
  exact hgood

theorem lev_inZ {W k x : V} (hW : IsW W) (h : InLev W k x) : InZ x := by
  rcases lev_inv hW h with ⟨-, hx⟩ | ⟨n, -, -, hx, -⟩
  · exact om_inZ hx
  · exact hx

/-- `P⁰(Ω) = Ω`. -/
theorem lev_zero_iff {W z x : V} (hW : IsW W) (hz : ZeroN z) : InLev W z x ↔ InOm x := by
  refine ⟨fun h => ?_, lev_zero hW hz⟩
  rcases lev_inv hW h with ⟨-, hx⟩ | ⟨n, -, hs, -, -⟩
  · exact hx
  · exact (zero_not_succ hz hs).elim

/-- `Pⁿ⁺¹(Ω) = P(Pⁿ(Ω))`. -/
theorem lev_succ_iff {W n n' x : V} (hW : IsW W) (hn : NatN n) (hs : SuccN n n') :
    InLev W n' x ↔ InZ x ∧ ∀ u, EE u x → InLev W n u := by
  refine ⟨fun h => ?_, fun h => lev_succ hW hn hs h.1 h.2⟩
  rcases lev_inv hW h with ⟨hz, -⟩ | ⟨n₂, hn₂, hs₂, hx, hu⟩
  · exact (zero_not_succ hz hs).elim
  · obtain rfl := succN_inj hn₂ hn hs₂ hs
    exact ⟨hx, hu⟩

theorem exists_slice (W n : V) : ∃ L : V, ∀ x, x ∈ L ↔ InLev W n x :=
  (inLevD.comp (τ' := ![6, 9, 6]) ![1, 2, 0] 0).comprehensionU ![W, n]

/-! ### `θ` and the levels -/

/-- **`θ` maps `Pⁿ(Ω)` onto `Pᵐ(Ω)` whenever `m = T⁶ n`.** The statement is stratified. The
Axiom of Counting is used in the induction step. -/
theorem lev_theta (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {W g : V} (hW : IsW W)
    (hg : IsEg g) : ∀ n, NatN n → QQ n W W g := by
  refine natN_ind 4 qqD ![W, W, g] (fun z hz => ?_) (fun n hn ih n' hs => ?_)
  · show QQ z W W g
    intro m hm h6
    have hzm : ZeroN m := r6_zero hz hm h6
    obtain ⟨Ω, hΩ, hΩs, -⟩ := om_stable hg
    refine ⟨fun x hx y hy => ?_, fun y hy => ?_⟩
    · have hxo : InOm x := (lev_zero_iff hW hz).mp hx
      exact lev_zero hW hzm ((hΩ y).mp (hΩs.2.1 x ((hΩ x).mpr hxo) y hy))
    · have hyo : InOm y := (lev_zero_iff hW hzm).mp hy
      obtain ⟨x, hxΩ, hyx⟩ := hΩs.2.2 y ((hΩ y).mpr hyo)
      exact ⟨x, lev_zero hW hz ((hΩ x).mp hxΩ), hyx⟩
  · show QQ n' W W g
    have ih' : QQ n W W g := ih
    intro m' hm' h6'
    obtain ⟨m, hm, hsm, h6⟩ := r6_succ hs hm' h6'
    have hΦ : Phi W W g n m := ih' m hm h6
    have hΦn : Phi W W g n n := ih' n hn (r6_self hC hn)
    obtain ⟨L, hL⟩ := exists_slice W n
    have hLs : Stable g L := ⟨fun x hx => lev_inZ hW ((hL x).mp hx),
      fun x hx y hy => (hL y).mpr (hΦn.1 x ((hL x).mp hx) y hy),
      fun y hy => let ⟨x, hx, hyx⟩ := hΦn.2 y ((hL y).mp hy); ⟨x, (hL x).mpr hx, hyx⟩⟩
    refine ⟨fun x hx y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨-, hxu⟩ := (lev_succ_iff hW hn hs).mp hx
      refine lev_succ hW hm hsm (theta_inZ hg hy) fun v hv => ?_
      obtain ⟨u, hu, hvu⟩ := (theta_mem hg hy).mp hv
      exact hΦ.1 u (hxu u hu) v hvu
    · obtain ⟨hyZ, hyv⟩ := (lev_succ_iff hW hm hsm).mp hy
      obtain ⟨S, hS⟩ := ((SDef.mem (τ := ![6, 7, 9, 12]) 0 1).and (SDef.ex 12
        ((isTypeD.comp ![0, 3, 1] 6).and (eeD.comp ![0, 4] 6)))).comprehensionU ![L, g, y]
      have hS' : ∀ u, u ∈ S ↔ u ∈ L ∧ ∃ v, IsType v g u ∧ EE v y := hS
      obtain ⟨x, hxZ, hx⟩ := stable_full hg hLs S fun s hs => ((hS' s).mp hs).1
      have hxlev : InLev W n' x := lev_succ hW hn hs hxZ fun u hu =>
        (hL u).mp ((hS' u).mp ((hx u).mp hu)).1
      obtain ⟨y₀, hy₀⟩ := exists_type g x
      have e : y₀ = y := ee_ext (theta_inZ hg hy₀) hyZ fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · exact ⟨x, hxlev, e ▸ hy₀⟩
      · obtain ⟨u, hu, hvu⟩ := (theta_mem hg hy₀).mp hv
        obtain ⟨-, v', hv'u, hv'y⟩ := (hS' u).mp ((hx u).mp hu)
        rw [type_unique (wf_eg hg) hvu hv'u]
        exact hv'y
      · obtain ⟨u, hu, hvu⟩ := hΦ.2 v (hyv v hv)
        exact (theta_mem hg hy₀).mpr
          ⟨u, (hx u).mpr ((hS' u).mpr ⟨(hL u).mpr hu, v, hvu, hv⟩), hvu⟩

/-- **With the Axiom of Counting, every level is stable.** -/
theorem lev_stable (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {W g n L : V} (hW : IsW W)
    (hg : IsEg g) (hn : NatN n) (hL : ∀ x, x ∈ L ↔ InLev W n x) : Stable g L := by
  have hΦ : Phi W W g n n := lev_theta hC hW hg n hn n hn (r6_self hC hn)
  exact ⟨fun x hx => lev_inZ hW ((hL x).mp hx),
    fun x hx y hy => (hL y).mpr (hΦ.1 x ((hL x).mp hx) y hy),
    fun y hy => let ⟨x, hx, hyx⟩ := hΦ.2 y ((hL y).mp hy); ⟨x, (hL x).mpr hx, hyx⟩⟩

/-! ### The levels are transitive and form a chain -/

/-- Every level is transitive. -/
theorem lev_trans {W : V} (hW : IsW W) :
    ∀ n, NatN n → ∀ x u, InLev W n x → EE u x → InLev W n u := by
  refine natN_ind 4 (SDef.all (τ := ![6, 9]) 6 (SDef.all 6 ((inLevD.comp ![3, 2, 1] 0).imp
    ((eeD.comp ![0, 1] 0).imp (inLevD.comp ![3, 2, 0] 0))))) ![W] (fun z hz => ?_)
    (fun n hn ih n' hs => ?_)
  · show ∀ x u, InLev W z x → EE u x → InLev W z u
    intro x u hx hu
    exact lev_zero hW hz (om_trans ((lev_zero_iff hW hz).mp hx) hu)
  · show ∀ x u, InLev W n' x → EE u x → InLev W n' u
    have ih' : ∀ x u, InLev W n x → EE u x → InLev W n u := ih
    intro x u hx hu
    have hun : InLev W n u := ((lev_succ_iff hW hn hs).mp hx).2 u hu
    exact lev_succ hW hn hs (lev_inZ hW hun) fun w hw => ih' u w hun hw

/-- Every level is included in the next. -/
theorem lev_mono {W n n' x : V} (hW : IsW W) (hn : NatN n) (hs : SuccN n n')
    (h : InLev W n x) : InLev W n' x :=
  lev_succ hW hn hs (lev_inZ hW h) fun u hu => lev_trans hW n hn x u h hu

/-- The level `0` is included in every level. -/
theorem lev_zero_sub {W z : V} (hW : IsW W) (hz : ZeroN z) :
    ∀ m, NatN m → ∀ x, InLev W z x → InLev W m x := by
  refine natN_ind 4 (SDef.all (τ := ![6, 9, 6]) 6 ((inLevD.comp ![2, 3, 0] 0).imp
    (inLevD.comp ![2, 1, 0] 0))) ![W, z] (fun z₂ hz₂ => ?_) (fun m hm ih m' hs => ?_)
  · show ∀ x, InLev W z x → InLev W z₂ x
    exact fun x hx => lev_zero hW hz₂ ((lev_zero_iff hW hz).mp hx)
  · show ∀ x, InLev W z x → InLev W m' x
    have ih' : ∀ x, InLev W z x → InLev W m x := ih
    exact fun x hx => lev_mono hW hm hs (ih' x hx)

/-- **Any two levels are comparable.** -/
theorem lev_total {W : V} (hW : IsW W) : ∀ n, NatN n → ∀ m, NatN m →
    (∀ x, InLev W n x → InLev W m x) ∨ (∀ x, InLev W m x → InLev W n x) := by
  refine natN_ind 4 (SDef.all (τ := ![6, 9]) 6 ((natND.comp ![0] 4).imp
    ((SDef.all 6 ((inLevD.comp ![3, 2, 0] 0).imp (inLevD.comp ![3, 1, 0] 0))).or
      (SDef.all 6 ((inLevD.comp ![3, 1, 0] 0).imp (inLevD.comp ![3, 2, 0] 0)))))) ![W]
    (fun z hz => ?_) (fun n hn ih n' hs => ?_)
  · show ∀ m, NatN m → (∀ x, InLev W z x → InLev W m x) ∨ (∀ x, InLev W m x → InLev W z x)
    exact fun m hm => Or.inl (lev_zero_sub hW hz m hm)
  · show ∀ m, NatN m → (∀ x, InLev W n' x → InLev W m x) ∨ (∀ x, InLev W m x → InLev W n' x)
    have ih' : ∀ m, NatN m →
        (∀ x, InLev W n x → InLev W m x) ∨ (∀ x, InLev W m x → InLev W n x) := ih
    intro m hm
    rcases natN_cases hm with hz | ⟨k, hk, hsk⟩
    · exact Or.inr (lev_zero_sub hW hz n' (natN_succ hn hs))
    · rcases ih' k hk with h | h
      · refine Or.inl fun x hx => ?_
        obtain ⟨hxZ, hxu⟩ := (lev_succ_iff hW hn hs).mp hx
        exact lev_succ hW hk hsk hxZ fun u hu => h u (hxu u hu)
      · refine Or.inr fun x hx => ?_
        obtain ⟨hxZ, hxu⟩ := (lev_succ_iff hW hk hsk).mp hx
        exact lev_succ hW hn hs hxZ fun u hu => h u (hxu u hu)

omit [Nonempty V] hT in
/-- The domain in terms of a given `W`. -/
theorem inX_iff {W x : V} (hW : IsW W) : InX x ↔ ∃ n, NatN n ∧ InLev W n x := by
  refine ⟨fun ⟨W', n, hW', hn, p, hp, hpW'⟩ => ⟨n, hn, p, hp, (hW p).mpr ((hW' p).mp hpW')⟩,
    fun ⟨n, hn, h⟩ => ⟨W, n, hW, hn, h⟩⟩

end model

end HinU

end FFL.FirstOrder.SetTheory
