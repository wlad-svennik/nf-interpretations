module

public import NFUFix
public import NFUCountZ

@[expose] public section

set_option autoImplicit false

/-!
# Levels along a well-founded relation on fixed types, in a model of `𝗡𝗙𝗨𝗜`

`NFUCountLev.lean` builds the levels `Pⁿ(Ω)` along Frege's natural numbers. Here the index set
is any set `A` of types fixed by the type-raising map `θ`, with a set relation `R` that is
well-founded, transitive and directed on `A`, and without a last element (`IdxOK g A R`).

* `IsWG A R W`: `W` is the least set of pairs `⟨a, x⟩`, `a ∈ A` and `x` a type, such that
  `⟨a, x⟩ ∈ W` when `x` is a finite ordinal or every member of `x` is in an earlier level:
  `⟨b, u⟩ ∈ W` for some `b` with `b R a`. So the level of `a` is `V_{ω + ρ(a) + 1}` among the
  types, `ρ(a)` the rank of `a` in `R`. `levG_iff` is the defining equation.
* **`levG_theta`**: for every `a ∈ A`, `θ` maps the level of `a` onto itself. The statement
  "`θ` maps the level of `a` onto the level of `θ a`" is stratified; it is proved by taking an
  `R`-minimal counterexample, and `θ a = a` because the members of `A` are fixed.
* `base_of_levelsG`: the types that belong to some level satisfy the conditions of `IsMacBase`
  and separation for all formulas, so they form a model of `𝗭` (`models_z_of_base`).

This is the general form of Proposition 17.5 of the draft *Choice and Consistency Strength in NF
and NFU* (v15): a model of Zermelo set theory of height `ω + δ` for a limit `δ` of fixed
ordinals.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `C` is closed under the rule that generates the levels along `R` on `A`. -/
def ClosedG (A R C : V) : Prop :=
  ∀ a x p : V, a ∈ A → InZ x →
    (InOm x ∨ ∀ u : V, EE u x → ∃ b : V, Rl R b a ∧ InLev C b u) → IsOp p a x → p ∈ C

/-- `W` is the least set closed under the rule. -/
def IsWG (A R W : V) : Prop := ∀ p : V, p ∈ W ↔ ∀ C : V, ClosedG A R C → p ∈ C

/-- The condition under which a pair is in `W`. -/
def GoodG (A R W a x : V) : Prop :=
  a ∈ A ∧ InZ x ∧ (InOm x ∨ ∀ u : V, EE u x → ∃ b : V, Rl R b a ∧ InLev W b u)

/-- `θ` maps the level of `a` in `W₁` onto the level of `θ a` in `W₂`. -/
def QG (a W₁ W₂ g : V) : Prop := ∀ a' : V, IsType a' g a → Phi W₁ W₂ g a a'

/-- `x` belongs to some level. -/
def InXG (A W x : V) : Prop := ∃ a : V, a ∈ A ∧ InLev W a x

/-- **The conditions on the index set.** -/
structure IdxOK (g A R : V) : Prop where
  /-- The members of `A` are fixed types. -/
  fixed : ∀ a : V, a ∈ A → Fixed g a
  /-- `R` is well-founded. -/
  wf : WF R
  /-- `R` is transitive. -/
  trans : ∀ a b c : V, Rl R a b → Rl R b c → Rl R a c
  /-- `R` is directed on `A`. -/
  dir : ∀ a b : V, a ∈ A → b ∈ A → ∃ c : V, c ∈ A ∧ (a = c ∨ Rl R a c) ∧ (b = c ∨ Rl R b c)
  /-- `A` has no last element. -/
  next : ∀ a : V, a ∈ A → ∃ c : V, c ∈ A ∧ Rl R a c
  /-- `A` has a member. -/
  nonempty : ∃ a : V, a ∈ A

end defs

section sdefs

def closedGD : SDef ![7, 9, 9] (fun _ _ v ↦ ClosedG (v 0) (v 1) (v 2)) :=
  (SDef.all 6 (SDef.all 6 (SDef.all 8 ((SDef.mem 2 3).imp ((inZD.comp ![1] 0).imp
    (((inOmD.comp ![1] 0).or (SDef.all 6 ((eeD.comp ![0, 2] 0).imp (SDef.ex 6
        ((rlD.comp ![6, 0, 4] 6).and (inLevD.comp ![7, 0, 1] 0)))))).imp
      ((isOpD.comp ![0, 2, 1] 6).imp (SDef.mem 0 5)))))))).congr fun _ _ _ => Iff.rfl

def isWGD : SDef ![7, 9, 9] (fun _ _ v ↦ IsWG (v 0) (v 1) (v 2)) :=
  (SDef.all 8 ((SDef.mem 0 3).iff (SDef.all 9 ((closedGD.comp ![2, 3, 0] 0).imp
    (SDef.mem 1 0))))).congr fun _ _ _ => Iff.rfl

def goodGD : SDef ![7, 9, 9, 6, 6] (fun _ _ v ↦ GoodG (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((SDef.mem 3 0).and ((inZD.comp ![4] 0).and ((inOmD.comp ![4] 0).or
    (SDef.all 6 ((eeD.comp ![0, 5] 0).imp (SDef.ex 6
      ((rlD.comp ![3, 0, 5] 6).and (inLevD.comp ![4, 0, 1] 0)))))))).congr fun _ _ _ => Iff.rfl

def qgD : SDef ![6, 9, 15, 9] (fun _ _ v ↦ QG (v 0) (v 1) (v 2) (v 3)) :=
  (SDef.all 12 ((isTypeD.comp ![0, 4, 1] 6).imp (phiD.comp ![2, 3, 4, 1, 0] 0))).congr
    fun _ _ _ => Iff.rfl

def inXGD : SDef ![7, 9, 6] (fun _ _ v ↦ InXG (v 0) (v 1) (v 2)) :=
  (SDef.ex 6 ((SDef.mem 0 1).and (inLevD.comp ![2, 0, 3] 0))).congr fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

theorem exists_WG (A R : V) : ∃ W : V, IsWG A R W :=
  (SDef.all (τ := ![8, 7, 9]) 9 ((closedGD.comp ![2, 3, 0] 0).imp
    (SDef.mem 1 0))).comprehensionU ![A, R]

omit [Nonempty V] hT in
theorem wg_closed {A R W : V} (hW : IsWG A R W) : ClosedG A R W := by
  intro a x p ha hx h hp
  refine (hW p).mpr fun C hC => hC a x p ha hx (h.imp id fun hu u hux => ?_) hp
  obtain ⟨b, hb, q, hq, hqW⟩ := hu u hux
  exact ⟨b, hb, q, hq, (hW q).mp hqW C hC⟩

theorem levG_intro {A R W a x : V} (hW : IsWG A R W) (ha : a ∈ A) (hx : InZ x)
    (h : InOm x ∨ ∀ u, EE u x → ∃ b, Rl R b a ∧ InLev W b u) : InLev W a x := by
  obtain ⟨p, hp⟩ := exists_op a x
  exact ⟨p, hp, wg_closed hW a x p ha hx h hp⟩

/-- **Inversion.** -/
theorem levG_inv {A R W a x : V} (hW : IsWG A R W) (h : InLev W a x) : GoodG A R W a x := by
  obtain ⟨W', hW'⟩ := ((SDef.mem (τ := ![8, 9, 7, 9]) 0 1).and (SDef.ex 6 (SDef.ex 6
    ((isOpD.comp ![2, 1, 0] 6).and (goodGD.comp ![4, 5, 3, 1, 0] 0))))).comprehensionU ![W, A, R]
  have hW'' : ∀ p, p ∈ W' ↔ p ∈ W ∧ ∃ a x, IsOp p a x ∧ GoodG A R W a x := hW'
  have hcl : ClosedG A R W' := by
    intro a x p ha hx h hp
    have h' : InOm x ∨ ∀ u, EE u x → ∃ b, Rl R b a ∧ InLev W b u := h.imp id fun hu u hux =>
      let ⟨b, hb, q, hq, hqW⟩ := hu u hux; ⟨b, hb, q, hq, ((hW'' q).mp hqW).1⟩
    exact (hW'' p).mpr ⟨wg_closed hW a x p ha hx h' hp, a, x, hp, ha, hx, h'⟩
  obtain ⟨p, hp, hpW⟩ := h
  obtain ⟨-, a₂, x₂, hp₂, hgood⟩ := (hW'' p).mp ((hW p).mp hpW W' hcl)
  obtain ⟨rfl, rfl⟩ := op_inj hp hp₂
  exact hgood

/-- **The levels**: `x` is in the level of `a` if and only if `a ∈ A`, `x` is a type, and `x` is
a finite ordinal or every member of `x` is in the level of some `b` with `b R a`. -/
theorem levG_iff {A R W a x : V} (hW : IsWG A R W) :
    InLev W a x ↔ a ∈ A ∧ InZ x ∧ (InOm x ∨ ∀ u, EE u x → ∃ b, Rl R b a ∧ InLev W b u) :=
  ⟨levG_inv hW, fun ⟨ha, hx, h⟩ => levG_intro hW ha hx h⟩

theorem levG_mono {A R W a c x : V} (hW : IsWG A R W)
    (htr : ∀ a b c : V, Rl R a b → Rl R b c → Rl R a c) (hc : c ∈ A) (hac : Rl R a c)
    (h : InLev W a x) : InLev W c x := by
  obtain ⟨-, hx, h'⟩ := levG_inv hW h
  exact levG_intro hW hc hx (h'.imp id fun hu u hux =>
    let ⟨b, hb, hbu⟩ := hu u hux; ⟨b, htr b a c hb hac, hbu⟩)

theorem levG_trans {A R W a x u : V} (hW : IsWG A R W)
    (htr : ∀ a b c : V, Rl R a b → Rl R b c → Rl R a c) (h : InLev W a x) (hu : EE u x) :
    InLev W a u := by
  obtain ⟨ha, -, h'⟩ := levG_inv hW h
  rcases h' with hxo | hxu
  · exact levG_intro hW ha (om_inZ (om_trans hxo hu)) (Or.inl (om_trans hxo hu))
  · obtain ⟨b, hb, hbu⟩ := hxu u hu
    exact levG_mono hW htr ha hb hbu

/-- **`θ` maps every level onto itself.** -/
theorem levG_theta {g A R W : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W) :
    ∀ a, a ∈ A → QG a W W g := by
  obtain ⟨Bad, hBad⟩ := ((SDef.mem (τ := ![6, 7, 9, 15, 9]) 0 1).and
    (qgD.comp ![0, 2, 3, 4] 0).not).comprehensionU ![A, W, W, g]
  have hBad' : ∀ a, a ∈ Bad ↔ a ∈ A ∧ ¬ QG a W W g := hBad
  by_contra hcon
  have hne : ∃ a, a ∈ Bad := by
    by_contra h
    exact hcon fun a ha => by
      by_contra hq
      exact h ⟨a, (hBad' a).mpr ⟨ha, hq⟩⟩
  obtain ⟨c, hcBad, hmin⟩ := ok.wf Bad hne
  obtain ⟨hc, hnc⟩ := (hBad' c).mp hcBad
  have ih : ∀ b, b ∈ A → Rl R b c → QG b W W g := fun b hb hbc => by
    by_contra hq
    exact hmin b ((hBad' b).mpr ⟨hb, hq⟩) hbc
  apply hnc
  intro c' hc'
  rw [type_unique (wf_eg hg) hc' (ok.fixed c hc)]
  -- the union of the earlier levels
  obtain ⟨L, hL⟩ := (SDef.ex (τ := ![6, 9, 6, 9]) 6 ((rlD.comp ![2, 0, 3] 6).and
    (inLevD.comp ![4, 0, 1] 0))).comprehensionU ![R, c, W]
  have hL' : ∀ u, u ∈ L ↔ ∃ b, Rl R b c ∧ InLev W b u := hL
  have hQb : ∀ b, Rl R b c → ∀ u, InLev W b u → Phi W W g b b := fun b hb u hbu => by
    have hbA : b ∈ A := (levG_inv hW hbu).1
    exact ih b hbA hb b (ok.fixed b hbA)
  have hLs : Stable g L := by
    refine ⟨fun u hu => ?_, fun u hu v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨b, -, hbu⟩ := (hL' u).mp hu
      exact (levG_inv hW hbu).2.1
    · obtain ⟨b, hb, hbu⟩ := (hL' u).mp hu
      exact (hL' v).mpr ⟨b, hb, (hQb b hb u hbu).1 u hbu v hv⟩
    · obtain ⟨b, hb, hbv⟩ := (hL' v).mp hv
      obtain ⟨u, hbu, hvu⟩ := (hQb b hb v hbv).2 v hbv
      exact ⟨u, (hL' u).mpr ⟨b, hb, hbu⟩, hvu⟩
  obtain ⟨Ω, hΩ, hΩs, -⟩ := om_stable hg
  refine ⟨fun x hx y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨-, -, h'⟩ := levG_inv hW hx
    refine levG_intro hW hc (theta_inZ hg hy) ?_
    rcases h' with hxo | hxu
    · exact Or.inl ((hΩ y).mp (hΩs.2.1 x ((hΩ x).mpr hxo) y hy))
    · refine Or.inr fun v hv => ?_
      obtain ⟨u, hu, hvu⟩ := (theta_mem hg hy).mp hv
      obtain ⟨b, hb, hbu⟩ := hxu u hu
      exact ⟨b, hb, (hQb b hb u hbu).1 u hbu v hvu⟩
  · obtain ⟨-, hyZ, h'⟩ := levG_inv hW hy
    rcases h' with hyo | hyv
    · obtain ⟨x, hxΩ, hyx⟩ := hΩs.2.2 y ((hΩ y).mpr hyo)
      exact ⟨x, levG_intro hW hc (om_inZ ((hΩ x).mp hxΩ)) (Or.inl ((hΩ x).mp hxΩ)), hyx⟩
    · obtain ⟨S, hS⟩ := ((SDef.mem (τ := ![6, 7, 9, 12]) 0 1).and (SDef.ex 12
        ((isTypeD.comp ![0, 3, 1] 6).and (eeD.comp ![0, 4] 6)))).comprehensionU ![L, g, y]
      have hS' : ∀ u, u ∈ S ↔ u ∈ L ∧ ∃ v, IsType v g u ∧ EE v y := hS
      obtain ⟨x, hxZ, hx⟩ := stable_full hg hLs S fun s hs => ((hS' s).mp hs).1
      have hxlev : InLev W c x := levG_intro hW hc hxZ (Or.inr fun u hu =>
        (hL' u).mp ((hS' u).mp ((hx u).mp hu)).1)
      obtain ⟨y₀, hy₀⟩ := exists_type g x
      have e : y₀ = y := ee_ext (theta_inZ hg hy₀) hyZ fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · exact ⟨x, hxlev, e ▸ hy₀⟩
      · obtain ⟨u, hu, hvu⟩ := (theta_mem hg hy₀).mp hv
        obtain ⟨-, v', hv'u, hv'y⟩ := (hS' u).mp ((hx u).mp hu)
        rw [type_unique (wf_eg hg) hvu hv'u]
        exact hv'y
      · obtain ⟨b, hb, hbv⟩ := hyv v hv
        obtain ⟨u, hbu, hvu⟩ := (hQb b hb v hbv).2 v hbv
        exact (theta_mem hg hy₀).mpr
          ⟨u, (hx u).mpr ((hS' u).mpr ⟨(hL' u).mpr ⟨b, hb, hbu⟩, v, hvu, hv⟩), hvu⟩

/-- **Every level is stable.** -/
theorem levG_stable {g A R W a L : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W)
    (ha : a ∈ A) (hL : ∀ x, x ∈ L ↔ InLev W a x) : Stable g L := by
  have hΦ : Phi W W g a a := levG_theta hg ok hW a ha a (ok.fixed a ha)
  exact ⟨fun x hx => (levG_inv hW ((hL x).mp hx)).2.1,
    fun x hx y hy => (hL y).mpr (hΦ.1 x ((hL x).mp hx) y hy),
    fun y hy => let ⟨x, hx, hyx⟩ := hΦ.2 y ((hL y).mp hy); ⟨x, (hL x).mpr hx, hyx⟩⟩

/-- **The types that belong to some level satisfy the conditions for a model of `𝗭`.** -/
theorem base_of_levelsG {g A R W : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W)
    {D : Type} [SetStructure D] (i : D → V) (hi : Function.Injective i)
    (hdom : ∀ x : V, InXG A W x ↔ ∃ w, i w = x) (hmem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b)) :
    IsMacBase D ∧ ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → D) (t : D),
      ∃ y : D, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := D) ![z] ε ψ := by
  obtain ⟨X, hX⟩ := (inXGD.comp (τ' := ![6, 7, 9]) ![1, 2, 0] 0).comprehensionU ![A, W]
  have hX' : ∀ v, v ∈ X ↔ ∃ w, i w = v := fun v => (hX v).trans (hdom v)
  have hlev : ∀ w, ∃ a, a ∈ A ∧ InLev W a (i w) := fun w => (hdom _).mpr ⟨w, rfl⟩
  have hZ : ∀ w, InZ (i w) := fun w => let ⟨_, _, h⟩ := hlev w; (levG_inv hW h).2.1
  have hdown : ∀ w v, EE v (i w) → ∃ w', i w' = v := fun w v hv => by
    obtain ⟨a, ha, h⟩ := hlev w
    exact (hdom v).mp ⟨a, ha, levG_trans hW ok.trans h hv⟩
  let Lev : V → Prop := fun L => ∃ a, a ∈ A ∧ ∀ x, x ∈ L ↔ InLev W a x
  have lev_mem : ∀ w, ∃ L, Lev L ∧ i w ∈ L := fun w => by
    obtain ⟨a, ha, h⟩ := hlev w
    obtain ⟨L, hL⟩ := exists_slice W a
    exact ⟨L, ⟨a, ha, hL⟩, (hL _).mpr h⟩
  have lev_dir : ∀ L₁ L₂, Lev L₁ → Lev L₂ →
      ∃ L, Lev L ∧ (∀ x, x ∈ L₁ → x ∈ L) ∧ ∀ x, x ∈ L₂ → x ∈ L := by
    rintro L₁ L₂ ⟨a, ha, h1⟩ ⟨b, hb, h2⟩
    obtain ⟨c, hc, hac, hbc⟩ := ok.dir a b ha hb
    obtain ⟨L, hL⟩ := exists_slice W c
    refine ⟨L, ⟨c, hc, hL⟩, fun x hx => (hL x).mpr ?_, fun x hx => (hL x).mpr ?_⟩
    · rcases hac with rfl | hac
      · exact (h1 x).mp hx
      · exact levG_mono hW ok.trans hc hac ((h1 x).mp hx)
    · rcases hbc with rfl | hbc
      · exact (h2 x).mp hx
      · exact levG_mono hW ok.trans hc hbc ((h2 x).mp hx)
  have lev_tr : ∀ L, Lev L → ∀ x, x ∈ L → ∀ v, EE v x → v ∈ L := by
    rintro L ⟨a, -, hL⟩ x hx v hv
    exact (hL v).mpr (levG_trans hW ok.trans ((hL x).mp hx) hv)
  have lev_key : ∀ L, Lev L → ∀ S : V, (∀ s, s ∈ S → s ∈ L) →
      ∃ w : D, ∀ v, EE v (i w) ↔ v ∈ S := by
    rintro L ⟨a, ha, hL⟩ S hS
    obtain ⟨y, hyZ, hy⟩ := stable_full hg (levG_stable hg ok hW ha hL) S hS
    obtain ⟨c, hc, hac⟩ := ok.next a ha
    have hyl : InLev W c y := levG_intro hW hc hyZ (Or.inr fun u hu =>
      ⟨a, hac, (hL u).mp (hS u ((hy u).mp hu))⟩)
    obtain ⟨w, rfl⟩ := (hdom y).mp ⟨c, hc, hyl⟩
    exact ⟨w, hy⟩
  have lev_pow : ∀ L, Lev L → ∃ L', Lev L' ∧ ∀ y, InZ y → (∀ u, EE u y → u ∈ L) → y ∈ L' := by
    rintro L ⟨a, ha, hL⟩
    obtain ⟨c, hc, hac⟩ := ok.next a ha
    obtain ⟨L', hL'⟩ := exists_slice W c
    exact ⟨L', ⟨c, hc, hL'⟩, fun y hyZ hyu =>
      (hL' y).mpr (levG_intro hW hc hyZ (Or.inr fun u hu => ⟨a, hac, (hL u).mp (hyu u hu)⟩))⟩
  -- the least level is the set of the finite ordinals
  obtain ⟨a₀, ha₀, hmin⟩ := ok.wf A ok.nonempty
  obtain ⟨Ω, hΩ⟩ := exists_slice W a₀
  have hΩ' : ∀ x, x ∈ Ω ↔ InOm x := fun x => by
    refine (hΩ x).trans ⟨fun h => ?_, fun h => levG_intro hW ha₀ (om_inZ h) (Or.inl h)⟩
    obtain ⟨-, hxZ, h'⟩ := levG_inv hW h
    rcases h' with hxo | hxu
    · exact hxo
    · refine om_zero ⟨hxZ, fun v hv => ?_⟩
      obtain ⟨b, hb, hbv⟩ := hxu v hv
      exact hmin b (levG_inv hW hbv).1 hb
  exact ⟨isMacBase_of_levels i hi hg hmem hZ hdown Lev lev_mem lev_dir lev_tr lev_key lev_pow hΩ'
      ⟨a₀, ha₀, hΩ⟩,
    sep_of_levels i hi hg hmem hX' Lev lev_mem lev_tr lev_key⟩

end model

end HinU

end FFL.FirstOrder.SetTheory
