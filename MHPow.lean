module

public import MHFull

@[expose] public section

set_option autoImplicit false

/-!
# Levels of the constructible sets against sets with true power sets

In a model of `𝗠𝗛`. `VInj A S`: `A` maps one-to-one into `S` by a relation of the model, not
necessarily a constructible one (`LInj` of `MHCard.lean` is the constructible form).

* `vinj_succ`: if a level above `ω` maps one-to-one into `S`, so does the next level, when `S`
  has the empty set as a member and is closed under pairs. The codes are those of `linj_succ`.
* **`vinj_of_segs`**: let `T` have every set of relations on `S` as a member. If the members
  of the level at `ν` below `x`, in the order of the constructible sets, map one-to-one into
  `S` for every `x` in that level, then the level maps one-to-one into `T`. A member `x` is
  sent to the set of the images of the order below `x` under the one-to-one relations into
  `S`. Two members with a common image are equal, because the order is a well-order. No
  choice is made. `vinj_lim` is the form for a limit ordinal all of whose smaller levels map
  one-to-one into `S`.

These are for comparing the heights of the constructible hierarchy with a hierarchy of sets
closed under subsets, where the model has one.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- `F` maps the members of `L` below `x`, in the order `lt`, one-to-one into `S`. -/
def SegInj {V : Type} [SetStructure V] (F x L lt S : V) : Prop :=
  (∀ y, y ∈ L → (Pr lt y x → ∃ v, v ∈ S ∧ Pr F y v)) ∧
  (∀ y, y ∈ L → ∀ y', y' ∈ L → ∀ v, v ∈ S →
    (Pr lt y x → (Pr lt y' x → (Pr F y v → (Pr F y' v → y = y')))))

def segInjB : BDef (k := 5) (fun V _ v ↦ SegInj (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((BDef.ball 2 ((prB.comp ![4, 0, 2]).imp (BDef.bex 5 (prB.comp ![2, 1, 0])))).and
    (BDef.ball 2 (BDef.ball 3 (BDef.ball 6 ((prB.comp ![6, 2, 4]).imp ((prB.comp ![6, 1, 4]).imp
      ((prB.comp ![3, 2, 0]).imp ((prB.comp ![3, 1, 0]).imp (BDef.eq 2 1))))))))).congr
    fun _ _ _ => Iff.rfl

/-- `v` and `v'` are related by `F` to two members of `L` below `x`, the first equal to the
second or before it. -/
def ImgAt {V : Type} [SetStructure V] (F x L lt v v' : V) : Prop :=
  ∃ y, y ∈ L ∧ ∃ y', y' ∈ L ∧ (Pr lt y x ∧ (Pr lt y' x ∧ ((y = y' ∨ Pr lt y y') ∧
    (Pr F y v ∧ Pr F y' v'))))

def imgAtB : BDef (k := 6) (fun V _ v ↦ ImgAt (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 2 (BDef.bex 3 ((prB.comp ![5, 1, 3]).and ((prB.comp ![5, 0, 3]).and
    (((BDef.eq 1 0).or (prB.comp ![5, 1, 0])).and
      ((prB.comp ![2, 1, 6]).and (prB.comp ![2, 0, 7]))))))).congr fun _ _ _ => Iff.rfl

/-- On `S`, `w` is the image under `F` of the order of the members of `L` below `x`. -/
def ImgR {V : Type} [SetStructure V] (w F x L lt S : V) : Prop :=
  ∀ v, v ∈ S → ∀ v', v' ∈ S → (Pr w v v' ↔ ImgAt F x L lt v v')

def imgRB : BDef (k := 6) (fun V _ v ↦ ImgR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.ball 5 (BDef.ball 6 ((prB.comp ![2, 1, 0]).iff
    (imgAtB.comp ![3, 4, 5, 6, 1, 0])))).congr fun _ _ _ => Iff.rfl

/-- `w` is such an image, for a one-to-one relation in `PF`. -/
def CxR {V : Type} [SetStructure V] (w x L lt S PF : V) : Prop :=
  ∃ F, F ∈ PF ∧ (SegInj F x L lt S ∧ ImgR w F x L lt S)

def cxRB : BDef (k := 6) (fun V _ v ↦ CxR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 5 ((segInjB.comp ![0, 2, 3, 4, 5]).and
    (imgRB.comp ![1, 0, 2, 3, 4, 5]))).congr fun _ _ _ => Iff.rfl

section pow

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `A` maps one-to-one into `S` by a relation of the model. -/
def VInj (A S : V) : Prop := ∃ F : V, InjS F A S

theorem linj_vinj {A S : V} (h : LInj A S) : VInj A S :=
  let ⟨F, _, hF⟩ := h
  ⟨F, hF⟩

omit [Nonempty V] hH in
theorem vinj_dom_mono {A A' S : V} (h : VInj A S) (hA : ∀ z, z ∈ A' → z ∈ A) : VInj A' S :=
  let ⟨F, hF⟩ := h
  ⟨F, injS_dom_mono hF hA⟩

omit [Nonempty V] hH in
theorem vinj_mono {A S S' : V} (h : VInj A S) (hS : ∀ z, z ∈ S → z ∈ S') : VInj A S' :=
  let ⟨F, hF⟩ := h
  ⟨F, injS_mono hF hS⟩

/-- A set maps one-to-one into every set that includes it. -/
theorem vinj_of_sub {A S : V} (hsub : ∀ z, z ∈ A → z ∈ S) : VInj A S := by
  let F : V := sepB (k := 1) (BDef.bex 1 (isOpB.comp ![1, 0, 0])) (prodS A S) ![A]
  have hFz : ∀ z, z ∈ F ↔ z ∈ prodS A S ∧ ∃ a, a ∈ A ∧ IsOp z a a := fun z => mem_sepB _ _ _ z
  refine ⟨F, fun u hu => ⟨u, hsub u hu, hin_rl_iff.mpr ((hFz _).mpr
    ⟨mem_prodS.mpr ⟨u, hu, u, hsub u hu, rfl⟩, u, hu, isOp_kp u u⟩)⟩,
    fun u u' v _ _ h1 h2 => ?_⟩
  obtain ⟨-, a, -, hop⟩ := (hFz _).mp (hin_rl_iff.mp h1)
  obtain ⟨-, a', -, hop'⟩ := (hFz _).mp (hin_rl_iff.mp h2)
  obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
  obtain ⟨e1', e2'⟩ := kp_inj (isOp_iff.mp hop')
  rw [e1, e1', ← e2, ← e2']

/-- One-to-one relations compose. -/
theorem vinj_comp {A B C : V} (h1 : VInj A B) (h2 : VInj B C) : VInj A C := by
  obtain ⟨F, hF⟩ := h1
  obtain ⟨G, hG⟩ := h2
  let K : V := sepB (k := 5) (BDef.bex 1 (BDef.bex 4 (BDef.bex 4 ((isOpB.comp ![3, 2, 1]).and
    ((prB.comp ![7, 2, 0]).and (prB.comp ![8, 0, 1])))))) (prodS A C) ![A, B, C, F, G]
  have hKz : ∀ q, q ∈ K ↔ q ∈ prodS A C ∧ ∃ a, a ∈ A ∧ ∃ c, c ∈ C ∧ ∃ b, b ∈ B ∧
      (IsOp q a c ∧ (Pr F a b ∧ Pr G b c)) := fun q => mem_sepB _ _ _ q
  have hinv : ∀ a c, kp a c ∈ K → ∃ b, b ∈ B ∧ (Pr F a b ∧ Pr G b c) := by
    intro a c h
    obtain ⟨-, a₁, -, c₁, -, b, hb, hop, f1, f2⟩ := (hKz _).mp h
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact ⟨b, hb, f1, f2⟩
  refine ⟨K, fun a ha => ?_, fun a a' c ha ha' k1 k2 => ?_⟩
  · obtain ⟨b, hb, hr⟩ := hF.1 a ha
    obtain ⟨c, hc, hr'⟩ := hG.1 b hb
    exact ⟨c, hc, hin_rl_iff.mpr ((hKz _).mpr ⟨mem_prodS.mpr ⟨a, ha, c, hc, rfl⟩, a, ha, c, hc,
      b, hb, isOp_kp a c, pr_iff.mpr (hin_rl_iff.mp hr), pr_iff.mpr (hin_rl_iff.mp hr')⟩)⟩
  · obtain ⟨b, hb, f1, f2⟩ := hinv a c (hin_rl_iff.mp k1)
    obtain ⟨b', hb', f1', f2'⟩ := hinv a' c (hin_rl_iff.mp k2)
    have e : b = b' := hG.2 b b' c hb hb' (hin_rl_iff.mpr (pr_iff.mp f2))
      (hin_rl_iff.mpr (pr_iff.mp f2'))
    rw [← e] at f1'
    exact hF.2 a a' b ha ha' (hin_rl_iff.mpr (pr_iff.mp f1)) (hin_rl_iff.mpr (pr_iff.mp f1'))

/-- **If a level above `ω` maps one-to-one into `S`, so does the next level**, when `S` has the
empty set as a member and is closed under pairs. -/
theorem vinj_succ {S δ : V} (hSp : ∀ a b, a ∈ S → b ∈ S → kp a b ∈ S) (h0 : (∅ : V) ∈ S)
    (hδ : Big δ) (h : VInj (Lev δ) S) : VInj (Lev (sc δ)) S := by
  obtain ⟨G, hG⟩ := h
  let F : V := sepB (k := 5)
    (BDef.bex 1 (BDef.bex 6 ((isOpB.comp ![2, 1, 0]).and (cdRB.comp ![1, 0, 4, 5, 6, 7]))))
    (prodS (Lev (sc δ)) S) ![Lev (sc δ), G, Lev δ, LtS δ, S]
  have hFz : ∀ z, z ∈ F ↔ z ∈ prodS (Lev (sc δ)) S ∧ ∃ x, x ∈ Lev (sc δ) ∧ ∃ c, c ∈ S ∧
      (IsOp z x c ∧ CdR x c G (Lev δ) (LtS δ) S) := fun z => mem_sepB _ _ _ z
  have hto : ∀ x c, x ∈ Lev (sc δ) → c ∈ S → CdR x c G (Lev δ) (LtS δ) S → kp x c ∈ F :=
    fun x c hx hc hcd => (hFz _).mpr ⟨mem_prodS.mpr ⟨x, hx, c, hc, rfl⟩, x, hx, c, hc,
      isOp_kp x c, hcd⟩
  have hfrom : ∀ x c, kp x c ∈ F → CdR x c G (Lev δ) (LtS δ) S := by
    intro x c hxc
    obtain ⟨-, x', -, c', -, hop, hcd⟩ := (hFz _).mp hxc
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact hcd
  have hGinj : ∀ u, u ∈ Lev δ → ∀ u', u' ∈ Lev δ → ∀ v, Pr G u v → Pr G u' v → u = u' :=
    fun u hu u' hu' v h1 h2 => hG.2 u u' v hu hu' (hin_rl_iff.mpr (pr_iff.mp h1))
      (hin_rl_iff.mpr (pr_iff.mp h2))
  have hGtot : ∀ u, u ∈ Lev δ → ∃ v, v ∈ S ∧ Pr G u v := fun u hu =>
    let ⟨v, hv, hr⟩ := hG.1 u hu
    ⟨v, hv, pr_iff.mpr (hin_rl_iff.mp hr)⟩
  have hemp : ∀ w, w ∈ (∅ : V) → False := fun w hw => absurd hw (by simp)
  refine ⟨F, fun x hx => ?_, fun x x' v _ _ h1 h2 =>
    cdR_inj hGinj (hfrom x v (hin_rl_iff.mp h1)) (hfrom x' v (hin_rl_iff.mp h2))⟩
  rcases lev_sc_cases hδ.1 hx with hxδ | hin
  · obtain ⟨g, hg, hpr⟩ := hGtot x hxδ
    exact ⟨kp ∅ g, hSp _ _ h0 hg, hin_rl_iff.mpr (hto x _ hx (hSp _ _ h0 hg)
      (Or.inr (Or.inl ⟨hxδ, g, hg, ∅, h0, hemp, hpr, isOp_kp ∅ g⟩)))⟩
  · rcases hin with e | ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, hD⟩
    · exact ⟨∅, h0, hin_rl_iff.mpr (hto x _ hx h0 (Or.inl ⟨e, hemp⟩))⟩
    · obtain ⟨s', hs', p0⟩ := hGtot s hs
      obtain ⟨t₁, ht1, p1⟩ := hGtot y₁ h1
      obtain ⟨t₂, ht2, p2⟩ := hGtot y₂ h2
      obtain ⟨t₃, ht3, p3⟩ := hGtot y₃ h3
      have q1 := hSp _ _ hs' ht1
      have q2 := hSp _ _ ht2 ht3
      exact ⟨kp (kp s' t₁) (kp t₂ t₃), hSp _ _ q1 q2, hin_rl_iff.mpr (hto x _ hx (hSp _ _ q1 q2)
        (Or.inr (Or.inr ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, s', hs', t₁, ht1, t₂, ht2, t₃, ht3,
          p0, p1, p2, p3, hD, kp s' t₁, q1, kp t₂ t₃, q2, isOp_kp _ _, isOp_kp _ _,
          isOp_kp _ _⟩)))⟩

/-- **The step through two power sets.** If the members of the level at `ν` below each of its
members map one-to-one into `S`, and every set of relations on `S` is a member of `T`, then the
level at `ν` maps one-to-one into `T`. -/
theorem vinj_of_segs {ν S T : V} (hν : Ord ν)
    (hseg : ∀ x, x ∈ Lev ν → ∃ F : V, SegInj F x (Lev ν) (LtS ν) S)
    (hT : ∀ C : V, (∀ w, w ∈ C → ∀ p, p ∈ w → p ∈ prodS S S) → C ∈ T) : VInj (Lev ν) T := by
  have hlt : ∀ y x : V, Pr (LtS ν) y x ↔ y ∈ Lev ν ∧ (x ∈ Lev ν ∧ LtL y x) :=
    fun y x => lts_iff hν
  let PF : V := ℘ (prodS (Lev ν) S)
  let PP : V := ℘ (prodS S S)
  -- a common image preserves the order
  have hA : ∀ x x' F F' w : V, ImgR w F x (Lev ν) (LtS ν) S → ImgR w F' x' (Lev ν) (LtS ν) S →
      SegInj F x (Lev ν) (LtS ν) S → SegInj F' x' (Lev ν) (LtS ν) S →
      ∀ y₁ y₂ y₁' y₂' v₁ v₂ : V, v₁ ∈ S → v₂ ∈ S → Pr (LtS ν) y₁ x → Pr (LtS ν) y₂ x →
        Pr (LtS ν) y₁' x' → Pr (LtS ν) y₂' x' → Pr F y₁ v₁ → Pr F' y₁' v₁ → Pr F y₂ v₂ →
        Pr F' y₂' v₂ → LtL y₁ y₂ → LtL y₁' y₂' := by
    intro x x' F F' w hw hw' hF hF' y₁ y₂ y₁' y₂' v₁ v₂ hv1 hv2 l1 l2 l1' l2' f1 f1' f2 f2' h
    have k1 := (hlt y₁ x).mp l1
    have k2 := (hlt y₂ x).mp l2
    have k1' := (hlt y₁' x').mp l1'
    have k2' := (hlt y₂' x').mp l2'
    have hp : Pr w v₁ v₂ := (hw v₁ hv1 v₂ hv2).mpr ⟨y₁, k1.1, y₂, k2.1, l1, l2,
      Or.inr ((hlt y₁ y₂).mpr ⟨k1.1, k2.1, h⟩), f1, f2⟩
    obtain ⟨a, ha, a', ha', la, la', hor, fa, fa'⟩ := (hw' v₁ hv1 v₂ hv2).mp hp
    have ea : a = y₁' := hF'.2 a ha y₁' k1'.1 v₁ hv1 la l1' fa f1'
    have ea' : a' = y₂' := hF'.2 a' ha' y₂' k2'.1 v₂ hv2 la' l2' fa' f2'
    rw [ea, ea'] at hor
    rcases hor with e | h'
    · exfalso
      rw [← e] at f2'
      have hp2 : Pr w v₂ v₁ := (hw' v₂ hv2 v₁ hv1).mpr ⟨y₁', k1'.1, y₁', k1'.1, l1', l1',
        Or.inl rfl, f2', f1'⟩
      obtain ⟨c, hc, c', hc', lc, lc', hor2, fc, fc'⟩ := (hw v₂ hv2 v₁ hv1).mp hp2
      have ec : c = y₂ := hF.2 c hc y₂ k2.1 v₂ hv2 lc l2 fc f2
      have ec' : c' = y₁ := hF.2 c' hc' y₁ k1.1 v₁ hv1 lc' l1 fc' f1
      rw [ec, ec'] at hor2
      rcases hor2 with e2 | h2
      · rw [e2] at h
        exact ltL_irrefl' hν k1.1 h
      · exact ltL_asymm hν k1.1 k2.1 h ((hlt y₂ y₁).mp h2).2.2
    · exact ((hlt y₁' y₂').mp h').2.2
  -- two members with a common image are equal
  have hkey : ∀ x x' F F' w : V, ImgR w F x (Lev ν) (LtS ν) S →
      ImgR w F' x' (Lev ν) (LtS ν) S → SegInj F x (Lev ν) (LtS ν) S →
      SegInj F' x' (Lev ν) (LtS ν) S → x ∈ Lev ν → x' ∈ Lev ν → LtL x' x → False := by
    intro x x' F F' w hw hw' hF hF' hx hx' hlx
    let Z : V := sepB (k := 7) ((prB.comp ![3, 0, 1]).and (BDef.bex 7 ((prB.comp ![4, 0, 3]).and
      ((prB.comp ![4, 0, 1]).and (BDef.bex 5 ((prB.comp ![7, 2, 0]).and
        (prB.comp ![8, 1, 0]))))))) (Lev ν) ![x, x', LtS ν, S, F, F', Lev ν]
    have hZ : ∀ z, z ∈ Z ↔ z ∈ Lev ν ∧ (Pr (LtS ν) z x ∧ ∃ z', z' ∈ Lev ν ∧
        (Pr (LtS ν) z' x' ∧ (Pr (LtS ν) z' z ∧ ∃ v, v ∈ S ∧ (Pr F z v ∧ Pr F' z' v)))) :=
      fun z => mem_sepB _ _ _ z
    have lxx : Pr (LtS ν) x' x := (hlt x' x).mpr ⟨hx', hx, hlx⟩
    have hne : ∃ z, z ∈ Z := by
      obtain ⟨v, hv, fv⟩ := hF.1 x' hx' lxx
      have hp : Pr w v v := (hw v hv v hv).mpr ⟨x', hx', x', hx', lxx, lxx, Or.inl rfl, fv, fv⟩
      obtain ⟨a, ha, a', -, la, -, -, fa, -⟩ := (hw' v hv v hv).mp hp
      exact ⟨x', (hZ x').mpr ⟨hx', lxx, a, ha, la, la, v, hv, fv, fa⟩⟩
    obtain ⟨m, hm, hmin⟩ := ltL_least hν Z (fun z hz => ((hZ z).mp hz).1) hne
    obtain ⟨hmL, lmx, m', hm'L, lm'x', lm'm, v, hv, fm, fm'⟩ := (hZ m).mp hm
    have hm'm : LtL m' m := ((hlt m' m).mp lm'm).2.2
    have lm'x : Pr (LtS ν) m' x := (hlt m' x).mpr ⟨hm'L, hx,
      ltL_trans hν hm'L hmL hx hm'm ((hlt m x).mp lmx).2.2⟩
    obtain ⟨u, hu, fu⟩ := hF.1 m' hm'L lm'x
    have hp : Pr w u u := (hw u hu u hu).mpr ⟨m', hm'L, m', hm'L, lm'x, lm'x, Or.inl rfl,
      fu, fu⟩
    obtain ⟨a, ha, a', -, la, -, -, fa, -⟩ := (hw' u hu u hu).mp hp
    have lam' : LtL a m' := hA x x' F F' w hw hw' hF hF' m' m a m' u v hu hv lm'x lmx la lm'x'
      fu fa fm fm' hm'm
    exact hmin m' ((hZ m').mpr ⟨hm'L, lm'x, a, ha, la, (hlt a m').mpr ⟨ha, hm'L, lam'⟩, u, hu,
      fu, fa⟩) hm'm
  -- the set of the images for `x`
  let C : V → V := fun x => sepB (k := 5) cxRB PP ![x, Lev ν, LtS ν, S, PF]
  have hC : ∀ x w, w ∈ C x ↔ w ∈ PP ∧ CxR w x (Lev ν) (LtS ν) S PF :=
    fun x w => mem_sepB _ _ _ w
  have hCne : ∀ x, x ∈ Lev ν → ∃ w, w ∈ C x := by
    intro x hx
    obtain ⟨F, hF⟩ := hseg x hx
    let F' : V := sepB (k := 1) (BDef.mem 0 1) (prodS (Lev ν) S) ![F]
    have hF'z : ∀ z, z ∈ F' ↔ z ∈ prodS (Lev ν) S ∧ z ∈ F := fun z => mem_sepB _ _ _ z
    have hF'pr : ∀ y v, y ∈ Lev ν → v ∈ S → (Pr F' y v ↔ Pr F y v) := by
      intro y v hy hv
      rw [pr_iff, pr_iff, hF'z]
      exact ⟨fun h => h.2, fun h => ⟨mem_prodS.mpr ⟨y, hy, v, hv, rfl⟩, h⟩⟩
    have hF'S : SegInj F' x (Lev ν) (LtS ν) S :=
      ⟨fun y hy hl => let ⟨v, hv, h⟩ := hF.1 y hy hl; ⟨v, hv, (hF'pr y v hy hv).mpr h⟩,
        fun y hy y' hy' v hv l l' h h' => hF.2 y hy y' hy' v hv l l' ((hF'pr y v hy hv).mp h)
          ((hF'pr y' v hy' hv).mp h')⟩
    have hF'PF : F' ∈ PF := mem_power_iff.mpr fun z hz => ((hF'z z).mp hz).1
    let w : V := sepB (k := 5) (BDef.bex 5 (BDef.bex 6 ((isOpB.comp ![2, 1, 0]).and
      (imgAtB.comp ![3, 4, 5, 6, 1, 0])))) (prodS S S) ![F', x, Lev ν, LtS ν, S]
    have hwz : ∀ p, p ∈ w ↔ p ∈ prodS S S ∧ ∃ v, v ∈ S ∧ ∃ v', v' ∈ S ∧
        (IsOp p v v' ∧ ImgAt F' x (Lev ν) (LtS ν) v v') := fun p => mem_sepB _ _ _ p
    have hwR : ImgR w F' x (Lev ν) (LtS ν) S := by
      intro v hv v' hv'
      rw [pr_iff, hwz]
      constructor
      · rintro ⟨-, v₁, -, v₁', -, hop, h⟩
        obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
        rw [e1, e2]
        exact h
      · intro h
        exact ⟨mem_prodS.mpr ⟨v, hv, v', hv', rfl⟩, v, hv, v', hv', isOp_kp v v', h⟩
    exact ⟨w, (hC x w).mpr ⟨mem_power_iff.mpr fun p hp => ((hwz p).mp hp).1, F', hF'PF, hF'S,
      hwR⟩⟩
  have hCT : ∀ x, C x ∈ T := fun x => hT (C x) fun w hw p hp =>
    mem_power_iff.mp ((hC x w).mp hw).1 p hp
  have hCinj : ∀ x x', x ∈ Lev ν → x' ∈ Lev ν → C x = C x' → x = x' := by
    intro x x' hx hx' e
    rcases ltL_tri hν hx hx' with h | h | h
    · exfalso
      obtain ⟨w, hw⟩ := hCne x' hx'
      have hw' : w ∈ C x := by
        rw [e]
        exact hw
      obtain ⟨-, F, -, hF, hwF⟩ := (hC x' w).mp hw
      obtain ⟨-, F', -, hF', hwF'⟩ := (hC x w).mp hw'
      exact hkey x' x F F' w hwF hwF' hF hF' hx' hx h
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := hCne x hx
      have hw' : w ∈ C x' := by
        rw [← e]
        exact hw
      obtain ⟨-, F, -, hF, hwF⟩ := (hC x w).mp hw
      obtain ⟨-, F', -, hF', hwF'⟩ := (hC x' w).mp hw'
      exact hkey x x' F F' w hwF hwF' hF hF' hx hx' h
  -- the map
  let J : V := sepB (k := 6) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    ((BDef.ball 0 ((BDef.mem 0 9).and (cxRB.comp ![0, 2, 4, 6, 7, 8]))).and
      (BDef.ball 8 ((cxRB.comp ![0, 2, 4, 6, 7, 8]).imp (BDef.mem 0 1)))))))
    (prodS (Lev ν) T) ![Lev ν, T, LtS ν, S, PF, PP]
  have hJz : ∀ q, q ∈ J ↔ q ∈ prodS (Lev ν) T ∧ ∃ x, x ∈ Lev ν ∧ ∃ c, c ∈ T ∧ (IsOp q x c ∧
      ((∀ w, w ∈ c → (w ∈ PP ∧ CxR w x (Lev ν) (LtS ν) S PF)) ∧
        (∀ w, w ∈ PP → (CxR w x (Lev ν) (LtS ν) S PF → w ∈ c)))) := fun q => mem_sepB _ _ _ q
  have hJ : ∀ x c, kp x c ∈ J → c = C x := by
    intro x c h
    obtain ⟨-, x₁, -, c₁, -, hop, k1, k2⟩ := (hJz _).mp h
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact mem_ext fun w => ⟨fun hw => (hC x₁ w).mpr (k1 w hw),
      fun hw => let ⟨a, b⟩ := (hC x₁ w).mp hw; k2 w a b⟩
  refine ⟨J, fun x hx => ⟨C x, hCT x, hin_rl_iff.mpr ((hJz _).mpr
    ⟨mem_prodS.mpr ⟨x, hx, C x, hCT x, rfl⟩, x, hx, C x, hCT x, isOp_kp _ _,
      fun w hw => (hC x w).mp hw, fun w h1 h2 => (hC x w).mpr ⟨h1, h2⟩⟩)⟩,
    fun x x' c hx hx' h1 h2 => ?_⟩
  exact hCinj x x' hx hx' ((hJ x c (hin_rl_iff.mp h1)).symm.trans (hJ x' c (hin_rl_iff.mp h2)))

/-- The hypothesis of `vinj_of_segs` at a limit ordinal all of whose smaller levels map
one-to-one into `S`. -/
theorem segInj_of_levels {ν S : V} (hν : Lim ν) (h : ∀ δ, δ ∈ ν → VInj (Lev δ) S) :
    ∀ x, x ∈ Lev ν → ∃ F : V, SegInj F x (Lev ν) (LtS ν) S := by
  intro x hx
  obtain ⟨β, hβ, hcov⟩ := ltL_cover hν.1 hx
  obtain ⟨F, hF⟩ := h (sc β) (hν.2.2 β hβ)
  have hlt : ∀ y : V, Pr (LtS ν) y x → y ∈ Lev (sc β) :=
    fun y hy => hcov y ((lts_iff hν.1).mp hy).2.2
  exact ⟨F, fun y _ hl => let ⟨v, hv, hr⟩ := hF.1 y (hlt y hl)
      ⟨v, hv, pr_iff.mpr (hin_rl_iff.mp hr)⟩,
    fun y _ y' _ v _ l l' f f' => hF.2 y y' v (hlt y l) (hlt y' l')
      (hin_rl_iff.mpr (pr_iff.mp f)) (hin_rl_iff.mpr (pr_iff.mp f'))⟩

/-- **A limit level whose smaller levels map one-to-one into `S` maps one-to-one into `T`**,
when every set of relations on `S` is a member of `T`. -/
theorem vinj_lim {ν S T : V} (hν : Lim ν) (h : ∀ δ, δ ∈ ν → VInj (Lev δ) S)
    (hT : ∀ C : V, (∀ w, w ∈ C → ∀ p, p ∈ w → p ∈ prodS S S) → C ∈ T) : VInj (Lev ν) T :=
  vinj_of_segs hν.1 (segInj_of_levels hν h) hT

end pow

end MH

end FFL.FirstOrder.SetTheory
