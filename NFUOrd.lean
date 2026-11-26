module

public import NFULevels

@[expose] public section

set_option autoImplicit false

/-!
# Ordinals among the types, and Hartogs' set, in a model of `𝗡𝗙𝗨𝗜`

The ordinals here are von Neumann's, among the types of well-founded pointed graphs: a type
`α` is an ordinal (`IsOrd α`) if membership `E` is transitive on it and any two of its members
are equal or one is a member of the other.

* `ee_irrefl`, `ee_asymm`, `ee_no3`: `E` has no cycles of length at most three.
* `ord_mem`: the members of an ordinal are ordinals. `ord_sub`: an ordinal whose members are
  all members of another ordinal is equal to it or a member of it. `ord_tri`: two ordinals, the
  members of one of which are fixed types, are equal or one is a member of the other.
* `InH B α`: `α` is an ordinal whose members map one-to-one into the set `B`. For a set `B` of
  fixed types, the set `H` of these ordinals is **Hartogs' set** of `B`:
  * `hart_fixed`: its members are fixed. The map into `B` carries the picture of `α` to a
    pointed graph on fixed nodes, whose type is fixed (`fixed_of_nodes`).
  * `hart_down`: it is closed under members. `hart_no_inj`: it does not map one-to-one
    into `B`, because the type whose members are the members of `H` is an ordinal.
  * `hart_next`: if `B` contains the finite ordinals, `H` has no last element.
  * `hart_idxOK`: with membership restricted to it, `H` satisfies the conditions `IdxOK` of
    `NFULevels.lean`. So the types of rank below `H` form a model of `𝗭`.

This is Lemma 17.7 of the draft *Choice and Consistency Strength in NF and NFU* (v15), in terms
of fixed types in place of strongly cantorian sets.
-/

namespace FFL.FirstOrder.SetTheory

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- Membership is transitive on `x`: the members of the members of `x` are members of `x`. -/
def TrE (x : V) : Prop := ∀ u v : V, EE u x → EE v u → EE v x

/-- `x` is an ordinal. -/
def IsOrd (x : V) : Prop :=
  InZ x ∧ TrE x ∧ ∀ u v : V, EE u x → EE v x → (u = v ∨ EE u v ∨ EE v u)

/-- `f` maps the members of `α` one-to-one into `B`. -/
def InjOn (f α B : V) : Prop :=
  (∀ u : V, EE u α → ∃ b : V, b ∈ B ∧ Rl f u b) ∧
  (∀ u u' b : V, EE u α → EE u' α → Rl f u b → Rl f u' b → u = u')

/-- `α` is an ordinal whose members map one-to-one into `B`. -/
def InH (B α : V) : Prop := IsOrd α ∧ ∃ f : V, InjOn f α B

end defs

section sdefs

def trED : SDef ![6] (fun _ _ v ↦ TrE (v 0)) :=
  (SDef.all 6 (SDef.all 6 ((eeD.comp ![1, 2] 0).imp ((eeD.comp ![0, 1] 0).imp
    (eeD.comp ![0, 2] 0))))).congr fun _ _ _ => Iff.rfl

def isOrdD : SDef ![6] (fun _ _ v ↦ IsOrd (v 0)) :=
  ((inZD.comp ![0] 0).and ((trED.comp ![0] 0).and (SDef.all 6 (SDef.all 6
    ((eeD.comp ![1, 2] 0).imp ((eeD.comp ![0, 2] 0).imp ((SDef.eq 1 0).or
      ((eeD.comp ![1, 0] 0).or (eeD.comp ![0, 1] 0))))))))).congr fun _ _ _ => Iff.rfl

def injOnD : SDef ![9, 6, 7] (fun _ _ v ↦ InjOn (v 0) (v 1) (v 2)) :=
  ((SDef.all 6 ((eeD.comp ![0, 2] 0).imp (SDef.ex 6 ((SDef.mem 0 4).and
      (rlD.comp ![2, 1, 0] 6))))).and
    (SDef.all 6 (SDef.all 6 (SDef.all 6 ((eeD.comp ![2, 4] 0).imp ((eeD.comp ![1, 4] 0).imp
      ((rlD.comp ![3, 2, 0] 6).imp ((rlD.comp ![3, 1, 0] 6).imp (SDef.eq 2 1))))))))).congr
    fun _ _ _ => Iff.rfl

def inHD : SDef ![7, 6] (fun _ _ v ↦ InH (v 0) (v 1)) :=
  ((isOrdD.comp ![1] 0).and (SDef.ex 9 (injOnD.comp ![0, 2, 1] 0))).congr fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-! ### Membership between types has no short cycles -/

theorem ee_irrefl {a : V} (h : EE a a) : False := by
  obtain ⟨S, hS⟩ := exists_sing a
  obtain ⟨x, hx, -, hmin⟩ := ee_wf S ⟨a, (hS a).mpr rfl, h.1⟩
  obtain rfl := (hS x).mp hx
  exact hmin x hx h

theorem ee_asymm {a b : V} (h1 : EE a b) (h2 : EE b a) : False := by
  obtain ⟨S, hS⟩ := exists_up a b
  obtain ⟨x, hx, -, hmin⟩ := ee_wf S ⟨a, (hS a).mpr (Or.inl rfl), h1.1⟩
  rcases (hS x).mp hx with rfl | rfl
  · exact hmin b ((hS b).mpr (Or.inr rfl)) h2
  · exact hmin a ((hS a).mpr (Or.inl rfl)) h1

theorem ee_no3 {a b c : V} (h1 : EE a b) (h2 : EE b c) (h3 : EE c a) : False := by
  obtain ⟨S, hS⟩ := ((SDef.eq (τ := ![0, 0, 0, 0]) 0 1).or ((SDef.eq 0 2).or
    (SDef.eq 0 3))).comprehensionU ![a, b, c]
  have hS' : ∀ x, x ∈ S ↔ x = a ∨ x = b ∨ x = c := hS
  obtain ⟨x, hx, -, hmin⟩ := ee_wf S ⟨a, (hS' a).mpr (Or.inl rfl), h1.1⟩
  rcases (hS' x).mp hx with rfl | rfl | rfl
  · exact hmin c ((hS' c).mpr (Or.inr (Or.inr rfl))) h3
  · exact hmin a ((hS' a).mpr (Or.inl rfl)) h1
  · exact hmin b ((hS' b).mpr (Or.inr (Or.inl rfl))) h2

/-! ### Ordinals -/

/-- The members of an ordinal are ordinals. -/
theorem ord_mem {α u : V} (hα : IsOrd α) (hu : EE u α) : IsOrd u := by
  refine ⟨hu.1, fun v w hv hw => ?_, fun v w hv hw =>
    hα.2.2 v w (hα.2.1 u v hu hv) (hα.2.1 u w hu hw)⟩
  have hvα : EE v α := hα.2.1 u v hu hv
  have hwα : EE w α := hα.2.1 v w hvα hw
  rcases hα.2.2 u w hu hwα with h | h | h
  · rw [← h] at hw
    exact (ee_asymm hw hv).elim
  · exact (ee_no3 h hw hv).elim
  · exact h

/-- An ordinal whose members are all members of the ordinal `β` is `β` or a member of `β`. -/
theorem ord_sub {α β : V} (hα : IsOrd α) (hβ : IsOrd β) (hsub : ∀ u, EE u α → EE u β)
    (hne : α ≠ β) : EE α β := by
  obtain ⟨D, hD⟩ := ((eeD.comp (τ' := ![6, 6, 6]) ![0, 1] 0).and
    (eeD.comp ![0, 2] 0).not).comprehensionU ![β, α]
  have hD' : ∀ u, u ∈ D ↔ EE u β ∧ ¬ EE u α := hD
  have hne' : ∃ u, u ∈ D := by
    by_contra h
    exact hne (ee_ext hα.1 hβ.1 fun u => ⟨hsub u, fun hu => by
      by_contra hn
      exact h ⟨u, (hD' u).mpr ⟨hu, hn⟩⟩⟩)
  obtain ⟨u₀, hu₀⟩ := hne'
  obtain ⟨γ, hγD, -, hmin⟩ := ee_wf D ⟨u₀, hu₀, ((hD' u₀).mp hu₀).1.1⟩
  obtain ⟨hγβ, hγα⟩ := (hD' γ).mp hγD
  have e : γ = α := ee_ext hγβ.1 hα.1 fun v => ⟨fun hv => by
      by_contra hvα
      exact hmin v ((hD' v).mpr ⟨hβ.2.1 γ v hγβ hv, hvα⟩) hv,
    fun hv => by
      rcases hβ.2.2 v γ (hsub v hv) hγβ with h | h | h
      · rw [h] at hv
        exact (hγα hv).elim
      · exact h
      · exact (hγα (hα.2.1 v γ hv h)).elim⟩
  rw [e] at hγβ
  exact hγβ

/-- **Two ordinals are equal or one is a member of the other**, when the members of the first
are fixed types. -/
theorem ord_tri {g α β : V} (hg : IsEg g) (hα : IsOrd α) (hβ : IsOrd β)
    (hfα : ∀ u, EE u α → Fixed g u) : α = β ∨ EE α β ∨ EE β α := by
  obtain ⟨I, hI⟩ := ((eeD.comp (τ' := ![6, 6, 6]) ![0, 1] 0).and
    (eeD.comp ![0, 2] 0)).comprehensionU ![α, β]
  have hI' : ∀ u, u ∈ I ↔ EE u α ∧ EE u β := hI
  obtain ⟨γ, hγZ, -, hγ⟩ := exists_type_of_fixed hg (S := I) fun s hs => hfα s ((hI' s).mp hs).1
  have hγ' : ∀ v, EE v γ ↔ EE v α ∧ EE v β := fun v => (hγ v).trans (hI' v)
  have hγo : IsOrd γ := ⟨hγZ,
    fun u v hu hv => (hγ' v).mpr ⟨hα.2.1 u v ((hγ' u).mp hu).1 hv, hβ.2.1 u v ((hγ' u).mp hu).2 hv⟩,
    fun u v hu hv => hα.2.2 u v ((hγ' u).mp hu).1 ((hγ' v).mp hv).1⟩
  by_cases h1 : γ = α
  · by_cases h2 : γ = β
    · exact Or.inl (h1.symm.trans h2)
    · have := ord_sub hγo hβ (fun u hu => ((hγ' u).mp hu).2) h2
      rw [h1] at this
      exact Or.inr (Or.inl this)
  · have hγα := ord_sub hγo hα (fun u hu => ((hγ' u).mp hu).1) h1
    by_cases h2 : γ = β
    · rw [h2] at hγα
      exact Or.inr (Or.inr hγα)
    · have hγβ := ord_sub hγo hβ (fun u hu => ((hγ' u).mp hu).2) h2
      exact (ee_irrefl ((hγ' γ).mpr ⟨hγα, hγβ⟩)).elim

/-- The finite ordinals are ordinals. -/
theorem om_isOrd : ∀ n : V, InOm n → IsOrd n := by
  refine om_ind 0 isOrdD (![] : Fin 0 → V) (fun z hz => ?_) (fun y _ ih w hw => ?_)
  · show IsOrd z
    exact ⟨hz.1, fun u _ hu => absurd hu (hz.2 u), fun u _ hu => absurd hu (hz.2 u)⟩
  · show IsOrd w
    have ih' : IsOrd y := ih
    have hw' : ∀ u, EE u w ↔ EE u y ∨ u = y := hw.2.2
    refine ⟨hw.2.1, fun u v hu hv => ?_, fun u v hu hv => ?_⟩
    · rcases (hw' u).mp hu with h | h
      · exact (hw' v).mpr (Or.inl (ih'.2.1 u v h hv))
      · rw [h] at hv
        exact (hw' v).mpr (Or.inl hv)
    · rcases (hw' u).mp hu with h | h
      · rcases (hw' v).mp hv with h' | h'
        · exact ih'.2.2 u v h h'
        · rw [← h'] at h
          exact Or.inr (Or.inl h)
      · rcases (hw' v).mp hv with h' | h'
        · rw [← h] at h'
          exact Or.inr (Or.inr h')
        · exact Or.inl (h.trans h'.symm)

/-- The successor of finite ordinals is one-to-one. -/
theorem succ_inj' {a a' d : V} (h : Succ a d) (h' : Succ a' d) : a = a' := by
  rcases (h'.2.2 a).mp ((h.2.2 a).mpr (Or.inr rfl)) with h1 | h1
  · rcases (h.2.2 a').mp ((h'.2.2 a').mpr (Or.inr rfl)) with h2 | h2
    · exact (ee_asymm h1 h2).elim
    · exact h2.symm
  · exact h1

/-! ### Hartogs' set -/

theorem exists_H (B : V) : ∃ H : V, ∀ α, α ∈ H ↔ InH B α :=
  (inHD.comp (τ' := ![6, 7]) ![1, 0] 0).comprehensionU ![B]

/-- Hartogs' set is closed under members. -/
theorem hart_down {B α u : V} (h : InH B α) (hu : EE u α) : InH B u := by
  obtain ⟨hα, f, hf1, hf2⟩ := h
  exact ⟨ord_mem hα hu, f, fun v hv => hf1 v (hα.2.1 u v hu hv),
    fun v v' b hv hv' => hf2 v v' b (hα.2.1 u v hu hv) (hα.2.1 u v' hu hv')⟩

/-- **The members of Hartogs' set of a set of fixed types are fixed.** -/
theorem hart_fixed {g B α : V} (hg : IsEg g) (hB : ∀ b, b ∈ B → Fixed g b) (h : InH B α) :
    Fixed g α := by
  obtain ⟨hα, f, hf1, hf2⟩ := h
  -- the point of the new graph: the type whose members are the members of `B`
  obtain ⟨t, -, htfix, ht⟩ := exists_type_of_fixed hg hB
  have htB : t ∉ B := fun h => ee_irrefl ((ht t).mpr h)
  -- the new graph, on `B` and `t`
  obtain ⟨r, hr⟩ := exists_rel 6 (((SDef.mem (τ := ![6, 6, 9, 6, 7, 6]) 0 4).and
    ((SDef.mem 1 4).and (SDef.ex 6 (SDef.ex 6 ((eeD.comp ![1, 0] 0).and
      ((eeD.comp ![0, 5] 0).and ((rlD.comp ![4, 1, 2] 6).and (rlD.comp ![4, 0, 3] 6)))))))).or
    ((SDef.eq 1 5).and ((SDef.mem 0 4).and (SDef.ex 6 ((eeD.comp ![0, 4] 0).and
      (rlD.comp ![3, 0, 1] 6)))))) ![f, α, B, t]
  have hr' : ∀ b b', Rl r b b' ↔
      (b ∈ B ∧ b' ∈ B ∧ ∃ u u', EE u u' ∧ EE u' α ∧ Rl f u b ∧ Rl f u' b') ∨
      (b' = t ∧ b ∈ B ∧ ∃ u, EE u α ∧ Rl f u b) := hr
  have hwf : WF r := by
    rintro X ⟨c₀, hc₀⟩
    obtain ⟨X', hX'⟩ := ((eeD.comp (τ' := ![6, 6, 7, 7, 9]) ![0, 1] 0).and (SDef.ex 6
      ((SDef.mem 0 3).and ((SDef.mem 0 4).and (rlD.comp ![5, 1, 0] 6))))).comprehensionU
      ![α, X, B, f]
    have hX'' : ∀ u, u ∈ X' ↔ EE u α ∧ ∃ b, b ∈ X ∧ b ∈ B ∧ Rl f u b := hX'
    by_cases hne : ∃ u, u ∈ X'
    · obtain ⟨u₁, hu₁⟩ := hne
      obtain ⟨u₀, hu₀X', -, hmin⟩ := ee_wf X' ⟨u₁, hu₁, ((hX'' u₁).mp hu₁).1.1⟩
      obtain ⟨hu₀α, b₀, hb₀X, hb₀B, hfb₀⟩ := (hX'' u₀).mp hu₀X'
      refine ⟨b₀, hb₀X, fun b hbX hbb₀ => ?_⟩
      rcases (hr' b b₀).mp hbb₀ with ⟨hbB, -, u, u', huu', hu'α, hfu, hfu'⟩ | ⟨hb₀t, -, -⟩
      · have e : u' = u₀ := hf2 u' u₀ b₀ hu'α hu₀α hfu' hfb₀
        rw [e] at huu' hu'α
        exact hmin u ((hX'' u).mpr ⟨hα.2.1 u₀ u hu'α huu', b, hbX, hbB, hfu⟩) huu'
      · rw [hb₀t] at hb₀B
        exact htB hb₀B
    · refine ⟨c₀, hc₀, fun b hbX hbc => ?_⟩
      rcases (hr' b c₀).mp hbc with ⟨hbB, -, u, u', huu', hu'α, hfu, -⟩ | ⟨-, hbB, u, huα, hfu⟩
      · exact hne ⟨u, (hX'' u).mpr ⟨hα.2.1 u' u hu'α huu', b, hbX, hbB, hfu⟩⟩
      · exact hne ⟨u, (hX'' u).mpr ⟨huα, b, hbX, hbB, hfu⟩⟩
  -- the bisimulation between `(g, α)` and `(r, t)`
  obtain ⟨F, hF⟩ := exists_rel 6 (((eeD.comp (τ' := ![6, 6, 6, 7, 9, 6]) ![0, 2] 0).and
    ((SDef.mem 1 3).and (rlD.comp ![4, 0, 1] 6))).or ((SDef.eq 0 2).and (SDef.eq 1 5)))
    ![α, B, f, t]
  have hF' : ∀ a a', Rl F a a' ↔ (EE a α ∧ a' ∈ B ∧ Rl f a a') ∨ (a = α ∧ a' = t) := hF
  have hbis : IsBis F g r := by
    intro a a' haa'
    rcases (hF' a a').mp haa' with ⟨haα, ha'B, hfa⟩ | ⟨ha, ha'⟩
    · refine ⟨fun v hv => ?_, fun b' hb' => ?_⟩
      · have hva : EE v a := (rl_eg hg v a).mp hv
        have hvα : EE v α := hα.2.1 a v haα hva
        obtain ⟨b', hb'B, hfv⟩ := hf1 v hvα
        exact ⟨b', (hr' b' a').mpr (Or.inl ⟨hb'B, ha'B, v, a, hva, haα, hfv, hfa⟩),
          (hF' v b').mpr (Or.inl ⟨hvα, hb'B, hfv⟩)⟩
      · rcases (hr' b' a').mp hb' with ⟨hb'B, -, u, u', huu', hu'α, hfu, hfu'⟩ | ⟨ha't, -, -⟩
        · have e : u' = a := hf2 u' a a' hu'α haα hfu' hfa
          rw [e] at huu' hu'α
          exact ⟨u, (rl_eg hg u a).mpr huu', (hF' u b').mpr
            (Or.inl ⟨hα.2.1 a u hu'α huu', hb'B, hfu⟩)⟩
        · rw [ha't] at ha'B
          exact (htB ha'B).elim
    · rw [ha, ha']
      refine ⟨fun v hv => ?_, fun b' hb' => ?_⟩
      · have hvα : EE v α := (rl_eg hg v α).mp hv
        obtain ⟨b', hb'B, hfv⟩ := hf1 v hvα
        exact ⟨b', (hr' b' t).mpr (Or.inr ⟨rfl, hb'B, v, hvα, hfv⟩),
          (hF' v b').mpr (Or.inl ⟨hvα, hb'B, hfv⟩)⟩
      · rcases (hr' b' t).mp hb' with ⟨-, htB', -⟩ | ⟨-, hb'B, u, huα, hfu⟩
        · exact (htB htB').elim
        · exact ⟨u, (rl_eg hg u α).mpr huα, (hF' u b').mpr (Or.inl ⟨huα, hb'B, hfu⟩)⟩
  obtain ⟨y, hy⟩ := exists_type g α
  have hyr : IsType y r t := isType_of_bis hy ⟨F, hbis, (hF' α t).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  have hyfix : Fixed g y := fixed_of_nodes hg hwf hyr htfix fun a b hab => by
    rcases (hr' a b).mp hab with ⟨haB, -⟩ | ⟨-, haB, -⟩
    · exact hB a haB
    · exact hB a haB
  have e : y = α := theta_inj hg hyfix hy (theta_inZ hg hy) hα.1
  rw [e] at hy
  exact hy

/-- **Hartogs' set of a set of fixed types does not map one-to-one into it.** -/
theorem hart_no_inj {g B H : V} (hg : IsEg g) (hB : ∀ b, b ∈ B → Fixed g b)
    (hH : ∀ α, α ∈ H ↔ InH B α) :
    ¬ ∃ f : V, (∀ u, u ∈ H → ∃ b, b ∈ B ∧ Rl f u b) ∧
      ∀ u u' b, u ∈ H → u' ∈ H → Rl f u b → Rl f u' b → u = u' := by
  rintro ⟨f, h1, h2⟩
  have hfix : ∀ s, s ∈ H → Fixed g s := fun s hs => hart_fixed hg hB ((hH s).mp hs)
  obtain ⟨η, hηZ, -, hη⟩ := exists_type_of_fixed hg hfix
  have hηo : IsOrd η := ⟨hηZ,
    fun u v hu hv => (hη v).mpr ((hH v).mpr (hart_down ((hH u).mp ((hη u).mp hu)) hv)),
    fun u v hu hv => ord_tri hg ((hH u).mp ((hη u).mp hu)).1 ((hH v).mp ((hη v).mp hv)).1
      fun w hw => hart_fixed hg hB (hart_down ((hH u).mp ((hη u).mp hu)) hw)⟩
  have : InH B η := ⟨hηo, f, fun u hu => h1 u ((hη u).mp hu),
    fun u u' b hu hu' => h2 u u' b ((hη u).mp hu) ((hη u').mp hu')⟩
  exact ee_irrefl ((hη η).mpr ((hH η).mpr this))

/-- The finite ordinals belong to Hartogs' set of every set that contains them. -/
theorem om_inH {B n : V} (hΩ : ∀ k, InOm k → k ∈ B) (hn : InOm n) : InH B n := by
  obtain ⟨f, hf⟩ := exists_rel 6 (SDef.eq (τ := ![6, 6]) 0 1) (![] : Fin 0 → V)
  have hf' : ∀ u b, Rl f u b ↔ u = b := hf
  exact ⟨om_isOrd n hn, f, fun u hu => ⟨u, hΩ u (om_trans hn hu), (hf' u u).mpr rfl⟩,
    fun u u' b _ _ h h' => ((hf' u b).mp h).trans ((hf' u' b).mp h').symm⟩

/-- **Hartogs' set has no last element**, for a set of fixed types that contains the finite
ordinals: shift the map by the successor on the finite ordinals and send `α` to zero. -/
theorem hart_next {g B α : V} (hg : IsEg g) (hB : ∀ b, b ∈ B → Fixed g b)
    (hΩ : ∀ k, InOm k → k ∈ B) (h : InH B α) : ∃ c, InH B c ∧ EE α c := by
  have hαfix : Fixed g α := hart_fixed hg hB h
  have hdown : ∀ u, EE u α → Fixed g u := fun u hu => hart_fixed hg hB (hart_down h hu)
  obtain ⟨hα, f, hf1, hf2⟩ := h
  obtain ⟨S, hS⟩ := ((eeD.comp (τ' := ![6, 6]) ![0, 1] 0).or
    (SDef.eq 0 1)).comprehensionU ![α]
  have hS' : ∀ u, u ∈ S ↔ EE u α ∨ u = α := hS
  obtain ⟨c, hcZ, -, hc⟩ := exists_type_of_fixed hg (S := S) fun s hs => by
    rcases (hS' s).mp hs with h | h
    · exact hdown s h
    · rw [h]; exact hαfix
  have hc' : ∀ v, EE v c ↔ EE v α ∨ v = α := fun v => (hc v).trans (hS' v)
  have hco : IsOrd c := by
    refine ⟨hcZ, fun u v hu hv => ?_, fun u v hu hv => ?_⟩
    · rcases (hc' u).mp hu with h | h
      · exact (hc' v).mpr (Or.inl (hα.2.1 u v h hv))
      · rw [h] at hv
        exact (hc' v).mpr (Or.inl hv)
    · rcases (hc' u).mp hu with h | h
      · rcases (hc' v).mp hv with h' | h'
        · exact hα.2.2 u v h h'
        · rw [← h'] at h
          exact Or.inr (Or.inl h)
      · rcases (hc' v).mp hv with h' | h'
        · rw [← h] at h'
          exact Or.inr (Or.inr h')
        · exact Or.inl (h.trans h'.symm)
  obtain ⟨f', hf'⟩ := exists_rel 6 (((eeD.comp (τ' := ![6, 6, 6, 7, 9]) ![0, 2] 0).and
    (SDef.ex 6 ((SDef.mem 0 4).and ((rlD.comp ![5, 1, 0] 6).and
      (((inOmD.comp ![0] 0).and (succD.comp ![0, 2] 0)).or
        ((inOmD.comp ![0] 0).not.and (SDef.eq 2 0))))))).or
    ((SDef.eq 0 2).and (isZeroD.comp ![1] 0))) ![α, B, f]
  have hf'' : ∀ u d, Rl f' u d ↔
      (EE u α ∧ ∃ b, b ∈ B ∧ Rl f u b ∧ ((InOm b ∧ Succ b d) ∨ (¬ InOm b ∧ d = b))) ∨
      (u = α ∧ IsZero d) := hf'
  refine ⟨c, ⟨hco, f', fun u hu => ?_, fun u u' d _ _ hud hu'd => ?_⟩, (hc' α).mpr (Or.inr rfl)⟩
  · rcases (hc' u).mp hu with huα | huα
    · obtain ⟨b, hbB, hfu⟩ := hf1 u huα
      by_cases hbo : InOm b
      · obtain ⟨d, hsd, hdo⟩ := om_succ_exists hbo
        exact ⟨d, hΩ d hdo, (hf'' u d).mpr (Or.inl ⟨huα, b, hbB, hfu, Or.inl ⟨hbo, hsd⟩⟩)⟩
      · exact ⟨b, hbB, (hf'' u b).mpr (Or.inl ⟨huα, b, hbB, hfu, Or.inr ⟨hbo, rfl⟩⟩)⟩
    · obtain ⟨o, ho⟩ := exists_zero (V := V)
      exact ⟨o, hΩ o (om_zero ho), (hf'' u o).mpr (Or.inr ⟨huα, ho⟩)⟩
  · have hnz : ∀ b, (InOm b ∧ Succ b d) ∨ (¬ InOm b ∧ d = b) → ¬ IsZero d := by
      rintro b (⟨-, hs⟩ | ⟨hbo, hdb⟩) hz
      · exact hz.2 b ((hs.2.2 b).mpr (Or.inr rfl))
      · rw [hdb] at hz
        exact hbo (om_zero hz)
    rcases (hf'' u d).mp hud with ⟨huα, b, -, hfu, hb⟩ | ⟨hu, hz⟩
    · rcases (hf'' u' d).mp hu'd with ⟨hu'α, b', -, hfu', hb'⟩ | ⟨-, hz⟩
      · have e : b = b' := by
          rcases hb with ⟨hbo, hs⟩ | ⟨hbo, hdb⟩
          · rcases hb' with ⟨-, hs'⟩ | ⟨hbo', hdb'⟩
            · exact succ_inj' hs hs'
            · rw [← hdb'] at hbo'
              exact (hbo' (om_succ hbo hs)).elim
          · rcases hb' with ⟨hbo', hs'⟩ | ⟨-, hdb'⟩
            · rw [← hdb] at hbo
              exact (hbo (om_succ hbo' hs')).elim
            · exact hdb.symm.trans hdb'
        rw [← e] at hfu'
        exact hf2 u u' b huα hu'α hfu hfu'
      · exact (hnz b hb hz).elim
    · rcases (hf'' u' d).mp hu'd with ⟨-, b', -, -, hb'⟩ | ⟨hu', -⟩
      · exact (hnz b' hb' hz).elim
      · exact hu.trans hu'.symm

/-- **Hartogs' set, with membership restricted to it, is an index set for levels.** -/
theorem hart_idxOK {g B H RH : V} (hg : IsEg g) (hB : ∀ b, b ∈ B → Fixed g b)
    (hΩ : ∀ k, InOm k → k ∈ B) (hH : ∀ α, α ∈ H ↔ InH B α)
    (hRH : ∀ b a, Rl RH b a ↔ b ∈ H ∧ a ∈ H ∧ EE b a) : IdxOK g H RH where
  fixed a ha := hart_fixed hg hB ((hH a).mp ha)
  wf := by
    intro X hX
    obtain ⟨c, hc, hmin⟩ := wf_eg hg X hX
    exact ⟨c, hc, fun b hb hbc => hmin b hb ((rl_eg hg b c).mpr ((hRH b c).mp hbc).2.2)⟩
  trans a b c hab hbc := by
    obtain ⟨haH, -, hab'⟩ := (hRH a b).mp hab
    obtain ⟨-, hcH, hbc'⟩ := (hRH b c).mp hbc
    exact (hRH a c).mpr ⟨haH, hcH, ((hH c).mp hcH).1.2.1 b a hbc' hab'⟩
  dir a b ha hb := by
    rcases ord_tri hg ((hH a).mp ha).1 ((hH b).mp hb).1
        (fun u hu => hart_fixed hg hB (hart_down ((hH a).mp ha) hu)) with h | h | h
    · exact ⟨b, hb, Or.inl h, Or.inl rfl⟩
    · exact ⟨b, hb, Or.inr ((hRH a b).mpr ⟨ha, hb, h⟩), Or.inl rfl⟩
    · exact ⟨a, ha, Or.inl rfl, Or.inr ((hRH b a).mpr ⟨hb, ha, h⟩)⟩
  next a ha := by
    obtain ⟨c, hc, hac⟩ := hart_next hg hB hΩ ((hH a).mp ha)
    exact ⟨c, (hH c).mpr hc, (hRH a c).mpr ⟨ha, (hH c).mpr hc, hac⟩⟩
  nonempty := by
    obtain ⟨o, ho⟩ := exists_zero (V := V)
    exact ⟨o, (hH o).mpr (om_inH hΩ (om_zero ho))⟩

theorem exists_RH (H : V) : ∃ RH : V, ∀ b a, Rl RH b a ↔ b ∈ H ∧ a ∈ H ∧ EE b a :=
  exists_rel 6 ((SDef.mem (τ := ![6, 6, 7]) 0 2).and ((SDef.mem 1 2).and
    (eeD.comp ![0, 1] 0))) ![H]

end model

end HinU

end FFL.FirstOrder.SetTheory
