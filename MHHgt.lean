module

public import MHPow

@[expose] public section

set_option autoImplicit false

/-!
# The full height of a set

In a model of `𝗠𝗛`. For a set `S`:

* `HgtV S κ`: `κ` is the least ordinal whose level of the constructible sets does not map
  one-to-one into `S` (by a relation of the model). It exists (`hgtV_exists`, by Hartogs'
  theorem `next_exists`), and it is a limit ordinal above `ω` when `S` has the empty set as a
  member, is closed under pairs, and the level at `ω` maps one-to-one into it (`BaseS`,
  `hgtV_lim`, by `vinj_succ`).
* `HgtF S μ`: `μ` is the next height after that `κ`. It exists and is unique, it is full
  (`hgtF_full`, by `lnext_sub`), and its level does not map one-to-one into `S` (`hgtF_not`).
* `Far S T`: there is a set `M` such that every set of relations on `S` is a member of `M` and
  every set of relations on `M` is a member of `T`. Then the level at the full height of `S`
  maps one-to-one into `T` (`hgtF_far`, two uses of `vinj_lim`), so **the full height of `S` is
  below the full height of `T`** (`hgtF_lt`).

So a sequence of sets each far above the earlier ones gives a strictly increasing sequence of
full heights, with no recursion: the height is a function of the set.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- Bounded form of "the level at `κ` does not map one-to-one into `S`": `Fh` is the sequence
of the levels, `LL` a set with the level as a member, `P` a set with the relations as
members. -/
def NoInjAt {V : Type} [SetStructure V] (κ Fh LL P S : V) : Prop :=
  ∃ A, A ∈ LL ∧ (LevAt Fh κ A ∧ ¬∃ F, F ∈ P ∧ InjV F A S)

def noInjAtB : BDef (k := 5) (fun V _ v ↦ NoInjAt (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 ((levAtB.comp ![2, 1, 0]).and
    (BDef.bex 4 (injVB.comp ![0, 1, 6])).not)).congr fun _ _ _ => Iff.rfl

section hgt

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- A one-to-one relation can be taken as a set of pairs from `A` and `S`. -/
theorem vinj_trim {A S : V} (h : VInj A S) : ∃ F : V, F ∈ ℘ (prodS A S) ∧ InjV F A S := by
  obtain ⟨F, hF⟩ := h
  let F' : V := sepB (k := 1) (BDef.mem 0 1) (prodS A S) ![F]
  have hF'z : ∀ z, z ∈ F' ↔ z ∈ prodS A S ∧ z ∈ F := fun z => mem_sepB _ _ _ z
  refine ⟨F', mem_power_iff.mpr fun z hz => ((hF'z z).mp hz).1, fun u hu => ?_,
    fun u hu u' hu' v _ h1 h2 => ?_⟩
  · obtain ⟨v, hv, hr⟩ := hF.1 u hu
    exact ⟨v, hv, pr_iff.mpr ((hF'z _).mpr ⟨mem_prodS.mpr ⟨u, hu, v, hv, rfl⟩,
      hin_rl_iff.mp hr⟩)⟩
  · exact hF.2 u u' v hu hu' (hin_rl_iff.mpr ((hF'z _).mp (pr_iff.mp h1)).2)
      (hin_rl_iff.mpr ((hF'z _).mp (pr_iff.mp h2)).2)

theorem vinj_of_injV {F A S : V} (h : InjV F A S) : VInj A S := by
  let F' : V := sepB (k := 1) (BDef.mem 0 1) (prodS A S) ![F]
  have hF'z : ∀ z, z ∈ F' ↔ z ∈ prodS A S ∧ z ∈ F := fun z => mem_sepB _ _ _ z
  refine ⟨F', fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
  · obtain ⟨v, hv, hr⟩ := h.1 u hu
    exact ⟨v, hv, hin_rl_iff.mpr ((hF'z _).mpr ⟨mem_prodS.mpr ⟨u, hu, v, hv, rfl⟩,
      pr_iff.mp hr⟩)⟩
  · obtain ⟨k1, k2⟩ := (hF'z _).mp (hin_rl_iff.mp h1)
    obtain ⟨-, k2'⟩ := (hF'z _).mp (hin_rl_iff.mp h2)
    obtain ⟨a, -, b, hb, e⟩ := mem_prodS.mp k1
    obtain ⟨-, e2⟩ := kp_inj e
    rw [← e2] at hb
    exact h.2 u hu u' hu' v hb (pr_iff.mpr k2) (pr_iff.mpr k2')

/-- `κ` is the least ordinal whose level does not map one-to-one into `S`. -/
def HgtV (S κ : V) : Prop := Ord κ ∧ ¬VInj (Lev κ) S ∧ ∀ δ, δ ∈ κ → VInj (Lev δ) S

theorem hgtV_exists (S : V) : ∃ κ : V, HgtV S κ := by
  obtain ⟨K, hK⟩ := next_exists S
  have hKO : Ord K := ord_of_ordS hK.1
  obtain ⟨lam, hl, hKl⟩ := exists_lim hKO
  have hno : ¬VInj (Lev lam) S := fun h => hK.2.1
    (vinj_dom_mono h fun ξ hξ => ord_mem_lev_lim hl ξ (hl.1.1 K hKl ξ hξ))
  obtain ⟨Fh, hFh⟩ := exists_hier hl.1
  have hscO : Ord (sc lam) := ord_sc hl.1
  let P : V := ℘ (prodS (Lev lam) S)
  let LL : V := Lev (sc lam)
  let Zs : V := sepB (k := 4) noInjAtB (sc lam) ![Fh, LL, P, S]
  have hZs : ∀ κ, κ ∈ Zs ↔ κ ∈ sc lam ∧ NoInjAt κ Fh LL P S := fun κ => mem_sepB _ _ _ κ
  have hchar : ∀ κ, κ ∈ sc lam → (NoInjAt κ Fh LL P S ↔ ¬VInj (Lev κ) S) := by
    intro κ hκ
    have hκO := ord_mem hscO hκ
    have hsub : ∀ x, x ∈ Lev κ → x ∈ Lev lam := lev_sub_of_le hκO hl.1 (mem_sc.mp hκ)
    constructor
    · rintro ⟨A, -, hA, hn⟩ hv
      have eA : A = Lev κ := (levAt_lev hl.1 hFh hκ).mp hA
      rw [eA] at hn
      obtain ⟨F, hFP, hF⟩ := vinj_trim hv
      refine hn ⟨F, mem_power_iff.mpr fun z hz => ?_, hF⟩
      obtain ⟨u, hu, v, hv', e⟩ := mem_prodS.mp (mem_power_iff.mp hFP z hz)
      exact mem_prodS.mpr ⟨u, hsub u hu, v, hv', e⟩
    · intro hn
      refine ⟨Lev κ, lev_mem hscO hκ, (levAt_lev hl.1 hFh hκ).mpr rfl, ?_⟩
      rintro ⟨F, -, hF⟩
      exact hn (vinj_of_injV hF)
  have hne : ∃ z, z ∈ Zs :=
    ⟨lam, (hZs lam).mpr ⟨self_mem_sc lam, (hchar lam (self_mem_sc lam)).mpr hno⟩⟩
  obtain ⟨κ, hκ, hmin⟩ := ord_least Zs (fun z hz => ord_mem hscO ((hZs z).mp hz).1) hne
  have hκs := ((hZs κ).mp hκ).1
  refine ⟨κ, ord_mem hscO hκs, (hchar κ hκs).mp ((hZs κ).mp hκ).2, fun δ hδ => ?_⟩
  by_contra hn
  have hδs : δ ∈ sc lam := hscO.1 κ hκs δ hδ
  rcases hmin δ ((hZs δ).mpr ⟨hδs, (hchar δ hδs).mpr hn⟩) with e | e
  · rw [e] at hδ
    exact mem_irrefl _ hδ
  · exact mem_asymm hδ e

theorem hgtV_unique {S κ κ' : V} (h : HgtV S κ) (h' : HgtV S κ') : κ = κ' := by
  rcases ord_tri h.1 h'.1 with e | e | e
  · exact absurd (h'.2.2 κ e) h.2.1
  · exact e
  · exact absurd (h.2.2 κ' e) h'.2.1

/-- The conditions of the first proof that a height is a limit ordinal above `ω`: `S` is closed
under pairs, has the empty set as a member, and the level at `ω` maps one-to-one into it. -/
structure BaseP (S : V) : Prop where
  pair : ∀ a b : V, a ∈ S → b ∈ S → kp a b ∈ S
  emp : (∅ : V) ∈ S
  om : VInj (Lev (om : V)) S

theorem hgtV_lim_p {S κ : V} (hS : BaseP S) (h : HgtV S κ) : Lim κ ∧ (om : V) ∈ κ := by
  have homκ : (om : V) ∈ κ := by
    rcases ord_tri (ord_om (V := V)) h.1 with e | e | e
    · exact e
    · exact absurd (e ▸ hS.om) h.2.1
    · exact absurd (vinj_dom_mono hS.om (lev_mono ord_om e)) h.2.1
  rcases ord_cases h.1 with e | ⟨η, hη, e⟩ | hl
  · rw [e] at homκ
    exact absurd homκ (by simp)
  · exfalso
    have hbig : Big η := ⟨ord_mem h.1 hη, fun n hn => by
      rw [e] at homκ
      rcases mem_sc.mp homκ with e' | e'
      · rw [← e']
        exact hn
      · exact (ord_mem h.1 hη).1 om e' n hn⟩
    have := vinj_succ hS.pair hS.emp hbig (h.2.2 η hη)
    rw [← e] at this
    exact h.2.1 this
  · exact ⟨hl, homκ⟩

/-! ### The height of any set into which the level at `ω` maps one-to-one is a limit

The closure under pairs is not needed. The level after an infinite ordinal `δ` maps one-to-one
into the level at the greatest limit ordinal `λ ≤ δ`: that level is closed under pairs, so its
height is a limit ordinal, and it is above `δ`. -/

theorem kp_mem_lev_ne {γ a b : V} (hγ : Ord γ) (hne : ∃ z, z ∈ γ) (ha : a ∈ Lev γ)
    (hb : b ∈ Lev γ) : kp a b ∈ Lev (scn 4 γ) := by
  have h0 := empty_mem_lev hγ hne
  have o1 : Ord (scn 1 γ) := ord_sc hγ
  have o2 : Ord (scn 2 γ) := ord_sc o1
  have o3 : Ord (scn 3 γ) := ord_sc o2
  have n1 : ∃ z, z ∈ scn 1 γ := ⟨γ, self_mem_sc γ⟩
  have n2 : ∃ z, z ∈ scn 2 γ := ⟨scn 1 γ, self_mem_sc _⟩
  have n3 : ∃ z, z ∈ scn 3 γ := ⟨scn 2 γ, self_mem_sc _⟩
  have s1 : ({a} : V) ∈ Lev (scn 1 γ) := insert_empty a ▸ adj_mem_lev hγ hne h0 ha
  have s2 : ({b} : V) ∈ Lev (scn 1 γ) := insert_empty b ▸ adj_mem_lev hγ hne h0 hb
  have s3 : ({a, b} : V) ∈ Lev (scn 2 γ) := adj_mem_lev o1 n1 s2 (lev_scn_sub hγ 1 a ha)
  have s4 : ({{a, b}} : V) ∈ Lev (scn 3 γ) :=
    insert_empty ({a, b} : V) ▸ adj_mem_lev o2 n2 (empty_mem_lev o2 n2) s3
  exact adj_mem_lev o3 n3 s4 (lev_scn_sub o1 2 _ s1)

/-- A member of the level at `ω` is a member of the level at a finite ordinal. -/
theorem lev_om_exists {a : V} (ha : a ∈ Lev (om : V)) : ∃ n, n ∈ (om : V) ∧ a ∈ Lev n := by
  obtain ⟨β, hβ, hin⟩ := (mem_lev ord_om).mp ha
  exact ⟨sc β, sc_mem_om hβ, inDef_mem (ord_mem ord_om hβ) hin⟩

/-- **The level at `ω` is closed under pairs.** -/
theorem kp_mem_lev_om {a b : V} (ha : a ∈ Lev (om : V)) (hb : b ∈ Lev (om : V)) :
    kp a b ∈ Lev (om : V) := by
  obtain ⟨n, hn, han⟩ := lev_om_exists ha
  obtain ⟨m, hm, hbm⟩ := lev_om_exists hb
  have hnO := ord_mem (ord_om (V := V)) hn
  have hmO := ord_mem (ord_om (V := V)) hm
  have key : ∀ γ, γ ∈ (om : V) → a ∈ Lev γ → b ∈ Lev γ → kp a b ∈ Lev (om : V) := by
    intro γ hγ h1 h2
    have hγO := ord_mem (ord_om (V := V)) hγ
    have hs : sc γ ∈ (om : V) := sc_mem_om hγ
    have h4 : scn 4 (sc γ) ∈ (om : V) := sc_mem_om (sc_mem_om (sc_mem_om (sc_mem_om hs)))
    exact lev_mono ord_om h4 _ (kp_mem_lev_ne (ord_sc hγO) ⟨γ, self_mem_sc γ⟩
      (lev_mono (ord_sc hγO) (self_mem_sc γ) a h1) (lev_mono (ord_sc hγO) (self_mem_sc γ) b h2))
  rcases ord_tri hnO hmO with e | e | e
  · exact key m hm (lev_mono hmO e a han) hbm
  · exact key m hm (e ▸ han) hbm
  · exact key n hn han (lev_mono hnO e b hbm)

/-- A limit ordinal is not below `ω`. -/
theorem om_le_lim {lam : V} (hl : Lim lam) : (om : V) = lam ∨ (om : V) ∈ lam := by
  rcases ord_tri (ord_om (V := V)) hl.1 with e | e | e
  · exact Or.inr e
  · exact Or.inl e
  · exfalso
    rcases om_cases e with h0 | ⟨m, -, hm⟩
    · obtain ⟨z, hz⟩ := hl.2.1
      rw [h0] at hz
      exact absurd hz (by simp)
    · have h1 : m ∈ lam := by
        rw [hm]
        exact self_mem_sc m
      have h2 := hl.2.2 m h1
      rw [← hm] at h2
      exact mem_irrefl _ h2

/-- The level at a limit ordinal satisfies the conditions `BaseP`. -/
theorem baseP_lev {lam : V} (hl : Lim lam) : BaseP (Lev lam) := by
  have hom := om_le_lim hl
  refine ⟨fun a b ha hb => ?_, empty_mem_lev hl.1 hl.2.1,
    vinj_of_sub (lev_sub_of_le ord_om hl.1 hom)⟩
  rcases hom with e | e
  · rw [← e] at ha hb ⊢
    exact kp_mem_lev_om ha hb
  · exact kp_mem_lev_lim hl e ha hb

/-- **The greatest limit ordinal below or equal to an infinite ordinal.** -/
theorem exists_lim_below {δ : V} (hδ : Ord δ) (hom : (om : V) = δ ∨ (om : V) ∈ δ) :
    ∃ lam, Lim lam ∧ (lam = δ ∨ lam ∈ δ) ∧
      ∀ μ, Lim μ → lam ∈ μ → ¬ (μ = δ ∨ μ ∈ δ) := by
  have hscO : Ord (sc δ) := ord_sc hδ
  let Z : V := sepB (k := 1)
    (BDef.ball 1 ((BDef.mem 1 0).imp (BDef.bex 2 (succB.comp ![1, 0])))) (sc δ) ![sc δ]
  have hZ : ∀ γ, γ ∈ Z ↔ γ ∈ sc δ ∧ ∀ ξ, ξ ∈ sc δ → (γ ∈ ξ → ∃ η, η ∈ sc δ ∧ SuccR ξ η) :=
    fun γ => mem_sepB _ _ _ γ
  have hδZ : δ ∈ Z := (hZ δ).mpr ⟨self_mem_sc δ, fun ξ hξ hδξ => by
    rcases mem_sc.mp hξ with e | e
    · rw [e] at hδξ
      exact (mem_irrefl _ hδξ).elim
    · exact (mem_asymm hδξ e).elim⟩
  obtain ⟨γ₀, hγ₀, hmin⟩ := ord_least Z (fun z hz => ord_mem hscO ((hZ z).mp hz).1) ⟨δ, hδZ⟩
  obtain ⟨hγs, hγall⟩ := (hZ γ₀).mp hγ₀
  have hγO := ord_mem hscO hγs
  rcases ord_cases hγO with e | ⟨η₀, hη₀, e⟩ | hl
  · exfalso
    obtain ⟨η, -, hs⟩ := hγall om (mem_sc.mpr hom) (e ▸ empty_mem_om)
    have hs' : (om : V) = sc η := succR_iff_sc.mp hs
    have h1 : η ∈ (om : V) := by
      rw [hs']
      exact self_mem_sc η
    have h2 := sc_mem_om h1
    rw [← hs'] at h2
    exact mem_irrefl _ h2
  · exfalso
    have hη₀s : η₀ ∈ sc δ := hscO.1 γ₀ hγs η₀ hη₀
    have hη₀Z : η₀ ∈ Z := (hZ η₀).mpr ⟨hη₀s, fun ξ hξ hηξ => by
      rcases ord_tri hγO (ord_mem hscO hξ) with k | k | k
      · exact hγall ξ hξ k
      · exact ⟨η₀, hη₀s, succR_iff_sc.mpr (k ▸ e)⟩
      · rw [e] at k
        rcases mem_sc.mp k with k' | k'
        · rw [k'] at hηξ
          exact (mem_irrefl _ hηξ).elim
        · exact (mem_asymm hηξ k').elim⟩
    rcases hmin η₀ hη₀Z with k | k
    · rw [k] at hη₀
      exact mem_irrefl _ hη₀
    · exact mem_asymm hη₀ k
  · refine ⟨γ₀, hl, mem_sc.mp hγs, fun μ hμ hγμ hμδ => ?_⟩
    obtain ⟨η, -, hs⟩ := hγall μ (mem_sc.mpr hμδ) hγμ
    have hs' : μ = sc η := succR_iff_sc.mp hs
    have h1 : η ∈ μ := by
      rw [hs']
      exact self_mem_sc η
    have h2 := hμ.2.2 η h1
    rw [← hs'] at h2
    exact mem_irrefl _ h2

/-- **The level after an infinite ordinal `δ` maps one-to-one into the level at a limit ordinal
below or equal to `δ`.** -/
theorem vinj_sc_lim {δ : V} (hδ : Ord δ) (hom : (om : V) = δ ∨ (om : V) ∈ δ) :
    ∃ lam, Lim lam ∧ (lam = δ ∨ lam ∈ δ) ∧ VInj (Lev (sc δ)) (Lev lam) := by
  obtain ⟨lam, hl, hle, hno⟩ := exists_lim_below hδ hom
  obtain ⟨κ, hκ⟩ := hgtV_exists (Lev lam)
  obtain ⟨hκl, -⟩ := hgtV_lim_p (baseP_lev hl) hκ
  have hlamκ : lam ∈ κ := by
    rcases ord_tri hl.1 hκ.1 with k | k | k
    · exact k
    · exact absurd (vinj_of_sub (k ▸ fun z hz => hz)) hκ.2.1
    · exact absurd (vinj_of_sub (lev_mono hl.1 k)) hκ.2.1
  refine ⟨lam, hl, hle, ?_⟩
  rcases ord_tri (ord_sc hδ) hκ.1 with k | k | k
  · exact hκ.2.2 _ k
  · exfalso
    have h1 : δ ∈ κ := by
      rw [← k]
      exact self_mem_sc δ
    have h2 := hκl.2.2 δ h1
    rw [← k] at h2
    exact mem_irrefl _ h2
  · exact (hno κ hκl hlamκ (mem_sc.mp k)).elim

/-- The condition on `S` under which its height is a limit ordinal above `ω`: the level at `ω`
maps one-to-one into `S`. -/
structure BaseS (S : V) : Prop where
  om : VInj (Lev (om : V)) S

theorem BaseP.base {S : V} (h : BaseP S) : BaseS S := ⟨h.om⟩

theorem hgtV_lim {S κ : V} (hS : BaseS S) (h : HgtV S κ) : Lim κ ∧ (om : V) ∈ κ := by
  have homκ : (om : V) ∈ κ := by
    rcases ord_tri (ord_om (V := V)) h.1 with e | e | e
    · exact e
    · exact absurd (e ▸ hS.om) h.2.1
    · exact absurd (vinj_dom_mono hS.om (lev_mono ord_om e)) h.2.1
  rcases ord_cases h.1 with e | ⟨η, hη, e⟩ | hl
  · rw [e] at homκ
    exact absurd homκ (by simp)
  · exfalso
    have hηO := ord_mem h.1 hη
    have homη : (om : V) = η ∨ (om : V) ∈ η := by
      rw [e] at homκ
      exact mem_sc.mp homκ
    obtain ⟨lam, hl, hle, hv⟩ := vinj_sc_lim hηO homη
    have h1 : VInj (Lev lam) S := vinj_dom_mono (h.2.2 η hη) (lev_sub_of_le hl.1 hηO hle)
    have h2 := vinj_comp hv h1
    rw [← e] at h2
    exact h.2.1 h2
  · exact ⟨hl, homκ⟩

/-- Every set of relations on `S` is a member of `T`. -/
def SupRel (S T : V) : Prop :=
  ∀ C : V, (∀ w, w ∈ C → ∀ p, p ∈ w → p ∈ prodS S S) → C ∈ T

/-- `T` is far above `S`: two steps of `SupRel`. -/
def Far (S T : V) : Prop := ∃ M : V, SupRel S M ∧ SupRel M T

/-- `μ` is the full height of `S`: the next height after the least ordinal whose level does
not map one-to-one into `S`. -/
def HgtF (S μ : V) : Prop :=
  ∃ κ : V, HgtV S κ ∧ Lim μ ∧ κ ∈ μ ∧ ¬LInj (Lev μ) (Lev κ) ∧ ∀ δ, δ ∈ μ → LInj (Lev δ) (Lev κ)

theorem hgtF_exists {S : V} (hS : BaseS S) : ∃ μ : V, HgtF S μ := by
  obtain ⟨κ, hκ⟩ := hgtV_exists S
  obtain ⟨hl, hom⟩ := hgtV_lim hS hκ
  obtain ⟨μ, hμ, hκμ, hn, hall⟩ := lnext_spec hl hom
  exact ⟨μ, κ, hκ, hμ, hκμ, hn, hall⟩

theorem hgtF_ord {S μ : V} (h : HgtF S μ) : Ord μ :=
  let ⟨_, _, hμ, _⟩ := h
  hμ.1

/-- **The full height of a set is full.** -/
theorem hgtF_full {S μ : V} (hS : BaseS S) (h : HgtF S μ) : Full μ := by
  obtain ⟨κ, hκ, hμ, hκμ, hn, hall⟩ := h
  obtain ⟨hl, hom⟩ := hgtV_lim hS hκ
  exact full_of_sub hl hom hμ hκμ hn hall (lnext_sub hl hom hμ hκμ hn hall)

/-- The level at the full height of `S` does not map one-to-one into `S`. -/
theorem hgtF_not {S μ : V} (h : HgtF S μ) : ¬VInj (Lev μ) S := by
  obtain ⟨κ, hκ, hμ, hκμ, -, -⟩ := h
  exact fun hv => hκ.2.1 (vinj_dom_mono hv (lev_mono hμ.1 hκμ))

/-- An ordinal whose level maps one-to-one into `S` is below the full height of `S`. -/
theorem hgtF_gt {S μ γ : V} (h : HgtF S μ) (hγ : Ord γ) (hv : VInj (Lev γ) S) : γ ∈ μ := by
  obtain ⟨κ, hκ, hμ, hκμ, -, -⟩ := h
  rcases ord_tri hγ hκ.1 with e | e | e
  · exact hμ.1.1 κ hκμ γ e
  · rw [e]
    exact hκμ
  · exact absurd (vinj_dom_mono hv (lev_mono hγ e)) hκ.2.1

/-- **The level at the full height of `S` maps one-to-one into every set far above `S`.** -/
theorem hgtF_far {S T μ : V} (hS : BaseS S) (h : HgtF S μ) (hf : Far S T) :
    VInj (Lev μ) T := by
  obtain ⟨κ, hκ, hμ, -, -, hall⟩ := h
  obtain ⟨M, h1, h2⟩ := hf
  obtain ⟨hl, -⟩ := hgtV_lim hS hκ
  have a : VInj (Lev κ) M := vinj_lim hl hκ.2.2 h1
  exact vinj_lim hμ (fun δ hδ => vinj_comp (linj_vinj (hall δ hδ)) a) h2

/-- **The full height of `S` is below the full height of every set far above `S`.** -/
theorem hgtF_lt {S T μ μ' : V} (hS : BaseS S) (h : HgtF S μ) (h' : HgtF T μ')
    (hf : Far S T) : μ ∈ μ' :=
  hgtF_gt h' (hgtF_ord h) (hgtF_far hS h hf)

theorem hgtF_unique {S μ μ' : V} (h : HgtF S μ) (h' : HgtF S μ') : μ = μ' := by
  obtain ⟨κ, hκ, hμ, -, hn, hall⟩ := h
  obtain ⟨κ', hκ', hμ', -, hn', hall'⟩ := h'
  have e : κ' = κ := hgtV_unique hκ' hκ
  rw [e] at hn' hall'
  rcases ord_tri hμ.1 hμ'.1 with k | k | k
  · exact absurd (hall' μ k) hn
  · exact k
  · exact absurd (hall μ' k) hn'

end hgt

end MH

end FFL.FirstOrder.SetTheory
