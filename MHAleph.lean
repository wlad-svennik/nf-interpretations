module

public import MHInterpretsMAC
public import AlephTheory

@[expose] public section

set_option autoImplicit false

/-!
# The alephs of the constructible sets of a model of `𝗠𝗛`

In a model of `𝗠𝗛` in which "`ℵₙ` exists" holds for every `n`, the same holds in the structure of
the constructible sets. So `𝗠𝗛𝗔ω`, which is `𝗠𝗛` with those sentences, interprets `𝗠𝗔𝗖𝗔ω`, which is
`𝗠𝗔𝗖` with them. The ordinals found are the cardinals `ℵₙ` of the constructible sets; they are
the heights of the levels that the hosts of `docs/ordinal_towers_2026-11-23.md` are to be.

* `ord_mem_lev_lim`: every member of a limit ordinal `λ` is a member of the level at `λ`.
  `con_ord`: every ordinal is constructible.
* `hin_isOp_iff`, `hin_rl_iff`: the pairs and relations of `AlephTheory.lean` are the Kuratowski
  pairs of `𝗠𝗛`. `ord_of_ordS`, `ordS_of_ord`: `OrdS` is `Ord`. `omegaS_om`: `OmegaS ω`.
* `InjV`: a bounded form of `InjS`. `exists_trim`: the pairs of a constructible relation that
  lie in the product of two constructible sets form a constructible set.
* For a structure `W` embedded onto the constructible sets: `isOp_tr`, `rl_tr`, `injS_tr`,
  `ordS_tr`, `omegaS_of` carry the notions across the embedding.
* `next_tr`: if `a'` is the least ordinal that does not map one-to-one into `a`, and `e` in `W`
  is an ordinal included in `a`, then `W` has a least ordinal that does not map one-to-one into
  `e`, and it is included in `a'`. The constructible maps into `e` from ordinals up to `a'` can
  all be taken in one level (`bound_exists`), which makes the least such ordinal a set.
* `aleph_tr`: if `IsAleph n a`, then `W` has an `e` with `IsAleph n e` and `e ⊆ a`.
* `𝗠𝗛𝗔ω`, `𝗠𝗔𝗖𝗔ω`, and **`mhaInterpretsMACA : 𝗠𝗛𝗔ω ⊳ 𝗠𝗔𝗖𝗔ω`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-- `𝗠𝗛` with "`ℵₙ` exists" for every `n`. -/
abbrev MathiasMHAlephs : SetTheory := 𝗠𝗛 ∪ Set.range Axiom.aleph

@[inherit_doc] notation "𝗠𝗛𝗔ω" => MathiasMHAlephs

/-- `𝗠𝗔𝗖` with "`ℵₙ` exists" for every `n`. -/
abbrev MacLaneAlephs : SetTheory := 𝗠𝗔𝗖 ∪ Set.range Axiom.aleph

@[inherit_doc] notation "𝗠𝗔𝗖𝗔ω" => MacLaneAlephs

instance : 𝗘𝗤 _ ⪯ 𝗠𝗛𝗔ω :=
  let : 𝗘𝗤 _ ⪯ 𝗠𝗛 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

instance : 𝗘𝗤 _ ⪯ 𝗠𝗔𝗖𝗔ω :=
  let : 𝗘𝗤 _ ⪯ 𝗠𝗔𝗖 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

namespace MH

/-- `F` relates every member of `A` to a member of `B`, and no two members of `A` to the same
member of `B`. -/
def InjV {V : Type} [SetStructure V] (F A B : V) : Prop :=
  (∀ u, u ∈ A → ∃ v, v ∈ B ∧ Pr F u v) ∧
  (∀ u, u ∈ A → ∀ u', u' ∈ A → ∀ v, v ∈ B → Pr F u v → Pr F u' v → u = u')

def injVB : BDef (k := 3) (fun V _ v ↦ InjV (v 0) (v 1) (v 2)) :=
  ((BDef.ball 1 (BDef.bex 3 (prB.comp ![2, 1, 0]))).and
    (BDef.ball 1 (BDef.ball 2 (BDef.ball 4 ((prB.comp ![3, 2, 0]).imp
      ((prB.comp ![3, 1, 0]).imp (BDef.eq 2 1))))))).congr fun _ _ _ => Iff.rfl

/-- `z` is a member of `F` and a pair of a member of `A` and a member of `B`. -/
def trimB : BDef (k := 4)
    (fun V _ v ↦ v 0 ∈ v 1 ∧ ∃ u, u ∈ v 2 ∧ ∃ w, w ∈ v 3 ∧ IsOp (v 0) u w) :=
  ((BDef.mem 0 1).and (BDef.bex 2 (BDef.bex 4 (isOpB.comp ![2, 1, 0])))).congr
    fun _ _ _ => Iff.rfl

/-- The relation on `sc a` that copies the order of an ordinal `ξ` along a one-to-one
relation `F` from `ξ` into `a`, with the point `a` above every value. -/
def hartB : BDef (k := 5) (fun V _ v ↦
    ((∃ α, α ∈ v 3 ∧ ∃ β, β ∈ v 3 ∧ (Pr (v 2) α (v 0) ∧ (Pr (v 2) β (v 1) ∧ α ∈ β))) ∧
      (v 0 ∈ v 4 ∧ v 1 ∈ v 4)) ∨
    (v 1 = v 4 ∧ (v 0 ∈ v 4 ∧ ∃ α, α ∈ v 3 ∧ Pr (v 2) α (v 0)))) :=
  (((BDef.bex 3 (BDef.bex 4 ((prB.comp ![4, 1, 2]).and ((prB.comp ![4, 0, 3]).and
    (BDef.mem 1 0))))).and ((BDef.mem 0 4).and (BDef.mem 1 4))).or
    ((BDef.eq 1 4).and ((BDef.mem 0 4).and (BDef.bex 3 (prB.comp ![3, 0, 1]))))).congr
    fun _ _ _ => Iff.rfl

/-! ### The ordinals are constructible -/

section ord

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem lim_big {lam : V} (h : Lim lam) : Big lam := by
  refine ⟨h.1, ?_⟩
  have h0 : (∅ : V) ∈ lam := by
    rcases ord_tri ord_empty h.1 with e | e | e
    · exact e
    · obtain ⟨z, hz⟩ := h.2.1
      rw [← e] at hz
      exact absurd hz (by simp)
    · exact absurd e (by simp)
  exact om_ind (k := 1) (BDef.mem 0 1) ![lam] h0 (fun n _ hn => h.2.2 n hn)

/-- For a limit ordinal `λ`, the members of the level at `λ` form a closed property. -/
theorem closed_lev_lim {lam : V} (h : Lim lam) : Closed (fun a : V ↦ a ∈ Lev lam) := by
  have key : ∀ γ : V, Ord γ → Lev γ ∈ Lev lam → γ ∈ lam := fun γ hγ hl =>
    (rkL_mem (rkL_lev hγ) h.1).mp hl
  exact ⟨fun k => nm_mem_lev (lim_big h) k,
    fun γ hγ hl => lev_mem h.1 (h.2.2 γ (key γ hγ hl)),
    fun γ s y₁ y₂ y₃ x hγ hl hs h₁ h₂ h₃ _ _ _ _ hD =>
      def_mem_lev h.1 (key γ hγ hl) hs h₁ h₂ h₃ hD⟩

theorem ord_cases {ξ : V} (h : Ord ξ) : ξ = ∅ ∨ (∃ η, η ∈ ξ ∧ ξ = sc η) ∨ Lim ξ := by
  by_cases h0 : ∃ z, z ∈ ξ
  · by_cases hs : ∃ η, η ∈ ξ ∧ ξ = sc η
    · exact Or.inr (Or.inl hs)
    · refine Or.inr (Or.inr ⟨h, h0, fun β hβ => ?_⟩)
      rcases ord_sc_le (ord_mem h hβ) h hβ with e | e
      · exact absurd ⟨β, hβ, e.symm⟩ hs
      · exact e
  · exact Or.inl (mem_ext fun z => ⟨fun hz => absurd ⟨z, hz⟩ h0, fun hz => absurd hz (by simp)⟩)

/-- **Every member of a limit ordinal `λ` is a member of the level at `λ`.** By induction on
the member, for all limit ordinals up to `λ` at once: a successor is one operation later, and
a limit ordinal `ξ` is the set of the ordinals of the level at `ξ`, or a member of it. -/
theorem ord_mem_lev_lim {lam : V} (h : Lim lam) : ∀ ξ, ξ ∈ lam → ξ ∈ Lev lam := by
  by_contra hcon
  obtain ⟨ξ₁, hcon⟩ := not_forall.mp hcon
  obtain ⟨hξ₁, hn₁⟩ := Classical.not_imp.mp hcon
  obtain ⟨F, hF⟩ := exists_hier h.1
  let Z : V := sepB (k := 3) (BDef.bex 3 ((BDef.mem 1 0).and
    ((BDef.ball 0 (BDef.bex 1 (succB.comp ![0, 1]))).and
      (BDef.bex 3 ((levAtB.comp ![3, 1, 0]).and (BDef.mem 2 0).not))))) lam
    ![F, Lev (sc lam), sc lam]
  have hZ : ∀ ξ, ξ ∈ Z ↔ ξ ∈ lam ∧ ∃ μ, μ ∈ sc lam ∧ (ξ ∈ μ ∧
      ((∀ b, b ∈ μ → ∃ s, s ∈ μ ∧ SuccR s b) ∧
        ∃ A, A ∈ Lev (sc lam) ∧ (LevAt F μ A ∧ ¬ξ ∈ A))) := fun ξ => mem_sepB _ _ _ ξ
  have hne : ∃ z, z ∈ Z := ⟨ξ₁, (hZ ξ₁).mpr ⟨hξ₁, lam, self_mem_sc lam, hξ₁,
    fun b hb => ⟨sc b, h.2.2 b hb, succR_iff_sc.mpr rfl⟩, Lev lam,
    lev_mem (ord_sc h.1) (self_mem_sc lam), (levAt_lev h.1 hF (self_mem_sc lam)).mpr rfl, hn₁⟩⟩
  obtain ⟨ξ₀, hξ₀Z, hleast⟩ := ord_least Z (fun z hz => ord_mem h.1 ((hZ z).mp hz).1) hne
  obtain ⟨hξ₀, μ, hμ, hξ₀μ, hμs, A, -, hA, hnA⟩ := (hZ ξ₀).mp hξ₀Z
  have hμo : Ord μ := ord_mem (ord_sc h.1) hμ
  have eA : A = Lev μ := (levAt_lev h.1 hF hμ).mp hA
  rw [eA] at hnA
  have hμl : Lim μ := ⟨hμo, ⟨ξ₀, hξ₀μ⟩, fun b hb => by
    obtain ⟨s, hs, e⟩ := hμs b hb
    rw [succR_iff_sc.mp e] at hs
    exact hs⟩
  have hξ₀o : Ord ξ₀ := ord_mem h.1 hξ₀
  have hmin : ∀ ξ', ξ' ∈ ξ₀ → ∀ μ', μ' ∈ sc lam → Lim μ' → ξ' ∈ μ' → ξ' ∈ Lev μ' := by
    intro ξ' hξ' μ' hμ' hl' hξμ'
    by_contra hn
    have hZ' : ξ' ∈ Z := (hZ ξ').mpr ⟨h.1.1 ξ₀ hξ₀ ξ' hξ', μ', hμ', hξμ',
      fun b hb => ⟨sc b, hl'.2.2 b hb, succR_iff_sc.mpr rfl⟩, Lev μ',
      lev_mem (ord_sc h.1) hμ', (levAt_lev h.1 hF hμ').mpr rfl, hn⟩
    rcases hleast ξ' hZ' with e | e
    · rw [e] at hξ'
      exact mem_irrefl _ hξ'
    · exact mem_asymm hξ' e
  rcases ord_cases hξ₀o with e | ⟨η, hη, e⟩ | hl₀
  · exact hnA (by rw [e]; exact empty_mem_lev hμo ⟨ξ₀, hξ₀μ⟩)
  · have hηL : η ∈ Lev μ := hmin η hη μ hμ hμl (hμo.1 ξ₀ hξ₀μ η hη)
    obtain ⟨β, hβ, hin⟩ := (mem_lev hμo).mp hηL
    have hβo : Ord β := ord_mem hμo hβ
    have h1 : η ∈ Lev (sc β) := (mem_lev (ord_sc hβo)).mpr ⟨β, self_mem_sc β, hin⟩
    have h2 : sc η ∈ Lev (sc (sc β)) := adj_mem_lev (ord_sc hβo) ⟨β, self_mem_sc β⟩ h1 h1
    exact hnA (by rw [e]; exact lev_mono hμo (hμl.2.2 _ (hμl.2.2 β hβ)) _ h2)
  · have hsub : ∀ ξ', ξ' ∈ ξ₀ → ξ' ∈ Lev ξ₀ := fun ξ' hξ' =>
      hmin ξ' hξ' ξ₀ (mem_sc.mpr (Or.inr hξ₀)) hl₀ hξ'
    have ht : Good (fun a : V ↦ a ∈ Lev μ) (Lev ξ₀) :=
      ⟨lev_mem hμo hξ₀μ, sc ξ₀, big_sc (lim_big hl₀), lev_mem hμo (hμl.2.2 ξ₀ hξ₀μ),
        lev_mem (ord_sc hξ₀o) (self_mem_sc ξ₀)⟩
    obtain ⟨y, hy, hyz⟩ := sep_good_bdef (closed_lev_lim hμl) (k := 0) ordB ht (lev_tr hξ₀o)
      ![] (fun i => i.elim0)
    have hyz' : ∀ z, z ∈ y ↔ z ∈ Lev ξ₀ ∧ Ord z := hyz
    have hyo : Ord y := ⟨fun u hu z hz => (hyz' z).mpr
      ⟨lev_tr hξ₀o u ((hyz' u).mp hu).1 z hz, ord_mem ((hyz' u).mp hu).2 hz⟩,
      fun β hβ => ((hyz' β).mp hβ).2.1⟩
    rcases (ord_le_iff hξ₀o hyo).mp (fun z hz => (hyz' z).mpr ⟨hsub z hz, ord_mem hξ₀o hz⟩)
      with e | e
    · exact hnA (by rw [e]; exact hy.1)
    · exact hnA (lev_mono hμo hξ₀μ _ ((hyz' ξ₀).mp e).1)

/-- **Every ordinal is constructible.** -/
theorem con_ord {γ : V} (h : Ord γ) : Con γ :=
  let ⟨lam, hl, hγl⟩ := exists_lim h
  ⟨lam, hl.1, ord_mem_lev_lim hl γ hγl⟩

/-! ### The notions of `AlephTheory.lean` in a model of `𝗠𝗛` -/

theorem hin_isSing_iff {u a : V} : Hin.IsSing u a ↔ u = {a} :=
  ⟨fun h => mem_ext fun c => by simpa using h c, fun h c => by simp [h]⟩

theorem hin_isUp_iff {u a b : V} : Hin.IsUp u a b ↔ u = {a, b} :=
  ⟨fun h => mem_ext fun c => by simpa using h c, fun h c => by simp [h]⟩

theorem hin_isOp_iff {p a b : V} : Hin.IsOp p a b ↔ p = kp a b := by
  constructor
  · intro h
    refine mem_ext fun z => ?_
    rw [h z, hin_isSing_iff, hin_isUp_iff]
    simp [kp]
  · rintro rfl z
    rw [hin_isSing_iff, hin_isUp_iff]
    simp [kp]

theorem hin_rl_iff {F a b : V} : Hin.Rl F a b ↔ kp a b ∈ F :=
  ⟨fun ⟨_, hp, h⟩ => hin_isOp_iff.mp h ▸ hp, fun h => ⟨kp a b, h, hin_isOp_iff.mpr rfl⟩⟩

theorem no_cycle3 {a b c : V} (h1 : a ∈ b) (h2 : b ∈ c) : c ∉ a := by
  intro h3
  obtain ⟨z, hz, hmin⟩ := m_found ({a, b, c} : V) ⟨a, by simp⟩
  rcases (by simpa using hz : z = a ∨ z = b ∨ z = c) with e | e | e
  · exact hmin c (by simp) (e ▸ h3)
  · exact hmin a (by simp) (e ▸ h1)
  · exact hmin b (by simp) (e ▸ h2)

theorem ord_of_ordS {x : V} (h : OrdS x) : Ord x := by
  refine ⟨fun y hy z hz => h.1 y z hy hz, fun β hβ y hy z hz => ?_⟩
  have hyx : y ∈ x := h.1 β y hβ hy
  have hzx : z ∈ x := h.1 y z hyx hz
  rcases h.2 z β hzx hβ with e | e | e
  · rw [e] at hz
    exact absurd hy (mem_asymm hz)
  · exact e
  · exact absurd e (no_cycle3 hz hy)

theorem ordS_of_ord {x : V} (h : Ord x) : OrdS x :=
  ⟨fun u v hu hv => h.1 u hu v hv, fun u v hu hv => by
    rcases ord_tri (ord_mem h hu) (ord_mem h hv) with e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inl e
    · exact Or.inr (Or.inr e)⟩

theorem omegaS_om : OmegaS (om : V) := by
  refine ⟨ordS_of_ord ord_om, ⟨∅, empty_mem_om, fun z => by simp⟩,
    fun u hu => ⟨sc u, sc_mem_om hu, fun z => mem_sc.trans or_comm⟩, fun u hu => ?_⟩
  rcases om_cases hu with e | ⟨m, hm, e⟩
  · exact Or.inl fun z => by rw [e]; simp
  · exact Or.inr ⟨m, hm, fun z => by rw [e]; exact mem_sc.trans or_comm⟩

theorem om_sub_of_omegaS {a : V} (h : OmegaS a) : ∀ n, n ∈ (om : V) → n ∈ a := by
  obtain ⟨-, ⟨e, hea, he⟩, hs, -⟩ := h
  have e0 : e = ∅ :=
    mem_ext fun z => ⟨fun hz => absurd hz (he z), fun hz => absurd hz (by simp)⟩
  have h0 : (∅ : V) ∈ a := e0 ▸ hea
  refine om_ind (k := 1) (BDef.mem 0 1) ![a] h0 (fun n _ hn => ?_)
  obtain ⟨s, hsa, hsz⟩ := hs n hn
  have es : s = sc n := mem_ext fun z => (hsz z).trans (mem_sc.trans or_comm).symm
  have h1 : sc n ∈ a := es ▸ hsa
  exact h1

theorem injV_of_injS {F A B : V} (h : InjS F A B) : InjV F A B :=
  ⟨fun u hu => let ⟨v, hv, hr⟩ := h.1 u hu; ⟨v, hv, pr_iff.mpr (hin_rl_iff.mp hr)⟩,
    fun u hu u' hu' v _ h1 h2 => h.2 u u' v hu hu' (hin_rl_iff.mpr (pr_iff.mp h1))
      (hin_rl_iff.mpr (pr_iff.mp h2))⟩

theorem trim_kp {F F' A B : V}
    (hsp : ∀ z, z ∈ F' ↔ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧ z = kp u v)) (u v : V) :
    kp u v ∈ F' ↔ (kp u v ∈ F ∧ u ∈ A ∧ v ∈ B) := by
  constructor
  · intro h
    obtain ⟨hF, u', hu', v', hv', e⟩ := (hsp _).mp h
    obtain ⟨e1, e2⟩ := kp_inj e
    rw [e1, e2]
    exact ⟨e1 ▸ e2 ▸ hF, hu', hv'⟩
  · exact fun h => (hsp _).mpr ⟨h.1, u, h.2.1, v, h.2.2, rfl⟩

theorem injS_trim {F F' A B : V} (h : InjV F A B)
    (hsp : ∀ z, z ∈ F' ↔ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧ z = kp u v)) : InjS F' A B :=
  ⟨fun u hu => let ⟨v, hv, hr⟩ := h.1 u hu
    ⟨v, hv, hin_rl_iff.mpr ((trim_kp hsp u v).mpr ⟨pr_iff.mp hr, hu, hv⟩)⟩,
    fun u u' v hu hu' h1 h2 => by
      have a1 := (trim_kp hsp u v).mp (hin_rl_iff.mp h1)
      have a2 := (trim_kp hsp u' v).mp (hin_rl_iff.mp h2)
      exact h.2 u hu u' hu' v a1.2.2 (pr_iff.mpr a1.1) (pr_iff.mpr a2.1)⟩

omit [Nonempty V] hH in
theorem injS_mono {F A B B' : V} (h : InjS F A B) (hB : ∀ z, z ∈ B → z ∈ B') : InjS F A B' :=
  ⟨fun u hu => let ⟨v, hv, hr⟩ := h.1 u hu; ⟨v, hB v hv, hr⟩, h.2⟩

theorem con_kp {a b : V} (ha : Con a) (hb : Con b) : Con (kp a b) :=
  let ⟨γ, hγ, h1, h2⟩ := con_big2 ha hb
  ⟨scn 4 γ, (big_scn hγ 4).1, kp_mem_lev hγ h1 h2⟩

theorem con_big3 {x y z : V} (hx : Con x) (hy : Con y) (hz : Con z) :
    ∃ γ : V, Big γ ∧ x ∈ Lev γ ∧ y ∈ Lev γ ∧ z ∈ Lev γ := by
  obtain ⟨γ₁, g₁, h1, h2⟩ := con_big2 hx hy
  obtain ⟨γ₂, g₂, h3⟩ := con_big hz
  rcases ord_tri g₁.1 g₂.1 with h | h | h
  · exact ⟨γ₂, g₂, lev_mono g₂.1 h _ h1, lev_mono g₂.1 h _ h2, h3⟩
  · exact ⟨γ₁, g₁, h1, h2, h ▸ h3⟩
  · exact ⟨γ₁, g₁, h1, h2, lev_mono g₁.1 h _ h3⟩

/-- **The pairs of a constructible relation that lie in the product of two constructible sets
form a constructible set.** -/
theorem exists_trim {F A B : V} (hF : Con F) (hA : Con A) (hB : Con B) :
    ∃ F' : V, Con F' ∧ ∀ z, z ∈ F' ↔ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧ z = kp u v) := by
  obtain ⟨γ, hγ, h1, h2, h3⟩ := con_big3 hF hA hB
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef closed_true trimB (good_of_con (con_lev hγ.1))
    (lev_tr hγ.1) ![F, A, B] (by
      intro j
      match j with
      | 0 => exact ⟨h1, good_of_con hF⟩
      | 1 => exact ⟨h2, good_of_con hA⟩
      | 2 => exact ⟨h3, good_of_con hB⟩)
  have hyz' : ∀ z, z ∈ y ↔ z ∈ Lev γ ∧ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ w, w ∈ B ∧ IsOp z u w) := hyz
  refine ⟨y, con_of_good hy, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨-, hF', u, hu, v, hv, hop⟩ := (hyz' z).mp h
    exact ⟨hF', u, hu, v, hv, isOp_iff.mp hop⟩
  · obtain ⟨hF', u, hu, v, hv, e⟩ := h
    exact (hyz' z).mpr ⟨lev_tr hγ.1 F h1 z hF', hF', u, hu, v, hv, isOp_iff.mpr e⟩

/-! ### The alephs exist in every model of `𝗠𝗛` -/

/-- **An ordinal that maps one-to-one into `a` is a member of every set that bounds the
collapses of the well-founded relations on `sc a`.** The order of the ordinal is copied to
its values, the point `a` is put above them, and the collapse of the point is the ordinal. -/
theorem ord_mem_hc {a ξ F T : V} (hT : HCat T (sc a)) (hξ : Ord ξ)
    (htot : ∀ α, α ∈ ξ → ∃ v, v ∈ a ∧ Pr F α v)
    (hinj : ∀ α, α ∈ ξ → ∀ α', α' ∈ ξ → ∀ v, Pr F α v → Pr F α' v → α = α') : ξ ∈ T := by
  let u : V := sc a
  let r : V := relB (k := 3) hartB u u ![F, ξ, a]
  have hr : ∀ x y, Pr r x y ↔ x ∈ u ∧ y ∈ u ∧
      (((∃ α, α ∈ ξ ∧ ∃ β, β ∈ ξ ∧ (Pr F α x ∧ (Pr F β y ∧ α ∈ β))) ∧ (x ∈ a ∧ y ∈ a)) ∨
        (y = a ∧ (x ∈ a ∧ ∃ α, α ∈ ξ ∧ Pr F α x))) :=
    fun x y => pr_relB hartB u u ![F, ξ, a] x y
  have hau : ∀ x, x ∈ a → x ∈ u := fun x hx => mem_sc.mpr (Or.inr hx)
  have haa : a ∈ u := self_mem_sc a
  have hwf : WFon r u := by
    intro X hne hsub
    obtain ⟨c₁, hc₁, -⟩ := hne
    by_cases hA : ∃ c, c ∈ X ∧ (c ∈ a ∧ ∃ α, α ∈ ξ ∧ Pr F α c)
    · let Zs : V := sepB (k := 3) (BDef.bex 1 ((BDef.mem 0 4).and (prB.comp ![3, 1, 0]))) ξ
        ![X, F, a]
      have hZs : ∀ α, α ∈ Zs ↔ α ∈ ξ ∧ ∃ c, c ∈ X ∧ (c ∈ a ∧ Pr F α c) :=
        fun α => mem_sepB _ _ _ α
      obtain ⟨c, hcX, hca, α, hα, hαc⟩ := hA
      obtain ⟨α₀, hα₀, hleast⟩ := ord_least Zs (fun z hz => ord_mem hξ ((hZs z).mp hz).1)
        ⟨α, (hZs α).mpr ⟨hα, c, hcX, hca, hαc⟩⟩
      obtain ⟨hα₀ξ, c₀, hc₀X, hc₀a, hα₀c₀⟩ := (hZs α₀).mp hα₀
      refine ⟨c₀, hc₀X, fun b hbX hbr => ?_⟩
      obtain ⟨-, -, hcase⟩ := (hr b c₀).mp hbr
      rcases hcase with ⟨⟨α', hα', β, hβ, h1, h2, h3⟩, hba, -⟩ | ⟨e, -⟩
      · have eβ : β = α₀ := hinj β hβ α₀ hα₀ξ c₀ h2 hα₀c₀
        rw [eβ] at h3
        rcases hleast α' ((hZs α').mpr ⟨hα', b, hbX, hba, h1⟩) with e | e
        · rw [e] at h3
          exact mem_irrefl _ h3
        · exact mem_asymm h3 e
      · rw [e] at hc₀a
        exact mem_irrefl _ hc₀a
    · refine ⟨c₁, hc₁, fun b hbX hbr => hA ?_⟩
      obtain ⟨-, -, hcase⟩ := (hr b c₁).mp hbr
      rcases hcase with ⟨⟨α', hα', β, hβ, h1, h2, h3⟩, hba, -⟩ | ⟨-, hba, α', hα', h1⟩
      · exact ⟨b, hbX, hba, α', hα', h1⟩
      · exact ⟨b, hbX, hba, α', hα', h1⟩
  obtain ⟨G, hG⟩ := hT.2 r hwf
  have guniq : ∀ b, b ∈ u → ∀ v, Pr G b v → ∀ v', Pr G b v' → v = v' := by
    intro b hb v hv v' hv'
    obtain ⟨w, -, -, hw, -⟩ := hG b hb
    rw [hw v hv, hw v' hv']
  -- the collapse of a value is the ordinal it is the value of
  have key : ∀ η, η ∈ ξ → ∀ v, v ∈ a → Pr F η v → Pr G v η := by
    by_contra hcon
    let Z : V := sepB (k := 3)
      (BDef.bex 3 ((prB.comp ![2, 1, 0]).and (prB.comp ![3, 0, 1]).not)) ξ ![F, G, a]
    have hZ : ∀ η, η ∈ Z ↔ η ∈ ξ ∧ ∃ v, v ∈ a ∧ (Pr F η v ∧ ¬Pr G v η) :=
      fun η => mem_sepB _ _ _ η
    have hne : ∃ η, η ∈ Z := by
      by_contra hno
      exact hcon fun η hη v hv hF => by
        by_contra hG'
        exact hno ⟨η, (hZ η).mpr ⟨hη, v, hv, hF, hG'⟩⟩
    obtain ⟨η₀, hη₀, hleast⟩ := ord_least Z (fun z hz => ord_mem hξ ((hZ z).mp hz).1) hne
    obtain ⟨hη₀ξ, v₀, hv₀, hFv₀, hnG⟩ := (hZ η₀).mp hη₀
    obtain ⟨w, -, hGw, -, hwy⟩ := hG v₀ (hau v₀ hv₀)
    have ew : w = η₀ := mem_ext fun y => by
      rw [hwy]
      constructor
      · rintro ⟨x, hxu, hrx, hGx⟩
        obtain ⟨-, -, hcase⟩ := (hr x v₀).mp hrx
        rcases hcase with ⟨⟨α, hα, β, hβ, h1, h2, h3⟩, hxa, -⟩ | ⟨e, -⟩
        · have eβ : β = η₀ := hinj β hβ η₀ hη₀ξ v₀ h2 hFv₀
          rw [eβ] at h3
          have hGα : Pr G x α := by
            by_contra hn
            rcases hleast α ((hZ α).mpr ⟨hα, x, hxa, h1, hn⟩) with e | e
            · rw [e] at h3
              exact mem_irrefl _ h3
            · exact mem_asymm h3 e
          rw [guniq x hxu y hGx α hGα]
          exact h3
        · rw [e] at hv₀
          exact absurd hv₀ (mem_irrefl _)
      · intro hy
        have hyξ : y ∈ ξ := hξ.1 η₀ hη₀ξ y hy
        obtain ⟨x, hxa, hFx⟩ := htot y hyξ
        have hGx : Pr G x y := by
          by_contra hn
          rcases hleast y ((hZ y).mpr ⟨hyξ, x, hxa, hFx, hn⟩) with e | e
          · rw [e] at hy
            exact mem_irrefl _ hy
          · exact mem_asymm hy e
        exact ⟨x, hau x hxa, (hr x v₀).mpr ⟨hau x hxa, hau v₀ hv₀,
          Or.inl ⟨⟨y, hyξ, η₀, hη₀ξ, hFx, hFv₀, hy⟩, hxa, hv₀⟩⟩, hGx⟩
    rw [ew] at hGw
    exact hnG hGw
  obtain ⟨w, hwT, -, -, hwy⟩ := hG a haa
  have ew : w = ξ := mem_ext fun y => by
    rw [hwy]
    constructor
    · rintro ⟨x, hxu, hrx, hGx⟩
      obtain ⟨-, -, hcase⟩ := (hr x a).mp hrx
      rcases hcase with ⟨-, -, haa'⟩ | ⟨-, hxa, α, hα, h1⟩
      · exact absurd haa' (mem_irrefl _)
      · rw [guniq x hxu y hGx α (key α hα x hxa h1)]
        exact hα
    · intro hy
      obtain ⟨x, hxa, hFx⟩ := htot y hy
      exact ⟨x, hau x hxa, (hr x a).mpr ⟨hau x hxa, haa, Or.inr ⟨rfl, hxa, y, hy, hFx⟩⟩,
        key y hy x hxa hFx⟩
  rw [← ew]
  exact hwT

theorem exists_trimV (F A B : V) :
    ∃ F' : V, ∀ z, z ∈ F' ↔ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧ z = kp u v) := by
  refine ⟨sepB trimB F ![F, A, B], fun z => ?_⟩
  have h : z ∈ sepB trimB F ![F, A, B] ↔ z ∈ F ∧ (z ∈ F ∧ ∃ u, u ∈ A ∧ ∃ w, w ∈ B ∧ IsOp z u w) :=
    mem_sepB _ _ _ z
  rw [h]
  constructor
  · rintro ⟨hF, -, u, hu, v, hv, hop⟩
    exact ⟨hF, u, hu, v, hv, isOp_iff.mp hop⟩
  · rintro ⟨hF, u, hu, v, hv, e⟩
    exact ⟨hF, hF, u, hu, v, hv, isOp_iff.mpr e⟩

/-- **Hartogs' theorem with ordinals.** For every set there is a least ordinal that does not
map one-to-one into it. -/
theorem next_exists (a : V) : ∃ a' : V, NextS a a' := by
  obtain ⟨T, hT⟩ := hc_of_models (V := V) (sc a)
  have hK : Ord (kap T) := ord_kap hT.1
  have hbig : ∀ ξ F, Ord ξ → InjS F ξ a → ξ ∈ kap T := fun ξ F hξ hF =>
    mem_kap.mpr ⟨ord_mem_hc hT hξ
      (fun α hα => let ⟨v, hv, h⟩ := hF.1 α hα; ⟨v, hv, pr_iff.mpr (hin_rl_iff.mp h)⟩)
      (fun α hα α' hα' v h1 h2 => hF.2 α α' v hα hα' (hin_rl_iff.mpr (pr_iff.mp h1))
        (hin_rl_iff.mpr (pr_iff.mp h2))), hξ⟩
  let P : V := ℘ (prodS (sc (kap T)) a)
  have key : ∀ ξ, ξ ∈ sc (kap T) → ((∃ F, InjS F ξ a) ↔ ∃ F, F ∈ P ∧ InjV F ξ a) := by
    intro ξ hξ
    constructor
    · rintro ⟨F, hinj⟩
      obtain ⟨F', hsp⟩ := exists_trimV F ξ a
      refine ⟨F', mem_power_iff.mpr fun z hz => ?_,
        injV_of_injS (injS_trim (injV_of_injS hinj) hsp)⟩
      obtain ⟨-, u, hu, v, hv, e⟩ := (hsp z).mp hz
      exact mem_prodS.mpr ⟨u, (ord_sc hK).1 ξ hξ u hu, v, hv, e⟩
    · rintro ⟨F, -, hinj⟩
      obtain ⟨F', hsp⟩ := exists_trimV F ξ a
      exact ⟨F', injS_trim hinj hsp⟩
  let Z : V := sepB (k := 2) ((BDef.bex 1 (injVB.comp ![0, 1, 3])).not) (sc (kap T)) ![P, a]
  have hZ : ∀ ξ, ξ ∈ Z ↔ ξ ∈ sc (kap T) ∧ ¬∃ F, F ∈ P ∧ InjV F ξ a :=
    fun ξ => mem_sepB _ _ _ ξ
  have hKZ : kap T ∈ Z := (hZ _).mpr ⟨self_mem_sc _, fun hex => by
    obtain ⟨F, hinj⟩ := (key _ (self_mem_sc _)).mpr hex
    exact mem_irrefl _ (hbig _ F hK hinj)⟩
  obtain ⟨y, hyZ, hleast⟩ :=
    ord_least Z (fun z hz => ord_mem (ord_sc hK) ((hZ z).mp hz).1) ⟨_, hKZ⟩
  obtain ⟨hya, hyn⟩ := (hZ y).mp hyZ
  have hyo : Ord y := ord_mem (ord_sc hK) hya
  refine ⟨y, ordS_of_ord hyo, fun hex => hyn ((key y hya).mp hex), fun z hz => ?_⟩
  have hza : z ∈ sc (kap T) := (ord_sc hK).1 y hya z hz
  have hnZ : z ∉ Z := fun h => by
    rcases hleast z h with e1 | e1
    · rw [e1] at hz
      exact mem_irrefl _ hz
    · exact mem_asymm hz e1
  have hex : ∃ F, F ∈ P ∧ InjV F z a := by
    by_contra hne
    exact hnZ ((hZ _).mpr ⟨hza, hne⟩)
  exact (key z hza).mpr hex

/-- **"`ℵₙ` exists" holds in every model of `𝗠𝗛`.** -/
theorem aleph_exists : ∀ n : ℕ, ∃ y : V, IsAleph n y
  | 0 => ⟨om, omegaS_om⟩
  | n + 1 =>
    let ⟨a, ha⟩ := aleph_exists n
    let ⟨a', hn⟩ := next_exists a
    ⟨a', a, ha, hn⟩

/-! ### A structure embedded onto the constructible sets -/

variable {W : Type} [SetStructure W] (i : W → V) (hi : Function.Injective i)
  (hran : ∀ x : V, Con x ↔ ∃ w, i w = x) (hmem : ∀ a b : W, a ∈ b ↔ i a ∈ i b)

include hi hran hmem

theorem lift_mem {x : V} (w : W) (hx : x ∈ i w) : ∃ w', i w' = x ∧ w' ∈ w := by
  obtain ⟨w', hw'⟩ := (hran _).mp (con_tr ((hran _).mpr ⟨w, rfl⟩) hx)
  exact ⟨w', hw', (hmem _ _).mpr (by rw [hw']; exact hx)⟩

theorem sing_tr {u a : W} : Hin.IsSing u a ↔ i u = {i a} := by
  constructor
  · intro h
    refine mem_ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨c, rfl, hc⟩ := lift_mem i hi hran hmem u hx
      rw [(h c).mp hc]
      simp
    · rw [show x = i a by simpa using hx]
      exact (hmem _ _).mp ((h a).mpr rfl)
  · intro h c
    rw [hmem c u, h]
    simp [hi.eq_iff]

theorem up_tr {u a b : W} : Hin.IsUp u a b ↔ i u = {i a, i b} := by
  constructor
  · intro h
    refine mem_ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨c, rfl, hc⟩ := lift_mem i hi hran hmem u hx
      rcases (h c).mp hc with e | e <;> simp [e]
    · rcases (by simpa using hx : x = i a ∨ x = i b) with e | e
      · rw [e]
        exact (hmem _ _).mp ((h a).mpr (Or.inl rfl))
      · rw [e]
        exact (hmem _ _).mp ((h b).mpr (Or.inr rfl))
  · intro h c
    rw [hmem c u, h]
    simp [hi.eq_iff]

theorem isOp_tr {p a b : W} : Hin.IsOp p a b ↔ i p = kp (i a) (i b) := by
  have hc : ∀ w, Con (i w) := fun w => (hran _).mpr ⟨w, rfl⟩
  have hk : Con (kp (i a) (i b)) := con_kp (hc a) (hc b)
  constructor
  · intro h
    refine mem_ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨z, rfl, hz⟩ := lift_mem i hi hran hmem p hx
      rcases (h z).mp hz with e | e
      · rw [(sing_tr i hi hran hmem).mp e]
        simp [kp]
      · rw [(up_tr i hi hran hmem).mp e]
        simp [kp]
    · obtain ⟨z, rfl⟩ := (hran _).mp (con_tr hk hx)
      refine (hmem _ _).mp ((h z).mpr ?_)
      rcases (by simpa [kp] using hx : i z = {i a} ∨ i z = {i a, i b}) with e | e
      · exact Or.inl ((sing_tr i hi hran hmem).mpr e)
      · exact Or.inr ((up_tr i hi hran hmem).mpr e)
  · intro h z
    rw [hmem z p, h, sing_tr i hi hran hmem, up_tr i hi hran hmem]
    simp [kp]

theorem rl_tr {f a b : W} : Hin.Rl f a b ↔ kp (i a) (i b) ∈ i f := by
  constructor
  · rintro ⟨p, hp, h⟩
    rw [← (isOp_tr i hi hran hmem).mp h]
    exact (hmem _ _).mp hp
  · intro h
    obtain ⟨p, hp, hpf⟩ := lift_mem i hi hran hmem f h
    exact ⟨p, hpf, (isOp_tr i hi hran hmem).mpr hp⟩

theorem injS_tr {f a b : W} : InjS f a b ↔ InjS (i f) (i a) (i b) := by
  have hc : ∀ w, Con (i w) := fun w => (hran _).mpr ⟨w, rfl⟩
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x x' y hx hx' h1 h2 => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := lift_mem i hi hran hmem a hx
      obtain ⟨v, hv, hr⟩ := h.1 u hu
      exact ⟨i v, (hmem _ _).mp hv, hin_rl_iff.mpr ((rl_tr i hi hran hmem).mp hr)⟩
    · obtain ⟨u, rfl, hu⟩ := lift_mem i hi hran hmem a hx
      obtain ⟨u', rfl, hu'⟩ := lift_mem i hi hran hmem a hx'
      have k1 := hin_rl_iff.mp h1
      have hy : Con y := by
        have c1 : Con (kp (i u) y) := con_tr (hc f) k1
        have c2 : Con ({i u, y} : V) := con_tr c1 (by simp [kp])
        exact con_tr c2 (by simp)
      obtain ⟨v, rfl⟩ := (hran _).mp hy
      rw [h.2 u u' v hu hu' ((rl_tr i hi hran hmem).mpr k1)
        ((rl_tr i hi hran hmem).mpr (hin_rl_iff.mp h2))]
  · intro h
    refine ⟨fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
    · obtain ⟨y, hy, hr⟩ := h.1 (i u) ((hmem _ _).mp hu)
      obtain ⟨v, rfl, hv⟩ := lift_mem i hi hran hmem b hy
      exact ⟨v, hv, (rl_tr i hi hran hmem).mpr (hin_rl_iff.mp hr)⟩
    · exact hi (h.2 (i u) (i u') (i v) ((hmem _ _).mp hu) ((hmem _ _).mp hu')
        (hin_rl_iff.mpr ((rl_tr i hi hran hmem).mp h1))
        (hin_rl_iff.mpr ((rl_tr i hi hran hmem).mp h2)))

theorem ordS_tr {x : W} : OrdS x ↔ OrdS (i x) := by
  constructor
  · intro h
    refine ⟨fun y z hy hz => ?_, fun y z hy hz => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := lift_mem i hi hran hmem x hy
      obtain ⟨v, rfl, hv⟩ := lift_mem i hi hran hmem u hz
      exact (hmem _ _).mp (h.1 u v hu hv)
    · obtain ⟨u, rfl, hu⟩ := lift_mem i hi hran hmem x hy
      obtain ⟨v, rfl, hv⟩ := lift_mem i hi hran hmem x hz
      rcases h.2 u v hu hv with e | e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (Or.inl ((hmem _ _).mp e))
      · exact Or.inr (Or.inr ((hmem _ _).mp e))
  · intro h
    refine ⟨fun u v hu hv =>
      (hmem _ _).mpr (h.1 (i u) (i v) ((hmem _ _).mp hu) ((hmem _ _).mp hv)),
      fun u v hu hv => ?_⟩
    rcases h.2 (i u) (i v) ((hmem _ _).mp hu) ((hmem _ _).mp hv) with e | e | e
    · exact Or.inl (hi e)
    · exact Or.inr (Or.inl ((hmem _ _).mpr e))
    · exact Or.inr (Or.inr ((hmem _ _).mpr e))

theorem omegaS_of {x : W} (h : OmegaS (i x)) : OmegaS x := by
  obtain ⟨ho, ⟨e, hex, he⟩, hs, hp⟩ := h
  refine ⟨(ordS_tr i hi hran hmem).mpr ho, ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨e', rfl, he'⟩ := lift_mem i hi hran hmem x hex
    exact ⟨e', he', fun z hz => he (i z) ((hmem _ _).mp hz)⟩
  · obtain ⟨s, hsx, hsz⟩ := hs (i u) ((hmem _ _).mp hu)
    obtain ⟨s', rfl, hs'⟩ := lift_mem i hi hran hmem x hsx
    refine ⟨s', hs', fun z => ?_⟩
    rw [hmem z s', hsz, ← hmem z u, hi.eq_iff]
  · rcases hp (i u) ((hmem _ _).mp hu) with h0 | ⟨p, hpx, hpz⟩
    · exact Or.inl fun z hz => h0 (i z) ((hmem _ _).mp hz)
    · obtain ⟨p', rfl, hp'⟩ := lift_mem i hi hran hmem x hpx
      refine Or.inr ⟨p', hp', fun z => ?_⟩
      rw [hmem z u, hpz, ← hmem z p', hi.eq_iff]

/-- **The next cardinal of the constructible sets.** -/
theorem next_tr {a a' : V} {e : W} (hn : NextS a a') (hsub : ∀ z, z ∈ i e → z ∈ a)
    (heo : OrdS e) : ∃ e' : W, NextS e e' ∧ ∀ z, z ∈ i e' → z ∈ a' := by
  have hc : ∀ w, Con (i w) := fun w => (hran _).mpr ⟨w, rfl⟩
  have ha'o : Ord a' := ord_of_ordS hn.1
  have hbo : Ord (i e) := ord_of_ordS ((ordS_tr i hi hran hmem).mp heo)
  obtain ⟨lam, hl, hal, hbl⟩ := exists_lim2 (ord_sc ha'o) hbo
  have hbig := lim_big hl
  obtain ⟨κ, hκ, hbound⟩ := bound_exists (big_scn hbig 4)
  have hξL : ∀ ξ, ξ ∈ sc a' → ξ ∈ Lev lam := fun ξ hξ =>
    ord_mem_lev_lim hl ξ (hl.1.1 _ hal ξ hξ)
  have hvL : ∀ v, v ∈ i e → v ∈ Lev lam := fun v hv =>
    ord_mem_lev_lim hl v (hl.1.1 _ hbl v hv)
  -- a constructible map from an ordinal up to `a'` into `i e` can be taken in the level at `κ`
  have key : ∀ ξ, ξ ∈ sc a' →
      ((∃ F, Con F ∧ InjS F ξ (i e)) ↔ ∃ F, F ∈ Lev κ ∧ InjV F ξ (i e)) := by
    intro ξ hξ
    have hξc : Con ξ := con_ord (ord_mem (ord_sc ha'o) hξ)
    constructor
    · rintro ⟨F, hF, hinj⟩
      obtain ⟨F', hF', hsp⟩ := exists_trim hF hξc (hc e)
      have h1 : InjS F' ξ (i e) := injS_trim (injV_of_injS hinj) hsp
      obtain ⟨δ, hδ, hFδ⟩ := hF'
      refine ⟨F', hbound δ F' hδ hFδ (fun z hz => ?_), injV_of_injS h1⟩
      obtain ⟨-, u, hu, v, hv, rfl⟩ := (hsp z).mp hz
      exact kp_mem_lev hbig (hξL u ((ord_sc ha'o).1 ξ hξ u hu)) (hvL v hv)
    · rintro ⟨F, hFκ, hinj⟩
      obtain ⟨F', hF', hsp⟩ := exists_trim ⟨κ, hκ, hFκ⟩ hξc (hc e)
      exact ⟨F', hF', injS_trim hinj hsp⟩
  let Z : V := sepB (k := 2) ((BDef.bex 1 (injVB.comp ![0, 1, 3])).not) (sc a') ![Lev κ, i e]
  have hZ : ∀ ξ, ξ ∈ Z ↔ ξ ∈ sc a' ∧ ¬∃ F, F ∈ Lev κ ∧ InjV F ξ (i e) :=
    fun ξ => mem_sepB _ _ _ ξ
  have ha'Z : a' ∈ Z := (hZ a').mpr ⟨self_mem_sc a', fun hex => by
    obtain ⟨F, -, hinj⟩ := (key a' (self_mem_sc a')).mpr hex
    exact hn.2.1 ⟨F, injS_mono hinj hsub⟩⟩
  obtain ⟨y, hyZ, hleast⟩ :=
    ord_least Z (fun z hz => ord_mem (ord_sc ha'o) ((hZ z).mp hz).1) ⟨a', ha'Z⟩
  obtain ⟨hya, hyn⟩ := (hZ y).mp hyZ
  have hyo : Ord y := ord_mem (ord_sc ha'o) hya
  obtain ⟨e', he'⟩ := (hran _).mp (con_ord hyo)
  refine ⟨e', ⟨(ordS_tr i hi hran hmem).mpr (by rw [he']; exact ordS_of_ord hyo),
    fun ⟨f, hf⟩ => ?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · have h1 : InjS (i f) (i e') (i e) := (injS_tr i hi hran hmem).mp hf
    rw [he'] at h1
    exact hyn ((key y hya).mp ⟨i f, hc f, h1⟩)
  · have hzy : i z ∈ y := by rw [← he']; exact (hmem _ _).mp hz
    have hza : i z ∈ sc a' := (ord_sc ha'o).1 y hya (i z) hzy
    have hnZ : i z ∉ Z := fun h => by
      rcases hleast (i z) h with e1 | e1
      · rw [e1] at hzy
        exact mem_irrefl _ hzy
      · exact mem_asymm hzy e1
    have hex : ∃ F, F ∈ Lev κ ∧ InjV F (i z) (i e) := by
      by_contra hne
      exact hnZ ((hZ _).mpr ⟨hza, hne⟩)
    obtain ⟨F, hF, hinj⟩ := (key (i z) hza).mpr hex
    obtain ⟨f, rfl⟩ := (hran _).mp hF
    exact ⟨f, (injS_tr i hi hran hmem).mpr hinj⟩
  · rw [he'] at hz
    rcases mem_sc.mp hya with e1 | e1
    · rw [← e1]
      exact hz
    · exact ha'o.1 y e1 z hz

omit [Nonempty V] hH hi hran hmem in
theorem ordS_of_isAleph : ∀ {n : ℕ} {x : W}, IsAleph n x → OrdS x
  | 0, _, h => h.1
  | _ + 1, _, ⟨_, _, h⟩ => h.1

/-- **The alephs of the constructible sets.** If `a` is `ℵₙ`, then the structure embedded onto
the constructible sets has an `ℵₙ` of its own, included in `a`. -/
theorem aleph_tr : ∀ (n : ℕ) (a : V), IsAleph n a →
    ∃ e : W, IsAleph n e ∧ ∀ z, z ∈ i e → z ∈ a
  | 0, a, h => by
    obtain ⟨e, he⟩ := (hran _).mp (con_ord (ord_om (V := V)))
    refine ⟨e, omegaS_of i hi hran hmem (by rw [he]; exact omegaS_om), fun z hz => ?_⟩
    rw [he] at hz
    exact om_sub_of_omegaS h z hz
  | n + 1, a', ⟨a, ha, hn⟩ => by
    obtain ⟨e, he, hsub⟩ := aleph_tr n a ha
    obtain ⟨e', hn', hsub'⟩ := next_tr i hi hran hmem hn hsub (ordS_of_isAleph he)
    exact ⟨e', ⟨e, he, hn'⟩, hsub'⟩

end ord

end MH

/-! ### The interpretation -/

open DirectTranslation

/-- A model of `𝗠𝗔𝗖` in which "`ℵₙ` exists" holds for every `n` is a model of `𝗠𝗔𝗖𝗔ω`, when it
is given with its relation symbols. -/
theorem models_maca_of {W : Type} [SetStructure W] [Nonempty W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : W↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖) (hal : ∀ n : ℕ, ∃ y : W, IsAleph n y) : W↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖𝗔ω := by
  rcases standardStructure_unique W s
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | ⟨n, rfl⟩
  · exact models_theory_iff.mp h φ hφ
  · exact models_aleph_iff.mpr (hal n)

section

variable {M : Type} [SetStructure M] [Nonempty M] [hTA : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗔ω]

theorem mha_models_mh : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
  models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTA φ (Or.inl hφ)

theorem mha_aleph (n : ℕ) : ∃ y : M, IsAleph n y :=
  models_aleph_iff.mp (models_theory_iff.mp hTA _ (Or.inr ⟨n, rfl⟩))

end

/-- **The translation of `ℒₛₑₜ` into `𝗠𝗛𝗔ω`**: the domain is the constructible sets, and
membership and equality are themselves. -/
def lTranslationA : DirectTranslation 𝗠𝗛𝗔ω ℒₛₑₜ where
  domain := ⟨MH.conF.φ⟩
  rel := lRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    haveI : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mha_models_mh
    suffices ∃ x : M, (⟨MH.conF.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨∅, (lDomain_val_iff ∅).mpr ⟨MH.nm 1, MH.ord_nm 1, MH.nm_mem_lev_nm 0⟩⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : lRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hTA : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗔ω]

/-- The membership relation of the interpreted structure. -/
instance lModelA_setStructure : SetStructure (lTranslationA.Model M) :=
  ⟨fun y x ↦ (x : M) ∈ (y : M)⟩

omit [Nonempty M] hTA in
lemma lModelA_mem_iff (a b : lTranslationA.Model M) : a ∈ b ↔ (a : M) ∈ (b : M) := Iff.rfl

instance lModelA_mem : Tarski.Structure.Mem ℒₛₑₜ (lTranslationA.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : lTranslationA.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact Tarski.Structure.Mem.mem (L := ℒₛₑₜ) (a : M) (b : M)

/-- **In a model of `𝗠𝗛𝗔ω`, the constructible sets form a model of `𝗠𝗔𝗖𝗔ω`.** -/
theorem lModelA_models : (lTranslationA.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖𝗔ω := by
  haveI hMH : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mha_models_mh
  have hinj : Function.Injective (fun a : lTranslationA.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hran : ∀ x : M, MH.Con x ↔ ∃ w : lTranslationA.Model M, (w : M) = x :=
    fun x => ⟨fun hx => ⟨⟨x, (lDomain_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (lDomain_val_iff _).mp w.dom⟩
  haveI h1 : (lTranslationA.Model M)↓[ℒₛₑₜ] ⊧* 𝗠 :=
    IsMacBase.models' (MH.isMacBase_of_con _ hinj hran lModelA_mem_iff)
  haveI h2 : (lTranslationA.Model M)↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
    ac_models' (MH.ac_of_con _ hinj hran lModelA_mem_iff)
  have hMAC : (lTranslationA.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖 := inferInstance
  refine models_maca_of hMAC fun n => ?_
  obtain ⟨y, hy⟩ := mha_aleph (M := M) n
  obtain ⟨e, he, -⟩ := MH.aleph_tr _ hinj hran lModelA_mem_iff n y hy
  exact ⟨e, he⟩

end model

/-- **`𝗠𝗛` with "`ℵₙ` exists" for every `n` interprets `𝗠𝗔𝗖` with the same.** The domain is the
constructible sets; membership and equality are unchanged. -/
instance mhaInterpretsMACA : 𝗠𝗛𝗔ω ⊳ 𝗠𝗔𝗖𝗔ω where
  trln := lTranslationA
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp lModelA_models φ hφ)

/-! ### Without the hypothesis: `𝗠𝗛` proves that the alephs exist -/

/-- **`𝗠𝗛` proves "`ℵₙ` exists"**, for every `n`. -/
theorem mh_provable_aleph (n : ℕ) : 𝗠𝗛 ⊢ Axiom.aleph n := by
  apply SetTheory.complete.{0}
  intro M _ _ _
  exact models_aleph_iff.mpr (MH.aleph_exists n)

/-- `𝗠𝗛𝗔ω` has the theorems of `𝗠𝗛`. -/
instance : 𝗠𝗛𝗔ω ⪯ 𝗠𝗛 := Entailment.WeakerThan.ofAxm! fun {φ} hφ => by
  rcases hφ with hφ | ⟨n, rfl⟩
  · exact Entailment.by_axm hφ
  · exact mh_provable_aleph n

section model'

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **In a model of `𝗠𝗛`, the constructible sets form a model of `𝗠𝗔𝗖𝗔ω`.** -/
theorem lModel_models_maca : (lTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗔𝗖𝗔ω := by
  have hinj : Function.Injective (fun a : lTranslation.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hran : ∀ x : M, MH.Con x ↔ ∃ w : lTranslation.Model M, (w : M) = x :=
    fun x => ⟨fun hx => ⟨⟨x, (lDomain_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (lDomain_val_iff _).mp w.dom⟩
  refine models_maca_of lModel_models fun n => ?_
  obtain ⟨y, hy⟩ := MH.aleph_exists (V := M) n
  obtain ⟨e, he, -⟩ := MH.aleph_tr _ hinj hran lModel_mem_iff n y hy
  exact ⟨e, he⟩

end model'

/-- **`𝗠𝗛` interprets Mac Lane set theory with Choice and "`ℵₙ` exists" for every `n`.** The
domain is the constructible sets; membership and equality are unchanged. -/
instance mhInterpretsMACA : 𝗠𝗛 ⊳ 𝗠𝗔𝗖𝗔ω where
  trln := lTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp lModel_models_maca φ hφ)

/-- **`𝗡𝗙` interprets `𝗠𝗔𝗖𝗔ω`**, through `𝗠𝗛`. -/
instance nfInterpretsMACA : 𝗡𝗙 ⊳ 𝗠𝗔𝗖𝗔ω :=
  DirectInterpretation.comp mhInterpretsMACA nfInterpretsMH

end FFL.FirstOrder.SetTheory
