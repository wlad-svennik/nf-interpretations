module

public import MHIso

@[expose] public section

set_option autoImplicit false

/-!
# The sequence of the levels is constructible

In a model of `𝗠𝗛`.

* `ltL_ord_iff`, `ltL_lev_iff`: on ordinals, and on levels, the order of the constructible sets
  is membership. `mem_lev_iff_ltL`: the members of a level are the sets before it.
* `level_char`: a member `A` of a level is itself a level if and only if its members are the
  sets before it. `con_levels`: the set of the levels below a limit ordinal is constructible.
* `con_levmap`: the map `γ ↦ Lev γ` on a limit ordinal is constructible. It is an isomorphism
  from the ordinal onto the set of the levels, so `oiso_con` of `MHIso.lean` applies.
* `con_lts'`: the order of a level is a constructible set.
* **`con_hier`**: a sequence of the levels with their orders (`IsHier`) is a constructible set.

The hull of `MHCond.lean` is closed under a function that is defined from that sequence; this
is what makes the function, and then the hull, constructible.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- `lt` is the set of the pairs of members of `A` that are in the order given by `Q`. -/
def LtC {V : Type} [SetStructure V] (lt A Q : V) : Prop :=
  (∀ q, q ∈ lt → ∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (IsOp q a b ∧ Pr Q a b)) ∧
  (∀ a, a ∈ A → ∀ b, b ∈ A → Pr Q a b → Pr lt a b)

def ltCB : BDef (k := 3) (fun V _ v ↦ LtC (v 0) (v 1) (v 2)) :=
  ((BDef.ball 0 (BDef.bex 2 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
      (prB.comp ![5, 1, 0]))))).and
    (BDef.ball 1 (BDef.ball 2 ((prB.comp ![4, 1, 0]).imp (prB.comp ![2, 1, 0]))))).congr
    fun _ _ _ => Iff.rfl

/-- `q` is the pair of an ordinal `γ ∈ D` and the pair of the level at `γ` and its order: `I`
is the map from ordinals to levels, `LEV` the set of the levels, `K` bounds the orders. -/
def HierR {V : Type} [SetStructure V] (q D LEV I Q K : V) : Prop :=
  ∃ γ, γ ∈ D ∧ ∃ A, A ∈ LEV ∧ ∃ lt, lt ∈ K ∧ (Pr I γ A ∧ (LtC lt A Q ∧
    ∃ u, u ∈ q ∧ ∃ y, y ∈ u ∧ (IsOp y A lt ∧ IsOp q γ y)))

def hierRB : BDef (k := 6) (fun V _ v ↦ HierR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 1 (BDef.bex 3 (BDef.bex 7 ((prB.comp ![6, 2, 1]).and
    ((ltCB.comp ![0, 1, 7]).and (BDef.bex 3 (BDef.bex 0
      ((isOpB.comp ![0, 3, 2]).and (isOpB.comp ![5, 4, 0]))))))))).congr fun _ _ _ => Iff.rfl

section hier

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem ltL_ord_iff {lam α β : V} (hl : Ord lam) (hα : Ord α) (hβ : Ord β)
    (hαl : α ∈ Lev lam) (hβl : β ∈ Lev lam) : LtL α β ↔ α ∈ β := by
  constructor
  · intro h
    rcases ord_tri hα hβ with e | e | e
    · exact e
    · rw [e] at h
      exact absurd h (ltL_irrefl' hl hβl)
    · exact absurd h (ltL_asymm hl hβl hαl (ltL_of_mem hl hαl e))
  · exact fun h => ltL_of_mem hl hβl h

theorem ltL_lev_iff {γ γ' : V} (hγ : Ord γ) (hγ' : Ord γ') :
    LtL (Lev γ) (Lev γ') ↔ γ ∈ γ' := by
  rw [ltL_iff_rk (rkL_lev hγ) (rkL_lev hγ')]
  constructor
  · rintro (h | ⟨e, hs⟩)
    · exact h
    · exfalso
      rw [← e] at hs
      rcases hs with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2 rfl
      · exact h1 rfl
  · exact fun h => Or.inl h

/-- The members of a level are the sets that come before it. -/
theorem mem_lev_iff_ltL {lam γ x : V} (hl : Ord lam) (hγ : Ord γ) (hx : x ∈ Lev lam) :
    x ∈ Lev γ ↔ LtL x (Lev γ) := by
  obtain ⟨β, -, r⟩ := rkL_exists hl hx
  rw [rkL_mem r hγ, ltL_iff_rk r (rkL_lev hγ)]
  constructor
  · exact fun h => Or.inl h
  · rintro (h | ⟨e, hs⟩)
    · exact h
    · exfalso
      rcases hs with ⟨-, h2⟩ | ⟨-, h2, -⟩
      · rw [e] at h2
        exact h2 rfl
      · rw [e] at h2
        exact h2 rfl

/-- **A member of a level is a level if and only if its members are the sets before it.** -/
theorem level_char {lam A : V} (hl : Ord lam) (hA : A ∈ Lev lam) :
    (∀ x, x ∈ Lev lam → (x ∈ A ↔ LtL x A)) ↔ ∃ γ, γ ∈ lam ∧ A = Lev γ := by
  constructor
  · intro h
    obtain ⟨β, hβ, r⟩ := rkL_exists hl hA
    refine ⟨β, hβ, mem_ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · rcases r.2.1 with e | ⟨s, -, y₁, -, y₂, -, y₃, -, hD⟩
      · rw [e] at hx
        exact hx
      · exact (hD.1 x hx).1
    · have hxl : x ∈ Lev lam := lev_mono hl hβ x hx
      refine (h x hxl).mpr ?_
      obtain ⟨β₁, hβ₁, r₁⟩ := rkL_exists r.1 hx
      exact (ltL_iff_rk r₁ r).mpr (Or.inl hβ₁)
  · rintro ⟨γ, hγ, rfl⟩ x hx
    exact mem_lev_iff_ltL hl (ord_mem hl hγ) hx

/-- **The set of the levels below a limit ordinal is constructible.** -/
theorem con_levels {lam : V} (hl : Lim lam) :
    ∃ LEV : V, Con LEV ∧ ∀ A, A ∈ LEV ↔ ∃ γ, γ ∈ lam ∧ A = Lev γ := by
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hl)
  obtain ⟨γ₀, hγ₀, h1, h2⟩ := con_big2 (con_lev hl.1) hQc
  obtain ⟨L, hL, hLz⟩ := sep_good_bdef (closed_true (V := V)) (k := 2)
    ((BDef.mem 0 1).and (BDef.ball 1 ((BDef.mem 0 1).iff (prB.comp ![3, 0, 1]))))
    (good_of_con (con_lev hγ₀.1)) (lev_tr hγ₀.1) ![Lev lam, Q] (by
      intro i
      match i with
      | 0 => exact ⟨h1, good_of_con (con_lev hl.1)⟩
      | 1 => exact ⟨h2, good_of_con hQc⟩)
  have hLz' : ∀ A, A ∈ L ↔ A ∈ Lev γ₀ ∧
      (A ∈ Lev lam ∧ ∀ x, x ∈ Lev lam → (x ∈ A ↔ Pr Q x A)) := hLz
  refine ⟨L, con_of_good hL, fun A => ?_⟩
  rw [hLz']
  constructor
  · rintro ⟨-, hA, h⟩
    exact (level_char hl.1 hA).mp fun x hx => (h x hx).trans (hQ x A hx hA)
  · rintro ⟨γ, hγ, rfl⟩
    have hA : Lev γ ∈ Lev lam := lev_mem hl.1 hγ
    exact ⟨lev_tr hγ₀.1 _ h1 _ hA, hA, fun x hx =>
      ((level_char hl.1 hA).mpr ⟨γ, hγ, rfl⟩ x hx).trans (hQ x _ hx hA).symm⟩

/-- **The map `γ ↦ Lev γ` on a limit ordinal is constructible.** -/
theorem con_levmap {lam : V} (hl : Lim lam) :
    ∃ I : V, Con I ∧ ∀ γ A, γ ∈ lam → (Pr I γ A ↔ A = Lev γ) := by
  obtain ⟨LEV, hLc, hLEV⟩ := con_levels hl
  obtain ⟨F, hF⟩ := exists_hier hl.1
  let π : V := relB (k := 1) (levAtB.comp ![2, 0, 1]) lam LEV ![F]
  have hπ : ∀ γ A, Pr π γ A ↔ γ ∈ lam ∧ A ∈ LEV ∧ LevAt F γ A :=
    fun γ A => pr_relB _ _ _ _ γ A
  have hπ' : ∀ γ A, γ ∈ lam → (Pr π γ A ↔ A = Lev γ) := by
    intro γ A hγ
    rw [hπ, levAt_lev hl.1 hF (mem_sc.mpr (Or.inr hγ))]
    constructor
    · exact fun h => h.2.2
    · intro e
      exact ⟨hγ, (hLEV A).mpr ⟨γ, hγ, e⟩, e⟩
  have hlamL : ∀ a, a ∈ lam → a ∈ Lev lam := fun a ha => ord_mem_lev_lim hl a ha
  have hLl : ∀ b, b ∈ LEV → b ∈ Lev lam := fun b hb => by
    obtain ⟨γ, hγ, e⟩ := (hLEV b).mp hb
    rw [e]
    exact lev_mem hl.1 hγ
  have hiso : OIso π lam LEV := by
    refine ⟨fun γ hγ => ⟨Lev γ, (hLEV _).mpr ⟨γ, hγ, rfl⟩, (hπ' γ _ hγ).mpr rfl⟩,
      fun b hb => ?_, fun γ hγ γ' hγ' b hb b' hb' h1 h2 => ?_⟩
    · obtain ⟨γ, hγ, e⟩ := (hLEV b).mp hb
      exact ⟨γ, hγ, (hπ' γ _ hγ).mpr e⟩
    · rw [(hπ' γ b hγ).mp h1, (hπ' γ' b' hγ').mp h2,
        ltL_lev_iff (ord_mem hl.1 hγ) (ord_mem hl.1 hγ'),
        ltL_ord_iff hl.1 (ord_mem hl.1 hγ) (ord_mem hl.1 hγ') (hlamL γ hγ) (hlamL γ' hγ')]
  obtain ⟨I, hIc, hI⟩ := oiso_con hl (con_ord hl.1) hLc hlamL hLl hiso
  obtain ⟨I', hI'c, hI'⟩ := exists_trim hIc (con_ord hl.1) hLc
  refine ⟨I', hI'c, fun γ A hγ => ?_⟩
  rw [pr_iff, trim_kp hI' γ A]
  constructor
  · rintro ⟨h, -, hA⟩
    exact (hπ' γ A hγ).mp ((hI γ A hγ hA).mp h)
  · intro e
    have hA : A ∈ LEV := (hLEV A).mpr ⟨γ, hγ, e⟩
    exact ⟨(hI γ A hγ hA).mpr ((hπ' γ A hγ).mpr e), hγ, hA⟩

/-- The order of a level is a constructible set, for every ordinal. -/
theorem con_lts' {δ : V} (hδ : Ord δ) : Con (LtS δ) := by
  obtain ⟨lam, hl, hδl⟩ := exists_lim hδ
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hl)
  have hsub : ∀ a, a ∈ Lev δ → a ∈ Lev lam := lev_mono hl.1 hδl
  obtain ⟨γ, hγ, h1, h2⟩ := con_big2 hQc (con_lev hδ)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef (closed_true (V := V)) (k := 2)
    (BDef.bex 2 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and (prB.comp ![3, 1, 0]))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![Q, Lev δ] (by
      intro j
      match j with
      | 0 => exact ⟨up _ h1, good_of_con hQc⟩
      | 1 => exact ⟨up _ h2, good_of_con (con_lev hδ)⟩)
  have hyz' : ∀ z, z ∈ y ↔ z ∈ Lev (scn 4 γ) ∧ ∃ a, a ∈ Lev δ ∧ ∃ b, b ∈ Lev δ ∧
      (IsOp z a b ∧ Pr Q a b) := hyz
  have e : y = LtS δ := mem_ext fun z => by
    rw [hyz']
    constructor
    · rintro ⟨-, a, ha, b, hb, hop, hpr⟩
      rw [isOp_iff.mp hop]
      exact pr_iff.mp ((lts_iff hδ).mpr ⟨ha, hb, (hQ a b (hsub a ha) (hsub b hb)).mp hpr⟩)
    · intro hz
      obtain ⟨a, b, rfl, hpr⟩ := lts_pair hδ hz
      obtain ⟨ha, hb, hlt⟩ := (lts_iff hδ).mp hpr
      exact ⟨kp_mem_lev hγ (lev_tr hγ.1 _ h2 a ha) (lev_tr hγ.1 _ h2 b hb), a, ha, b, hb,
        isOp_kp a b, (hQ a b (hsub a ha) (hsub b hb)).mpr hlt⟩
  rw [← e]
  exact con_of_good hy

theorem ltC_iff {lam Q γ lt : V} (hl : Ord lam)
    (hQ : ∀ x y, x ∈ Lev lam → y ∈ Lev lam → (Pr Q x y ↔ LtL x y)) (hγ : γ ∈ lam) :
    LtC lt (Lev γ) Q ↔ lt = LtS γ := by
  have hγo := ord_mem hl hγ
  have hsub : ∀ a, a ∈ Lev γ → a ∈ Lev lam := lev_mono hl hγ
  constructor
  · rintro ⟨c1, c2⟩
    refine mem_ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨a, ha, b, hb, hop, hpr⟩ := c1 q hq
      rw [isOp_iff.mp hop]
      exact pr_iff.mp ((lts_iff hγo).mpr ⟨ha, hb, (hQ a b (hsub a ha) (hsub b hb)).mp hpr⟩)
    · obtain ⟨a, b, rfl, hpr⟩ := lts_pair hγo hq
      obtain ⟨ha, hb, hlt⟩ := (lts_iff hγo).mp hpr
      exact pr_iff.mp (c2 a ha b hb ((hQ a b (hsub a ha) (hsub b hb)).mpr hlt))
  · intro e
    rw [e]
    refine ⟨fun q hq => ?_, fun a ha b hb hpr => ?_⟩
    · obtain ⟨a, b, rfl, hpr⟩ := lts_pair hγo hq
      obtain ⟨ha, hb, hlt⟩ := (lts_iff hγo).mp hpr
      exact ⟨a, ha, b, hb, isOp_kp a b, (hQ a b (hsub a ha) (hsub b hb)).mpr hlt⟩
    · exact (lts_iff hγo).mpr ⟨ha, hb, (hQ a b (hsub a ha) (hsub b hb)).mp hpr⟩

/-- **A sequence of the levels with their orders is a constructible set.** -/
theorem con_hier {F δ : V} (hδ : Ord δ) (hF : IsHier F δ) : Con F := by
  obtain ⟨lam, hl, hδl⟩ := exists_lim hδ
  have hbig := lim_big hl
  have hDl : ∀ γ, γ ∈ sc δ → γ ∈ lam := fun γ hγ => hl.1.1 _ (hl.2.2 δ hδl) γ hγ
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet hbig
  obtain ⟨LEV, hLc, hLEV⟩ := con_levels hl
  obtain ⟨I, hIc, hI⟩ := con_levmap hl
  obtain ⟨κ₄, hκ₄, hb₄⟩ := bound_exists (big_scn hbig 4)
  have hK := con_lev hκ₄
  have hDc : Con (sc δ) := con_ord (ord_sc hδ)
  -- the orders of the levels are members of the level at `κ₄`
  have hltK : ∀ γ, γ ∈ sc δ → LtS γ ∈ Lev κ₄ := by
    intro γ hγ
    have hγo := ord_mem (ord_sc hδ) hγ
    obtain ⟨d, hd, hLd⟩ := con_lts' hγo
    refine hb₄ d _ hd hLd fun z hz => ?_
    obtain ⟨a, b, rfl, hpr⟩ := lts_pair hγo hz
    obtain ⟨ha, hb, -⟩ := (lts_iff hγo).mp hpr
    exact kp_mem_lev hbig (lev_mono hl.1 (hDl γ hγ) a ha) (lev_mono hl.1 (hDl γ hγ) b hb)
  -- a level that has the parameters, the ordinals, the levels and their orders as members
  obtain ⟨γ₁, hγ₁, -, hlamγ, hlst⟩ := good_common (good_of_con (con_lev hl.1))
    [sc δ, LEV, I, Q, Lev κ₄] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with e | e | e | e | e
      · rw [e]; exact good_of_con hDc
      · rw [e]; exact good_of_con hLc
      · rw [e]; exact good_of_con hIc
      · rw [e]; exact good_of_con hQc
      · rw [e]; exact good_of_con hK)
  have g4 := big_scn hγ₁ 4
  have g8 := big_scn g4 4
  have up4 := lev_scn_sub hγ₁.1 4
  have up8 := lev_scn_sub g4.1 4
  obtain ⟨F', hF'g, hF'z⟩ := sep_good_bdef (closed_true (V := V)) (k := 5) hierRB
    (good_of_con (con_lev g8.1)) (lev_tr g8.1) ![sc δ, LEV, I, Q, Lev κ₄] (by
      intro i
      match i with
      | 0 => exact ⟨up8 _ (up4 _ (hlst (sc δ) (by simp))), good_of_con hDc⟩
      | 1 => exact ⟨up8 _ (up4 _ (hlst LEV (by simp))), good_of_con hLc⟩
      | 2 => exact ⟨up8 _ (up4 _ (hlst I (by simp))), good_of_con hIc⟩
      | 3 => exact ⟨up8 _ (up4 _ (hlst Q (by simp))), good_of_con hQc⟩
      | 4 => exact ⟨up8 _ (up4 _ (hlst (Lev κ₄) (by simp))), good_of_con hK⟩)
  have hF'z' : ∀ q, q ∈ F' ↔ q ∈ Lev (scn 4 (scn 4 γ₁)) ∧ HierR q (sc δ) LEV I Q (Lev κ₄) :=
    hF'z
  have e : F = F' := mem_ext fun q => by
    rw [hF'z']
    constructor
    · intro hq
      obtain ⟨γ, hγ, u, hu, y, hy, hop⟩ := hF.1 q hq
      have hpr : Pr F γ y := pr_iff.mpr (by rw [← isOp_iff.mp hop]; exact hq)
      have ey : y = kp (Lev γ) (LtS γ) := att_fun hF hpr (hier_lev hδ hF hγ)
      have hγl := hDl γ hγ
      have hγ1 : γ ∈ Lev γ₁ := lev_tr hγ₁.1 _ hlamγ γ (ord_mem_lev_lim hl γ hγl)
      have hA1 : Lev γ ∈ Lev γ₁ := lev_tr hγ₁.1 _ hlamγ _ (lev_mem hl.1 hγl)
      have hlt1 : LtS γ ∈ Lev γ₁ := lev_tr hγ₁.1 _ (hlst (Lev κ₄) (by simp)) _ (hltK γ hγ)
      refine ⟨?_, γ, hγ, Lev γ, (hLEV _).mpr ⟨γ, hγl, rfl⟩, LtS γ, hltK γ hγ,
        (hI γ _ hγl).mpr rfl, (ltC_iff hl.1 hQ hγl).mpr rfl, u, hu, y, hy, ?_, hop⟩
      · rw [isOp_iff.mp hop, ey]
        exact kp_mem_lev g4 (up4 _ hγ1) (kp_mem_lev hγ₁ hA1 hlt1)
      · rw [ey]
        exact isOp_kp _ _
    · rintro ⟨-, γ, hγ, A, -, lt, -, hIγ, hlt, u, -, y, -, hopy, hopq⟩
      have hγl := hDl γ hγ
      have eA : A = Lev γ := (hI γ A hγl).mp hIγ
      rw [eA] at hlt hopy
      have elt : lt = LtS γ := (ltC_iff hl.1 hQ hγl).mp hlt
      rw [elt] at hopy
      rw [isOp_iff.mp hopq, isOp_iff.mp hopy]
      exact pr_iff.mp (hier_lev hδ hF hγ)
  rw [e]
  exact con_of_good hF'g

end hier

end MH

end FFL.FirstOrder.SetTheory
