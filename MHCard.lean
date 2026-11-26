module

public import MHHost

@[expose] public section

set_option autoImplicit false

/-!
# The next height: levels that map one-to-one into a constructible set

In a model of `𝗠𝗛`, for a constructible set `S`, `LInj A S` says that `A` maps one-to-one into
`S` by a constructible relation.

* `linj_bound`: for the members of a level, the relation can be taken in a fixed level, so the
  condition is bounded.
* `lnext_exists`: there is a least ordinal `κ` such that the level at `κ` does not map
  one-to-one into `S` by a constructible relation. An upper bound comes from Hartogs' theorem
  in the model (`next_exists`) and from `ord_mem_lev_lim`.

* `linj_succ`: if a level above `ω` maps one-to-one into `S` by a constructible relation, so
  does the next level, when `S` is closed under pairs: a member of the next level is coded by
  the codes of the parameters of one of its definitions (`CdR`, `cdR_inj`).
* `lnext_spec`: for a limit ordinal `ν` above `ω` and `S` the level at `ν`, the least such `κ`
  is a limit ordinal above `ν`.

* `lnext_reg`: this `κ` is regular: a constructible set of members of the level at `κ` that maps
  one-to-one into the level at `ν` by a constructible relation is included in an earlier level
  (`JRel`).

* `lnext_bd`: the second closure property (bd) of `Full` holds at `κ`.
  `full_of_sub`: `κ` satisfies `Full` of `MHHost.lean` if it has the first closure property
  (sub): every constructible subset of a member of the level at `κ` is a member of that level.

* `funR_mem_lev`: finite sequences of members of the level at a limit ordinal above `ω` are
  members of that level (the length is a natural number of the model).

This `κ` is the next cardinal of the constructible sets after `ν`. The property (sub) for it is
condensation in its sharp form, and is not proved.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- `c` is the pair of the pairs `⟨s', t₁⟩` and `⟨t₂, t₃⟩`, which are members of `S`. -/
def Code4 {V : Type} [SetStructure V] (c s' t₁ t₂ t₃ S : V) : Prop :=
  ∃ p₁, p₁ ∈ S ∧ ∃ p₂, p₂ ∈ S ∧ (IsOp p₁ s' t₁ ∧ (IsOp p₂ t₂ t₃ ∧ IsOp c p₁ p₂))

def code4B : BDef (k := 6) (fun V _ v ↦ Code4 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 5 (BDef.bex 6 ((isOpB.comp ![1, 3, 4]).and ((isOpB.comp ![0, 5, 6]).and
    (isOpB.comp ![2, 1, 0]))))).congr fun _ _ _ => Iff.rfl

/-- **The codes of the members of the next level.** `c` is a code of `x`, given codes `G` of
the members of the level `L` with order `lt`: the empty set for `L` itself; the pair of the
empty set and a code for a member of `L`; the pair of two pairs of codes of the parameters of
a definition of `x` over `L`. -/
def CdR {V : Type} [SetStructure V] (x c G L lt S : V) : Prop :=
  (x = L ∧ ∀ w, w ∈ c → False) ∨
  ((x ∈ L ∧ ∃ g, g ∈ S ∧ ∃ e, e ∈ S ∧ ((∀ w, w ∈ e → False) ∧ (Pr G x g ∧ IsOp c e g))) ∨
    (∃ s, s ∈ L ∧ ∃ y₁, y₁ ∈ L ∧ ∃ y₂, y₂ ∈ L ∧ ∃ y₃, y₃ ∈ L ∧ ∃ s', s' ∈ S ∧ ∃ t₁, t₁ ∈ S ∧
      ∃ t₂, t₂ ∈ S ∧ ∃ t₃, t₃ ∈ S ∧ (Pr G s s' ∧ (Pr G y₁ t₁ ∧ (Pr G y₂ t₂ ∧ (Pr G y₃ t₃ ∧
        (IsD L lt s y₁ y₂ y₃ x ∧ Code4 c s' t₁ t₂ t₃ S)))))))

def cdRB : BDef (k := 6) (fun V _ v ↦ CdR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (((BDef.eq 0 3).and (BDef.ball 1 BDef.fls)).or
    (((BDef.mem 0 3).and (BDef.bex 5 (BDef.bex 6 ((BDef.ball 0 BDef.fls).and
      ((prB.comp ![4, 2, 1]).and (isOpB.comp ![3, 0, 1])))))).or
    (BDef.bex 3 (BDef.bex 4 (BDef.bex 5 (BDef.bex 6 (BDef.bex 9 (BDef.bex 10 (BDef.bex 11
      (BDef.bex 12 ((prB.comp ![10, 7, 3]).and ((prB.comp ![10, 6, 2]).and
        ((prB.comp ![10, 5, 1]).and ((prB.comp ![10, 4, 0]).and
          ((isDB.comp ![11, 12, 7, 6, 5, 4, 8]).and
            (code4B.comp ![9, 3, 2, 1, 0, 13])))))))))))))))).congr fun _ _ _ => Iff.rfl

/-- **The relation that maps a level into `S` when a small set `B` is unbounded in it.** `z`
is sent to the pair of a code of some `v ∈ B` that comes after `z`, and the value at `z` of the
least one-to-one relation from the set `A` of the predecessors of `v` into `S`. Here `T` is the
level, `Q` gives its order, `K₂` bounds the sets `A`, `K₁` bounds the relations and `Q₁` gives
its order, and `E` codes the members of `B`. -/
def JRel {V : Type} [SetStructure V] (z c T S B Q K₂ K₁ Q₁ E : V) : Prop :=
  ∃ v, v ∈ B ∧ (Pr Q z v ∧ ∃ A, A ∈ K₂ ∧
    (((∀ z', z' ∈ A → z' ∈ T ∧ Pr Q z' v) ∧ (∀ z', z' ∈ T → Pr Q z' v → z' ∈ A)) ∧
      ∃ j, j ∈ K₁ ∧ (InjV j A S ∧ ((∀ j', j' ∈ K₁ → InjV j' A S → ¬Pr Q₁ j' j) ∧
        ∃ c₁, c₁ ∈ S ∧ (Pr E v c₁ ∧ ∃ c₂, c₂ ∈ S ∧ (Pr j z c₂ ∧ IsOp c c₁ c₂))))))

def jrelB : BDef (k := 10) (fun V _ v ↦
    JRel (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  (BDef.bex 4 ((prB.comp ![6, 1, 0]).and (BDef.bex 7
    (((BDef.ball 0 ((BDef.mem 0 5).and (prB.comp ![8, 0, 2]))).and
      (BDef.ball 4 ((prB.comp ![8, 0, 2]).imp (BDef.mem 0 1)))).and
    (BDef.bex 9 ((injVB.comp ![0, 1, 6]).and
      ((BDef.ball 10 ((injVB.comp ![0, 2, 7]).imp (prB.comp ![12, 0, 1]).not)).and
        (BDef.bex 6 ((prB.comp ![13, 3, 0]).and
          (BDef.bex 7 ((prB.comp ![2, 5, 0]).and (isOpB.comp ![6, 1, 0])))))))))))).congr
    fun _ _ _ => Iff.rfl

/-- `v` is the least set that `R` relates `u` to, among the members of `T` in the order given
by `Q`. -/
def WitR {V : Type} [SetStructure V] (u v T R Q : V) : Prop :=
  Pr R u v ∧ ∀ v', v' ∈ T → Pr Q v' v → ¬Pr R u v'

def witRB : BDef (k := 5) (fun V _ v ↦ WitR (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((prB.comp ![3, 0, 1]).and
    (BDef.ball 2 ((prB.comp ![5, 0, 2]).imp (prB.comp ![4, 1, 0]).not))).congr
    fun _ _ _ => Iff.rfl

section card

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `A` maps one-to-one into `S` by a constructible relation. -/
def LInj (A S : V) : Prop := ∃ F : V, Con F ∧ InjS F A S

omit [Nonempty V] hH in
theorem injS_dom_mono {F A A' B : V} (h : InjS F A B) (hA : ∀ z, z ∈ A' → z ∈ A) :
    InjS F A' B :=
  ⟨fun u hu => h.1 u (hA u hu), fun u u' v hu hu' => h.2 u u' v (hA u hu) (hA u' hu')⟩

/-- **For the members of a level the condition is bounded**: the relation can be taken in a
fixed level. -/
theorem linj_bound {S lam : V} (hS : Con S) (hl : Lim lam) (hSl : ∀ v, v ∈ S → v ∈ Lev lam) :
    ∃ κ₁ : V, Lim κ₁ ∧ ∀ A : V, Con A → (∀ u, u ∈ A → u ∈ Lev lam) →
      (LInj A S ↔ ∃ F, F ∈ Lev κ₁ ∧ InjV F A S) := by
  have hbig := lim_big hl
  obtain ⟨κ₀, hκ₀, hbound⟩ := bound_exists (big_scn hbig 4)
  obtain ⟨κ₁, hκ₁, h01⟩ := exists_lim hκ₀
  refine ⟨κ₁, hκ₁, fun A hA hAl => ⟨?_, ?_⟩⟩
  · rintro ⟨F, hF, hinj⟩
    obtain ⟨F', hF', hsp⟩ := exists_trim hF hA hS
    have h1 : InjS F' A S := injS_trim (injV_of_injS hinj) hsp
    obtain ⟨δ, hδ, hFδ⟩ := hF'
    refine ⟨F', lev_mono hκ₁.1 h01 _ (hbound δ F' hδ hFδ (fun z hz => ?_)), injV_of_injS h1⟩
    obtain ⟨-, u, hu, v, hv, rfl⟩ := (hsp z).mp hz
    exact kp_mem_lev hbig (hAl u hu) (hSl v hv)
  · rintro ⟨F, hFκ, hinj⟩
    obtain ⟨F', hF', hsp⟩ := exists_trim ⟨κ₁, hκ₁.1, hFκ⟩ hA hS
    exact ⟨F', hF', injS_trim hinj hsp⟩

/-- **The next height.** For a constructible set `S` there is a least ordinal `κ` such that the
level at `κ` does not map one-to-one into `S` by a constructible relation. -/
theorem lnext_exists {S : V} (hS : Con S) :
    ∃ κ : V, Ord κ ∧ ¬LInj (Lev κ) S ∧ ∀ δ, δ ∈ κ → LInj (Lev δ) S := by
  obtain ⟨K, hK⟩ := next_exists S
  have hKo : Ord K := ord_of_ordS hK.1
  obtain ⟨γ₀, hγ₀, hSγ₀⟩ := hS
  obtain ⟨lam, hl, hKl, hγl⟩ := exists_lim2 hKo hγ₀
  have hSl : ∀ v, v ∈ S → v ∈ Lev lam :=
    fun v hv => lev_mono hl.1 hγl v (lev_tr hγ₀ S hSγ₀ v hv)
  obtain ⟨κ₁, hκ₁, hkey⟩ := linj_bound ⟨γ₀, hγ₀, hSγ₀⟩ hl hSl
  obtain ⟨Fh, hFh⟩ := exists_hier hl.1
  let Z : V := sepB (k := 4) (BDef.bex 2 ((levAtB.comp ![2, 1, 0]).and
    (BDef.bex 4 (injVB.comp ![0, 1, 6])).not)) (sc lam) ![Fh, Lev (sc lam), Lev κ₁, S]
  have hZ : ∀ δ, δ ∈ Z ↔ δ ∈ sc lam ∧ ∃ A, A ∈ Lev (sc lam) ∧
      (LevAt Fh δ A ∧ ¬∃ F, F ∈ Lev κ₁ ∧ InjV F A S) := fun δ => mem_sepB _ _ _ δ
  have hZ' : ∀ δ, δ ∈ sc lam → (δ ∈ Z ↔ ¬LInj (Lev δ) S) := by
    intro δ hδ
    have hδo := ord_mem (ord_sc hl.1) hδ
    have hsub : ∀ u, u ∈ Lev δ → u ∈ Lev lam := lev_sub_of_le hδo hl.1 (mem_sc.mp hδ)
    rw [hZ, hkey (Lev δ) (con_lev hδo) hsub]
    constructor
    · rintro ⟨-, A, -, hA, hn⟩
      rw [(levAt_lev hl.1 hFh hδ).mp hA] at hn
      exact hn
    · intro hn
      exact ⟨hδ, Lev δ, lev_mem (ord_sc hl.1) hδ, (levAt_lev hl.1 hFh hδ).mpr rfl, hn⟩
  have hlamZ : lam ∈ Z := (hZ' lam (self_mem_sc lam)).mpr (fun h => by
    obtain ⟨F, -, hinj⟩ := h
    exact hK.2.1 ⟨F, injS_dom_mono hinj
      (fun z hz => ord_mem_lev_lim hl z (hl.1.1 K hKl z hz))⟩)
  obtain ⟨κ, hκZ, hleast⟩ :=
    ord_least Z (fun z hz => ord_mem (ord_sc hl.1) ((hZ z).mp hz).1) ⟨lam, hlamZ⟩
  have hκs : κ ∈ sc lam := ((hZ κ).mp hκZ).1
  refine ⟨κ, ord_mem (ord_sc hl.1) hκs, (hZ' κ hκs).mp hκZ, fun δ hδ => ?_⟩
  have hδs : δ ∈ sc lam := (ord_sc hl.1).1 κ hκs δ hδ
  by_contra hn
  rcases hleast δ ((hZ' δ hδs).mpr hn) with e | e
  · rw [e] at hδ
    exact mem_irrefl _ hδ
  · exact mem_asymm hδ e

/-! ### The next height is a limit ordinal -/

theorem isOp_nonempty {v a b : V} (h : IsOp v a b) : ∃ w, w ∈ v := by
  rw [isOp_iff.mp h]
  exact ⟨{a}, by simp [kp]⟩

theorem isD_unique {A lt s y₁ y₂ y₃ x x' : V} (h : IsD A lt s y₁ y₂ y₃ x)
    (h' : IsD A lt s y₁ y₂ y₃ x') : x = x' :=
  mem_ext fun z => ⟨fun hz => h'.2 z (h.1 z hz).1 (h.1 z hz).2,
    fun hz => h.2 z (h'.1 z hz).1 (h'.1 z hz).2⟩

theorem lev_sc_cases {δ x : V} (hδ : Ord δ) (hx : x ∈ Lev (sc δ)) :
    x ∈ Lev δ ∨ InDef (Lev δ) (LtS δ) x := by
  obtain ⟨β, hβ, hin⟩ := (mem_lev (ord_sc hδ)).mp hx
  rcases mem_sc.mp hβ with e | e
  · rw [e] at hin
    exact Or.inr hin
  · exact Or.inl ((mem_lev hδ).mpr ⟨β, e, hin⟩)

/-- The order of a level is a constructible set. -/
theorem con_lts {δ : V} (hδ : Big δ) : Con (LtS δ) := by
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet hδ
  obtain ⟨γ, hγ, h1, h2⟩ := con_big2 hQc (con_lev hδ.1)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef (closed_true (V := V)) (k := 2)
    (BDef.bex 2 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and (prB.comp ![3, 1, 0]))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![Q, Lev δ] (by
      intro j
      match j with
      | 0 => exact ⟨up _ h1, good_of_con hQc⟩
      | 1 => exact ⟨up _ h2, good_of_con (con_lev hδ.1)⟩)
  have hyz' : ∀ z, z ∈ y ↔ z ∈ Lev (scn 4 γ) ∧ ∃ a, a ∈ Lev δ ∧ ∃ b, b ∈ Lev δ ∧
      (IsOp z a b ∧ Pr Q a b) := hyz
  have e : y = LtS δ := mem_ext fun z => by
    rw [hyz']
    constructor
    · rintro ⟨-, a, ha, b, hb, hop, hpr⟩
      rw [isOp_iff.mp hop]
      exact pr_iff.mp ((lts_iff hδ.1).mpr ⟨ha, hb, (hQ a b ha hb).mp hpr⟩)
    · intro hz
      obtain ⟨a, b, rfl, hpr⟩ := lts_pair hδ.1 hz
      obtain ⟨ha, hb, hlt⟩ := (lts_iff hδ.1).mp hpr
      exact ⟨kp_mem_lev hγ (lev_tr hγ.1 _ h2 a ha) (lev_tr hγ.1 _ h2 b hb), a, ha, b, hb,
        isOp_kp a b, (hQ a b ha hb).mpr hlt⟩
  rw [← e]
  exact con_of_good hy

/-- A code is the code of one set only. -/
theorem cdR_inj {x x' c G L lt S : V}
    (hG : ∀ u, u ∈ L → ∀ u', u' ∈ L → ∀ v, Pr G u v → Pr G u' v → u = u')
    (h : CdR x c G L lt S) (h' : CdR x' c G L lt S) : x = x' := by
  rcases h with ⟨e, h0⟩ | ⟨hx, g, -, e, -, he, hg, hop⟩ |
    ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, s', -, t₁, -, t₂, -, t₃, -, g0, g1, g2, g3, hD,
      p₁, -, p₂, -, o1, o2, o3⟩
  · rcases h' with ⟨e', -⟩ | ⟨-, g', -, e', -, -, -, hop'⟩ |
      ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, -, -, -, -, -, q₁, -, q₂, -, -, -, o3'⟩
    · rw [e, e']
    · obtain ⟨w, hw⟩ := isOp_nonempty hop'
      exact (h0 w hw).elim
    · obtain ⟨w, hw⟩ := isOp_nonempty o3'
      exact (h0 w hw).elim
  · rcases h' with ⟨-, h0'⟩ | ⟨hx', g', -, e', -, he', hg', hop'⟩ |
      ⟨_, -, _, -, _, -, _, -, s'', -, t₁', -, _, -, _, -, -, -, -, -, -, q₁, -, q₂, -,
        o1', -, o3'⟩
    · obtain ⟨w, hw⟩ := isOp_nonempty hop
      exact (h0' w hw).elim
    · have ee := kp_inj ((isOp_iff.mp hop).symm.trans (isOp_iff.mp hop'))
      rw [← ee.2] at hg'
      exact hG x hx x' hx' g hg hg'
    · have ee := kp_inj ((isOp_iff.mp hop).symm.trans (isOp_iff.mp o3'))
      obtain ⟨w, hw⟩ := isOp_nonempty o1'
      rw [← ee.1] at hw
      exact (he w hw).elim
  · rcases h' with ⟨-, h0'⟩ | ⟨-, g', -, e', -, he', -, hop'⟩ |
      ⟨z, hz, z₁, k1, z₂, k2, z₃, k3, u', -, v₁, -, v₂, -, v₃, -, f0, f1, f2, f3, hD',
        q₁, -, q₂, -, o1', o2', o3'⟩
    · obtain ⟨w, hw⟩ := isOp_nonempty o3
      exact (h0' w hw).elim
    · have ee := kp_inj ((isOp_iff.mp o3).symm.trans (isOp_iff.mp hop'))
      obtain ⟨w, hw⟩ := isOp_nonempty o1
      rw [ee.1] at hw
      exact (he' w hw).elim
    · have ee := kp_inj ((isOp_iff.mp o3).symm.trans (isOp_iff.mp o3'))
      have e1 := kp_inj ((isOp_iff.mp o1).symm.trans (ee.1.trans (isOp_iff.mp o1')))
      have e2 := kp_inj ((isOp_iff.mp o2).symm.trans (ee.2.trans (isOp_iff.mp o2')))
      rw [← e1.1] at f0
      rw [← e1.2] at f1
      rw [← e2.1] at f2
      rw [← e2.2] at f3
      rw [← hG s hs z hz s' g0 f0, ← hG y₁ h1 z₁ k1 t₁ g1 f1, ← hG y₂ h2 z₂ k2 t₂ g2 f2,
        ← hG y₃ h3 z₃ k3 t₃ g3 f3] at hD'
      exact isD_unique hD hD'

/-- **If a level above `ω` maps one-to-one into `S` by a constructible relation, so does the
next level**, when `S` has the empty set as a member and is closed under pairs. -/
theorem linj_succ {S δ : V} (hS : Con S) (hSp : ∀ a b, a ∈ S → b ∈ S → kp a b ∈ S)
    (h0 : (∅ : V) ∈ S) (hδ : Big δ) (h : LInj (Lev δ) S) : LInj (Lev (sc δ)) S := by
  obtain ⟨G, hGc, hG⟩ := h
  have hlt := con_lts hδ
  have hscδ := ord_sc hδ.1
  obtain ⟨γ₁, g₁, a1, a2, a3⟩ := con_big3 hGc (con_lev hδ.1) hlt
  obtain ⟨γ₂, g₂, b1, b2⟩ := con_big2 hS (con_lev hscδ)
  obtain ⟨γ, hγ, c1, c2, c3, c4, c5⟩ : ∃ γ, Big γ ∧ G ∈ Lev γ ∧ Lev δ ∈ Lev γ ∧
      LtS δ ∈ Lev γ ∧ S ∈ Lev γ ∧ Lev (sc δ) ∈ Lev γ := by
    rcases ord_tri g₁.1 g₂.1 with e | e | e
    · exact ⟨γ₂, g₂, lev_mono g₂.1 e _ a1, lev_mono g₂.1 e _ a2, lev_mono g₂.1 e _ a3, b1, b2⟩
    · exact ⟨γ₁, g₁, a1, a2, a3, e ▸ b1, e ▸ b2⟩
    · exact ⟨γ₁, g₁, a1, a2, a3, lev_mono g₁.1 e _ b1, lev_mono g₁.1 e _ b2⟩
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨F, hF, hFz⟩ := sep_good_bdef (closed_true (V := V)) (k := 5)
    (BDef.bex 1 (BDef.bex 6 ((isOpB.comp ![2, 1, 0]).and (cdRB.comp ![1, 0, 4, 5, 6, 7]))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![Lev (sc δ), G, Lev δ, LtS δ, S] (by
      intro j
      match j with
      | 0 => exact ⟨up _ c5, good_of_con (con_lev hscδ)⟩
      | 1 => exact ⟨up _ c1, good_of_con hGc⟩
      | 2 => exact ⟨up _ c2, good_of_con (con_lev hδ.1)⟩
      | 3 => exact ⟨up _ c3, good_of_con hlt⟩
      | 4 => exact ⟨up _ c4, good_of_con hS⟩)
  have hFz' : ∀ z, z ∈ F ↔ z ∈ Lev (scn 4 γ) ∧ ∃ x, x ∈ Lev (sc δ) ∧ ∃ c, c ∈ S ∧
      (IsOp z x c ∧ CdR x c G (Lev δ) (LtS δ) S) := hFz
  have hto : ∀ x c, x ∈ Lev (sc δ) → c ∈ S → CdR x c G (Lev δ) (LtS δ) S → kp x c ∈ F :=
    fun x c hx hc hcd => (hFz' _).mpr ⟨kp_mem_lev hγ (lev_tr hγ.1 _ c5 x hx)
      (lev_tr hγ.1 _ c4 c hc), x, hx, c, hc, isOp_kp x c, hcd⟩
  have hfrom : ∀ x c, kp x c ∈ F → CdR x c G (Lev δ) (LtS δ) S := by
    intro x c hxc
    obtain ⟨-, x', -, c', -, hop, hcd⟩ := (hFz' _).mp hxc
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
  refine ⟨F, con_of_good hF, fun x hx => ?_, fun x x' v _ _ h1 h2 =>
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

/-- A constructible set maps one-to-one into every set that includes it, by the identity. -/
theorem linj_of_sub {A S : V} (hA : Con A) (hsub : ∀ z, z ∈ A → z ∈ S) : LInj A S := by
  obtain ⟨γ, hγ, hAγ⟩ := con_big hA
  have hγ4 := big_scn hγ 4
  obtain ⟨F, hF, hFz⟩ := sep_good_bdef (closed_true (V := V)) (k := 1)
    (BDef.bex 1 (isOpB.comp ![1, 0, 0])) (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![A]
    (fun j => by
      have e := Fin.eq_zero j
      subst e
      exact ⟨lev_scn_sub hγ.1 4 _ hAγ, good_of_con hA⟩)
  have hFz' : ∀ z, z ∈ F ↔ z ∈ Lev (scn 4 γ) ∧ ∃ a, a ∈ A ∧ IsOp z a a := hFz
  have hfrom : ∀ u v, kp u v ∈ F → u = v := by
    intro u v huv
    obtain ⟨-, a, -, hop⟩ := (hFz' _).mp huv
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
  refine ⟨F, con_of_good hF, fun u hu => ⟨u, hsub u hu, hin_rl_iff.mpr ((hFz' _).mpr
    ⟨kp_mem_lev hγ (lev_tr hγ.1 A hAγ u hu) (lev_tr hγ.1 A hAγ u hu), u, hu, isOp_kp u u⟩)⟩,
    fun u u' v _ _ h1 h2 => ?_⟩
  rw [hfrom u v (hin_rl_iff.mp h1), hfrom u' v (hin_rl_iff.mp h2)]

/-- **The next height after a limit ordinal `ν` above `ω`**: a limit ordinal `κ` above `ν` such
that the level at `κ` does not map one-to-one into the level at `ν` by a constructible
relation, and every earlier level does. -/
theorem lnext_spec {ν : V} (hν : Lim ν) (hom : (om : V) ∈ ν) :
    ∃ κ : V, Lim κ ∧ ν ∈ κ ∧ ¬LInj (Lev κ) (Lev ν) ∧ ∀ δ, δ ∈ κ → LInj (Lev δ) (Lev ν) := by
  obtain ⟨κ, hκ, hn, hall⟩ := lnext_exists (con_lev hν.1)
  have hνκ : ν ∈ κ := by
    rcases ord_tri hν.1 hκ with e | e | e
    · exact e
    · exact absurd (linj_of_sub (con_lev hν.1) (fun z hz => hz)) (e ▸ hn)
    · exact absurd (linj_of_sub (con_lev hκ) (lev_mono hν.1 e)) hn
  have hSp : ∀ a b, a ∈ Lev ν → b ∈ Lev ν → kp a b ∈ Lev ν := by
    intro a b ha hb
    obtain ⟨δ, hδ, hδb, h1, h2⟩ := lev_lim_exists2 hν hom ha hb
    exact lev_mono hν.1 (hν.2.2 _ (hν.2.2 _ (hν.2.2 _ (hν.2.2 δ hδ)))) _ (kp_mem_lev hδb h1 h2)
  refine ⟨κ, ⟨hκ, ⟨ν, hνκ⟩, fun δ hδ => ?_⟩, hνκ, hn, hall⟩
  rcases ord_sc_le (ord_mem hκ hδ) hκ hδ with e | e
  · exfalso
    have hνδ : ν = δ ∨ ν ∈ δ := mem_sc.mp (e ▸ hνκ)
    have hδb : Big δ := ⟨ord_mem hκ hδ, fun n hn' => by
      rcases hνδ with e' | e'
      · rw [← e']
        exact (lim_big hν).2 n hn'
      · exact (ord_mem hκ hδ).1 ν e' n ((lim_big hν).2 n hn')⟩
    have := linj_succ (con_lev hν.1) hSp (empty_mem_lev hν.1 hν.2.1) hδb (hall δ hδ)
    rw [e] at this
    exact hn this
  · exact e

/-! ### The next height is regular -/

theorem kp_mem_lev_lim {ν a b : V} (hν : Lim ν) (hom : (om : V) ∈ ν) (ha : a ∈ Lev ν)
    (hb : b ∈ Lev ν) : kp a b ∈ Lev ν := by
  obtain ⟨δ, hδ, hδb, h1, h2⟩ := lev_lim_exists2 hν hom ha hb
  exact lev_mono hν.1 (hν.2.2 _ (hν.2.2 _ (hν.2.2 _ (hν.2.2 δ hδ)))) _ (kp_mem_lev hδb h1 h2)

/-- **The next height is regular.** Let `κ` be the next height after `ν`. A constructible set
of members of the level at `κ` that maps one-to-one into the level at `ν` by a constructible
relation is included in an earlier level. Otherwise the whole level at `κ` would map into the
level at `ν`: each member comes before some member `v` of the set, and the predecessors of `v`
map into the level at `ν` by a least relation. -/
theorem lnext_reg {ν κ : V} (hν : Lim ν) (hom : (om : V) ∈ ν) (hκ : Lim κ) (hνκ : ν ∈ κ)
    (hn : ¬LInj (Lev κ) (Lev ν)) (hall : ∀ δ, δ ∈ κ → LInj (Lev δ) (Lev ν))
    {B : V} (hB : Con B) (hBκ : ∀ v, v ∈ B → v ∈ Lev κ) (hBS : LInj B (Lev ν)) :
    ∃ δ, δ ∈ κ ∧ ∀ v, v ∈ B → v ∈ Lev δ := by
  by_contra hcon
  have hunb : ∀ δ, δ ∈ κ → ∃ v, v ∈ B ∧ v ∉ Lev δ := by
    intro δ hδ
    by_contra h
    exact hcon ⟨δ, hδ, fun v hv => by
      by_contra hv'
      exact h ⟨v, hv, hv'⟩⟩
  apply hn
  have hSκ : ∀ c, c ∈ Lev ν → c ∈ Lev κ := lev_mono hκ.1 hνκ
  have hSp : ∀ a b, a ∈ Lev ν → b ∈ Lev ν → kp a b ∈ Lev ν :=
    fun a b ha hb => kp_mem_lev_lim hν hom ha hb
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hκ)
  obtain ⟨κ₁, hκ₁, hkey⟩ := linj_bound (con_lev hν.1) hκ hSκ
  obtain ⟨Q₁, hQ₁c, hQ₁⟩ := exists_ltSet (lim_big hκ₁)
  obtain ⟨κ₂, hκ₂, hb₂⟩ := bound_exists (lim_big hκ)
  obtain ⟨E, hEc, hE⟩ := hBS
  -- the predecessors of a member of the level, and a one-to-one relation from them
  have hseg : ∀ v, v ∈ Lev κ → ∃ A, A ∈ Lev κ₂ ∧ (∀ z', z' ∈ A ↔ z' ∈ Lev κ ∧ LtL z' v) ∧
      ∃ j, j ∈ Lev κ₁ ∧ InjV j A (Lev ν) := by
    intro v hv
    have hvc : Con v := ⟨κ, hκ.1, hv⟩
    obtain ⟨γ, hγ, g1, g2, g3⟩ := con_big3 (con_lev hκ.1) hQc hvc
    obtain ⟨A, hA, hAz⟩ := sep_good_bdef (closed_true (V := V)) (k := 3)
      ((BDef.mem 0 1).and (prB.comp ![2, 0, 3])) (good_of_con (con_lev hγ.1)) (lev_tr hγ.1)
      ![Lev κ, Q, v] (by
        intro i
        match i with
        | 0 => exact ⟨g1, good_of_con (con_lev hκ.1)⟩
        | 1 => exact ⟨g2, good_of_con hQc⟩
        | 2 => exact ⟨g3, good_of_con hvc⟩)
    have hAz' : ∀ z', z' ∈ A ↔ z' ∈ Lev γ ∧ (z' ∈ Lev κ ∧ Pr Q z' v) := hAz
    have hA1 : ∀ z', z' ∈ A ↔ z' ∈ Lev κ ∧ LtL z' v := fun z' =>
      ⟨fun h => ⟨((hAz' z').mp h).2.1,
        (hQ z' v ((hAz' z').mp h).2.1 hv).mp ((hAz' z').mp h).2.2⟩,
       fun h => (hAz' z').mpr ⟨lev_tr hγ.1 _ g1 z' h.1, h.1, (hQ z' v h.1 hv).mpr h.2⟩⟩
    have hAκ : ∀ z', z' ∈ A → z' ∈ Lev κ := fun z' h => ((hA1 z').mp h).1
    obtain ⟨δ, hδ, hAδ⟩ := con_of_good hA
    refine ⟨A, hb₂ δ A hδ hAδ hAκ, hA1, ?_⟩
    obtain ⟨β, hβ, hc⟩ := ltL_cover hκ.1 hv
    obtain ⟨G, hGc, hG⟩ := hall (sc β) (hκ.2.2 β hβ)
    exact (hkey A ⟨δ, hδ, hAδ⟩ hAκ).mp
      ⟨G, hGc, injS_dom_mono hG (fun z' h => hc z' ((hA1 z').mp h).2)⟩
  -- a level that has all the parameters
  have gT := good_of_con (con_lev hκ.1)
  obtain ⟨γ, hγ, -, hTγ, hl⟩ := good_common gT [Lev ν, B, Q, Lev κ₂, Lev κ₁, Q₁, E] (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with e | e | e | e | e | e | e
    · rw [e]; exact good_of_con (con_lev hν.1)
    · rw [e]; exact good_of_con hB
    · rw [e]; exact good_of_con hQc
    · rw [e]; exact good_of_con (con_lev hκ₂)
    · rw [e]; exact good_of_con (con_lev hκ₁.1)
    · rw [e]; exact good_of_con hQ₁c
    · rw [e]; exact good_of_con hEc)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨J, hJ, hJz⟩ := sep_good_bdef (closed_true (V := V)) (k := 8)
    (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
      (jrelB.comp ![1, 0, 3, 4, 5, 6, 7, 8, 9, 10]))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1)
    ![Lev κ, Lev ν, B, Q, Lev κ₂, Lev κ₁, Q₁, E] (by
      intro i
      match i with
      | 0 => exact ⟨up _ hTγ, gT⟩
      | 1 => exact ⟨up _ (hl (Lev ν) (by simp)), good_of_con (con_lev hν.1)⟩
      | 2 => exact ⟨up _ (hl B (by simp)), good_of_con hB⟩
      | 3 => exact ⟨up _ (hl Q (by simp)), good_of_con hQc⟩
      | 4 => exact ⟨up _ (hl (Lev κ₂) (by simp)), good_of_con (con_lev hκ₂)⟩
      | 5 => exact ⟨up _ (hl (Lev κ₁) (by simp)), good_of_con (con_lev hκ₁.1)⟩
      | 6 => exact ⟨up _ (hl Q₁ (by simp)), good_of_con hQ₁c⟩
      | 7 => exact ⟨up _ (hl E (by simp)), good_of_con hEc⟩)
  have hJz' : ∀ p, p ∈ J ↔ p ∈ Lev (scn 4 γ) ∧ ∃ z, z ∈ Lev κ ∧ ∃ c, c ∈ Lev ν ∧
      (IsOp p z c ∧ JRel z c (Lev κ) (Lev ν) B Q (Lev κ₂) (Lev κ₁) Q₁ E) := hJz
  have hto : ∀ z c, z ∈ Lev κ → c ∈ Lev ν →
      JRel z c (Lev κ) (Lev ν) B Q (Lev κ₂) (Lev κ₁) Q₁ E → kp z c ∈ J :=
    fun z c hz hc h => (hJz' _).mpr ⟨kp_mem_lev hγ (lev_tr hγ.1 _ hTγ z hz)
      (lev_tr hγ.1 _ (hl (Lev ν) (by simp)) c hc), z, hz, c, hc, isOp_kp z c, h⟩
  have hfrom : ∀ z c, kp z c ∈ J → JRel z c (Lev κ) (Lev ν) B Q (Lev κ₂) (Lev κ₁) Q₁ E := by
    intro z c hzc
    obtain ⟨-, z', -, c', -, hop, hj⟩ := (hJz' _).mp hzc
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact hj
  refine ⟨J, con_of_good hJ, fun z hz => ?_, fun z z' c hz hz' h1 h2 => ?_⟩
  · obtain ⟨βz, hβz, rz⟩ := rkL_exists hκ.1 hz
    obtain ⟨v, hvB, hvn⟩ := hunb (sc βz) (hκ.2.2 βz hβz)
    have hvκ := hBκ v hvB
    obtain ⟨βv, -, rv⟩ := rkL_exists hκ.1 hvκ
    have hlt : LtL z v := by
      refine (ltL_iff_rk rz rv).mpr (Or.inl ?_)
      have h1 : βv ∉ sc βz := fun h => hvn ((rkL_mem rv (ord_sc rz.1)).mpr h)
      rcases ord_tri rz.1 rv.1 with e | e | e
      · exact e
      · exact absurd (mem_sc.mpr (Or.inl e.symm)) h1
      · exact absurd (mem_sc.mpr (Or.inr e)) h1
    obtain ⟨A, hA₂, hA1, j₀, hj₀, hj₀i⟩ := hseg v hvκ
    let Zj : V := sepB (k := 2) (injVB.comp ![0, 1, 2]) (Lev κ₁) ![A, Lev ν]
    have hZj : ∀ j, j ∈ Zj ↔ j ∈ Lev κ₁ ∧ InjV j A (Lev ν) := fun j => mem_sepB _ _ _ j
    obtain ⟨j, hjZ, hjmin⟩ := ltL_least hκ₁.1 Zj (fun j hj => ((hZj j).mp hj).1)
      ⟨j₀, (hZj j₀).mpr ⟨hj₀, hj₀i⟩⟩
    obtain ⟨hjκ, hji⟩ := (hZj j).mp hjZ
    obtain ⟨c₁, hc₁, hEc₁⟩ := hE.1 v hvB
    obtain ⟨c₂, hc₂, hjc₂⟩ := hji.1 z ((hA1 z).mpr ⟨hz, hlt⟩)
    refine ⟨kp c₁ c₂, hSp _ _ hc₁ hc₂, hin_rl_iff.mpr (hto z _ hz (hSp _ _ hc₁ hc₂) ?_)⟩
    exact ⟨v, hvB, (hQ z v hz hvκ).mpr hlt, A, hA₂,
      ⟨fun z' h => ⟨((hA1 z').mp h).1, (hQ z' v ((hA1 z').mp h).1 hvκ).mpr ((hA1 z').mp h).2⟩,
        fun z' h1 h2 => (hA1 z').mpr ⟨h1, (hQ z' v h1 hvκ).mp h2⟩⟩,
      j, hjκ, hji,
      fun j' hj' hji' hpr => hjmin j' ((hZj j').mpr ⟨hj', hji'⟩) ((hQ₁ j' j hj' hjκ).mp hpr),
      c₁, hc₁, pr_iff.mpr (hin_rl_iff.mp hEc₁), c₂, hc₂, hjc₂, isOp_kp c₁ c₂⟩
  · obtain ⟨v, hvB, hQz, A, -, ⟨hA_1, hA_2⟩, j, hjκ, hji, hjmin, c₁, -, hEc₁, c₂, hc₂, hjc₂, hop⟩ :=
      hfrom z c (hin_rl_iff.mp h1)
    obtain ⟨v', hvB', hQz', A', -, ⟨hA'_1, hA'_2⟩, j', hjκ', hji', hjmin', c₁', -, hEc₁', c₂', -,
      hjc₂', hop'⟩ := hfrom z' c (hin_rl_iff.mp h2)
    obtain ⟨e1, e2⟩ := kp_inj ((isOp_iff.mp hop).symm.trans (isOp_iff.mp hop'))
    rw [← e1] at hEc₁'
    rw [← e2] at hjc₂'
    have ev : v = v' := hE.2 v v' c₁ hvB hvB' (hin_rl_iff.mpr (pr_iff.mp hEc₁))
      (hin_rl_iff.mpr (pr_iff.mp hEc₁'))
    rw [← ev] at hA'_1 hA'_2 hQz'
    have eA : A = A' := mem_ext fun w =>
      ⟨fun hw => hA'_2 w (hA_1 w hw).1 (hA_1 w hw).2,
        fun hw => hA_2 w (hA'_1 w hw).1 (hA'_1 w hw).2⟩
    rw [← eA] at hji' hjmin' hA'_2
    have ej : j = j' := by
      rcases ltL_tri hκ₁.1 hjκ hjκ' with e | e | e
      · exact absurd ((hQ₁ j j' hjκ hjκ').mpr e) (hjmin' j hjκ hji)
      · exact e
      · exact absurd ((hQ₁ j' j hjκ' hjκ).mpr e) (hjmin j' hjκ' hji')
    rw [← ej] at hjc₂'
    exact hji.2 z (hA_2 z hz hQz) z' (hA'_2 z' hz' hQz') c₂ hc₂ hjc₂ hjc₂'

/-! ### Bounded relations -/

/-- **The second closure property of `Full` holds at the next height.** The least sets that
the relation relates the members of `a` to form a constructible set that maps one-to-one into
the level at `ν`, so it is included in an earlier level by `lnext_reg`. -/
theorem lnext_bd {ν κ : V} (hν : Lim ν) (hom : (om : V) ∈ ν) (hκ : Lim κ) (hνκ : ν ∈ κ)
    (hn : ¬LInj (Lev κ) (Lev ν)) (hall : ∀ δ, δ ∈ κ → LInj (Lev δ) (Lev ν))
    {a R : V} (ha : a ∈ Lev κ) (hR : Con R)
    (htot : ∀ u, u ∈ a → ∃ v, v ∈ Lev κ ∧ kp u v ∈ R) :
    ∃ b, b ∈ Lev κ ∧ ∀ u, u ∈ a → ∃ v, v ∈ b ∧ kp u v ∈ R := by
  have homκ : (om : V) ∈ κ := hκ.1.1 ν hνκ om hom
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hκ)
  obtain ⟨δ₀, hδ₀, hδ₀b, haδ₀⟩ := lev_lim_exists hκ homκ ha
  obtain ⟨G₀, hG₀c, hG₀⟩ := hall δ₀ hδ₀
  have hac : Con a := ⟨κ, hκ.1, ha⟩
  have haδ : ∀ u, u ∈ a → u ∈ Lev δ₀ := fun u hu => lev_tr hδ₀b.1 a haδ₀ u hu
  have hwit : ∀ u, u ∈ a → ∃ v, v ∈ Lev κ ∧ WitR u v (Lev κ) R Q := by
    intro u hu
    let Wu : V := sepB (k := 2) (prB.comp ![1, 2, 0]) (Lev κ) ![R, u]
    have hWu : ∀ v, v ∈ Wu ↔ v ∈ Lev κ ∧ Pr R u v := fun v => mem_sepB _ _ _ v
    obtain ⟨v₀, hv₀, hr₀⟩ := htot u hu
    obtain ⟨m, hm, hmin⟩ := ltL_least hκ.1 Wu (fun v hv => ((hWu v).mp hv).1)
      ⟨v₀, (hWu v₀).mpr ⟨hv₀, pr_iff.mpr hr₀⟩⟩
    obtain ⟨hmκ, hmR⟩ := (hWu m).mp hm
    exact ⟨m, hmκ, hmR, fun v' hv' hpr hR' =>
      hmin v' ((hWu v').mpr ⟨hv', hR'⟩) ((hQ v' m hv' hmκ).mp hpr)⟩
  have hwuniq : ∀ u v v', v ∈ Lev κ → v' ∈ Lev κ → WitR u v (Lev κ) R Q →
      WitR u v' (Lev κ) R Q → v = v' := by
    intro u v v' hv hv' h h'
    rcases ltL_tri hκ.1 hv hv' with e | e | e
    · exact absurd h.1 (h'.2 v hv ((hQ v v' hv hv').mpr e))
    · exact e
    · exact absurd h'.1 (h.2 v' hv' ((hQ v' v hv' hv).mpr e))
  have gT := good_of_con (con_lev hκ.1)
  obtain ⟨γ, hγ, -, hTγ, hl⟩ := good_common gT [Lev ν, a, R, Q, G₀] (by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with e | e | e | e | e
    · rw [e]; exact good_of_con (con_lev hν.1)
    · rw [e]; exact good_of_con hac
    · rw [e]; exact good_of_con hR
    · rw [e]; exact good_of_con hQc
    · rw [e]; exact good_of_con hG₀c)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨B, hBg, hBz⟩ := sep_good_bdef (closed_true (V := V)) (k := 4)
    ((BDef.mem 0 1).and (BDef.bex 2 (witRB.comp ![0, 1, 2, 4, 5])))
    (good_of_con (con_lev hγ.1)) (lev_tr hγ.1) ![Lev κ, a, R, Q] (by
      intro i
      match i with
      | 0 => exact ⟨hTγ, gT⟩
      | 1 => exact ⟨hl a (by simp), good_of_con hac⟩
      | 2 => exact ⟨hl R (by simp), good_of_con hR⟩
      | 3 => exact ⟨hl Q (by simp), good_of_con hQc⟩)
  have hBz' : ∀ v, v ∈ B ↔ v ∈ Lev γ ∧ (v ∈ Lev κ ∧ ∃ u, u ∈ a ∧ WitR u v (Lev κ) R Q) := hBz
  obtain ⟨E, hEg, hEz⟩ := sep_good_bdef (closed_true (V := V)) (k := 6)
    (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and (BDef.bex 5
      ((witRB.comp ![0, 2, 4, 7, 8]).and (prB.comp ![9, 0, 1]))))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![Lev κ, Lev ν, a, R, Q, G₀] (by
      intro i
      match i with
      | 0 => exact ⟨up _ hTγ, gT⟩
      | 1 => exact ⟨up _ (hl (Lev ν) (by simp)), good_of_con (con_lev hν.1)⟩
      | 2 => exact ⟨up _ (hl a (by simp)), good_of_con hac⟩
      | 3 => exact ⟨up _ (hl R (by simp)), good_of_con hR⟩
      | 4 => exact ⟨up _ (hl Q (by simp)), good_of_con hQc⟩
      | 5 => exact ⟨up _ (hl G₀ (by simp)), good_of_con hG₀c⟩)
  have hEz' : ∀ p, p ∈ E ↔ p ∈ Lev (scn 4 γ) ∧ ∃ v, v ∈ Lev κ ∧ ∃ c, c ∈ Lev ν ∧
      (IsOp p v c ∧ ∃ u, u ∈ a ∧ (WitR u v (Lev κ) R Q ∧ Pr G₀ u c)) := hEz
  have hEfrom : ∀ v c, kp v c ∈ E → ∃ u, u ∈ a ∧ (WitR u v (Lev κ) R Q ∧ Pr G₀ u c) := by
    intro v c hvc
    obtain ⟨-, v', -, c', -, hop, hu⟩ := (hEz' _).mp hvc
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact hu
  have hBκ : ∀ v, v ∈ B → v ∈ Lev κ := fun v hv => ((hBz' v).mp hv).2.1
  have hBS : LInj B (Lev ν) := by
    refine ⟨E, con_of_good hEg, fun v hv => ?_, fun v v' c hv hv' h1 h2 => ?_⟩
    · obtain ⟨-, hvκ, u, hu, hw⟩ := (hBz' v).mp hv
      obtain ⟨c, hc, hrc⟩ := hG₀.1 u (haδ u hu)
      exact ⟨c, hc, hin_rl_iff.mpr ((hEz' _).mpr ⟨kp_mem_lev hγ (lev_tr hγ.1 _ hTγ v hvκ)
        (lev_tr hγ.1 _ (hl (Lev ν) (by simp)) c hc), v, hvκ, c, hc, isOp_kp v c, u, hu, hw,
        pr_iff.mpr (hin_rl_iff.mp hrc)⟩)⟩
    · obtain ⟨u, hu, hw, hg⟩ := hEfrom v c (hin_rl_iff.mp h1)
      obtain ⟨u', hu', hw', hg'⟩ := hEfrom v' c (hin_rl_iff.mp h2)
      have eu : u = u' := hG₀.2 u u' c (haδ u hu) (haδ u' hu')
        (hin_rl_iff.mpr (pr_iff.mp hg)) (hin_rl_iff.mpr (pr_iff.mp hg'))
      rw [← eu] at hw'
      exact hwuniq u v v' (hBκ v hv) (hBκ v' hv') hw hw'
  obtain ⟨δ, hδ, hBδ⟩ := lnext_reg hν hom hκ hνκ hn hall (con_of_good hBg) hBκ hBS
  refine ⟨Lev δ, lev_mem hκ.1 hδ, fun u hu => ?_⟩
  obtain ⟨v, hvκ, hw⟩ := hwit u hu
  exact ⟨v, hBδ v ((hBz' v).mpr ⟨lev_tr hγ.1 _ hTγ v hvκ, hvκ, u, hu, hw⟩), pr_iff.mp hw.1⟩

/-- **The next height satisfies `Full` if it has the first closure property**: every
constructible subset of a member of its level is a member of its level. -/
theorem full_of_sub {ν κ : V} (hν : Lim ν) (hom : (om : V) ∈ ν) (hκ : Lim κ) (hνκ : ν ∈ κ)
    (hn : ¬LInj (Lev κ) (Lev ν)) (hall : ∀ δ, δ ∈ κ → LInj (Lev δ) (Lev ν))
    (hsub : ∀ a x : V, a ∈ Lev κ → Con x → (∀ z, z ∈ x → z ∈ a) → x ∈ Lev κ) : Full κ :=
  ⟨hκ, hκ.1.1 ν hνκ om hom, hsub,
    fun _ _ ha hR htot => lnext_bd hν hom hκ hνκ hn hall ha hR htot⟩

/-! ### Finite sequences -/

/-- **Finite sequences of members of the level at a limit ordinal above `ω` are members of that
level.** The length is a natural number of the model, so the proof is by induction on it, for a
bounded statement. -/
theorem funR_mem_lev {ν : V} (hν : Lim ν) (hom : (om : V) ∈ ν) :
    ∀ n, n ∈ (om : V) → ∀ f, FunR f n (Lev ν) → f ∈ Lev ν := by
  let P : V := ℘ (prodS (om : V) (Lev ν))
  have hP : ∀ n, n ∈ (om : V) → ∀ f, FunR f n (Lev ν) → f ∈ P := by
    intro n hn f hf
    refine mem_power_iff.mpr fun p hp => ?_
    obtain ⟨i, hi, a, ha, hop⟩ := hf.1 p hp
    exact mem_prodS.mpr ⟨i, (ord_om (V := V)).1 n hn i hi, a, ha, isOp_iff.mp hop⟩
  have h0 : ∀ f, f ∈ P → FunR f (∅ : V) (Lev ν) → f ∈ Lev ν := by
    intro f _ hf
    have e : f = ∅ := mem_ext fun p => ⟨fun hp => by
      obtain ⟨i, hi, -⟩ := hf.1 p hp
      exact absurd hi (by simp), fun hp => absurd hp (by simp)⟩
    rw [e]
    exact empty_mem_lev hν.1 hν.2.1
  have hs : ∀ n, n ∈ (om : V) → (∀ f, f ∈ P → FunR f n (Lev ν) → f ∈ Lev ν) →
      ∀ f, f ∈ P → FunR f (sc n) (Lev ν) → f ∈ Lev ν := by
    intro n hn ih f _ hf
    let g : V := sepB (k := 1) (BDef.bex 1 (hasFstB.comp ![1, 0])) f ![n]
    have hg : ∀ p, p ∈ g ↔ p ∈ f ∧ ∃ i, i ∈ n ∧ HasFst p i := fun p => mem_sepB _ _ _ p
    have hfst : ∀ p i a : V, IsOp p i a → HasFst p i := by
      intro p i a hop
      rw [isOp_iff.mp hop]
      exact ⟨({i, a} : V), by simp [kp], a, by simp, isOp_kp i a⟩
    have hgf : FunR g n (Lev ν) := by
      refine ⟨fun p hp => ?_, fun i hi => ?_, fun p hp q hq i hi a ha b hb h1 h2 => ?_⟩
      · obtain ⟨hpf, i, hi, _, _, _, _, hop⟩ := (hg p).mp hp
        obtain ⟨i', -, a, ha, hop'⟩ := hf.1 p hpf
        have e := kp_inj ((isOp_iff.mp hop).symm.trans (isOp_iff.mp hop'))
        rw [← e.1] at hop'
        exact ⟨i, hi, a, ha, hop'⟩
      · obtain ⟨p, hp, a, ha, hop⟩ := hf.2.1 i (mem_sc.mpr (Or.inr hi))
        exact ⟨p, (hg p).mpr ⟨hp, i, hi, hfst p i a hop⟩, a, ha, hop⟩
      · exact hf.2.2 p ((hg p).mp hp).1 q ((hg q).mp hq).1 i (mem_sc.mpr (Or.inr hi)) a ha b hb
          h1 h2
    have hgL : g ∈ Lev ν := ih g (hP n hn g hgf) hgf
    obtain ⟨pn, hpn, an, han, hopn⟩ := hf.2.1 n (self_mem_sc n)
    have hnL : n ∈ Lev ν := ord_mem_lev_lim hν n (hν.1.1 om hom n hn)
    have hkL : kp n an ∈ Lev ν := kp_mem_lev_lim hν hom hnL han
    have e : f = insert (kp n an) g := mem_ext fun p => by
      constructor
      · intro hp
        obtain ⟨i, hi, a, ha, hop⟩ := hf.1 p hp
        rcases mem_sc.mp hi with e | e
        · rw [e] at hop
          have ea : a = an := hf.2.2 p hp pn hpn n (self_mem_sc n) a ha an han hop hopn
          rw [isOp_iff.mp hop, ea]
          simp
        · have : p ∈ g := (hg p).mpr ⟨hp, i, e, hfst p i a hop⟩
          simp [this]
      · intro hp
        rcases (by simpa using hp : p = kp n an ∨ p ∈ g) with e | e
        · rw [e, ← isOp_iff.mp hopn]
          exact hpn
        · exact ((hg p).mp e).1
    obtain ⟨δ, hδ, hδb, h1, h2⟩ := lev_lim_exists2 hν hom hgL hkL
    rw [e]
    exact lev_mono hν.1 (hν.2.2 δ hδ) _ (adj_mem_lev hδb.1 (big_ne hδb) h1 h2)
  have key : ∀ n, n ∈ (om : V) → ∀ f, f ∈ P → FunR f n (Lev ν) → f ∈ Lev ν :=
    om_ind (k := 2) (BDef.ball 1 ((funRB.comp ![0, 1, 3]).imp (BDef.mem 0 3))) ![P, Lev ν] h0 hs
  exact fun n hn f hf => key n hn f (hP n hn f hf) hf

end card

end MH

end FFL.FirstOrder.SetTheory
