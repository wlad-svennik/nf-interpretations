module

public import MHClos

@[expose] public section

set_option autoImplicit false

/-!
# The next height is full: hosts in every model of `𝗠𝗛`

In a model of `𝗠𝗛`. Let `ν` be a limit ordinal above `ω` and `κ` the next height after `ν`
(`lnext_spec`): the least ordinal whose level does not map one-to-one into the level at `ν` by
a constructible relation. `lnext_sub`: **every constructible subset of a member of the level
at `κ` is a member of the level at `κ`.** With `full_of_sub` this gives `Full κ`
(`exists_full`), so the level at `κ` is a host (`levHost`), and the level at a smaller height
of the same kind is a closed level of it (`exists_closed_host`). There is no assumption on the
model.

The proof is condensation with a small hull. Let `x` be a constructible subset of a member of
the level at `δ`, with `δ` below `κ`, and let `x` be in the level at the limit ordinal `δ'`.
The hull of the level at `δ`, of that level and of `x` under the function of `MHCond.lean`,
inside the level at `δ'`, is taken constructible and with a constructible one-to-one coding by
members of the level at `ν` (`exists_chull`; the generators are coded because `δ` is below
`κ`). Its collapse sends the members of the hull in the level at the rank `ρ` of `x` onto the
level at an ordinal `ρ'`, and `x` is in the level after it (`main_ind`, `pi_inDef`). The
collapse preserves the order of the constructible sets, so its restriction is a constructible
set (`oiso_con`), though the collapse is not built inside the constructible sets. So the level
at `ρ'` maps one-to-one into the level at `ν` by a constructible relation, and `ρ'` is below
`κ`.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section full

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The product of two constructible sets is constructible. -/
theorem con_prodS {a b : V} (ha : Con a) (hb : Con b) : Con (prodS a b) := by
  obtain ⟨γ, hγ, h1, h2⟩ := con_big2 ha hb
  have e : prodS a b = sepB (k := 2) (BDef.bex 1 (BDef.bex 3 (isOpB.comp ![2, 1, 0])))
      (Lev (scn 4 γ)) ![a, b] := mem_ext fun p => by
    have hz : p ∈ sepB (k := 2) (BDef.bex 1 (BDef.bex 3 (isOpB.comp ![2, 1, 0])))
        (Lev (scn 4 γ)) ![a, b] ↔ p ∈ Lev (scn 4 γ) ∧ ∃ x, x ∈ a ∧ ∃ y, y ∈ b ∧ IsOp p x y :=
      mem_sepB _ _ _ p
    rw [hz, mem_prodS]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨kp_mem_lev hγ (lev_tr hγ.1 a h1 x hx) (lev_tr hγ.1 b h2 y hy), x, hx, y, hy,
        isOp_kp x y⟩
    · rintro ⟨-, x, hx, y, hy, hop⟩
      exact ⟨x, hx, y, hy, isOp_iff.mp hop⟩
  rw [e]
  exact con_sepB _ (con_lev (big_scn hγ 4).1) _ (by
    intro i
    match i with
    | 0 => exact ha
    | 1 => exact hb)

/-- **The function of the hull is a constructible set.** -/
theorem con_gSet {F δ : V} (hδ : Ord δ) (hF : IsHier F δ) :
    Con (gSet (Lev δ) F (sc δ) (LtS δ)) := by
  have hW : Con (Lev δ) := con_lev hδ
  unfold gSet
  exact con_sepB _ (con_prodS (con_prodS hW (con_prodS hW (con_prodS hW hW))) hW) _ (by
    intro i
    match i with
    | 0 => exact hW
    | 1 => exact con_hier hδ hF
    | 2 => exact con_ord (ord_sc hδ)
    | 3 => exact con_lts' hδ)

/-- **One more member.** If `A` maps one-to-one into `S` by a constructible relation, and `S`
is closed under pairs and has the empty set as a member, then so does `A` with one more
constructible member `x`. A member of `A` with code `c` gets the code `(c, c)`, and `x` the
code `(∅, (∅, ∅))`. -/
theorem linj_adj {A S x : V} (hA : Con A) (hS : Con S) (hx : Con x)
    (hSp : ∀ a b, a ∈ S → b ∈ S → kp a b ∈ S) (h0 : (∅ : V) ∈ S) (h : LInj A S) :
    ∃ G : V, Con G ∧ (∀ z, z ∈ G ↔ z ∈ A ∨ z = x) ∧ LInj G S := by
  obtain ⟨F₁, hF₁c, hF₁⟩ := h
  obtain ⟨γ, hγ, hAγ, hxγ, hSγ⟩ := con_big3 hA hx hS
  have hLc : Con (Lev γ) := con_lev hγ.1
  let cx : V := kp ∅ (kp ∅ ∅)
  have hcx : cx ∈ S := hSp _ _ h0 (hSp _ _ h0 h0)
  let G : V := sepB (k := 2) ((BDef.mem 0 1).or (BDef.eq 0 2)) (Lev γ) ![A, x]
  have hG : ∀ z, z ∈ G ↔ z ∈ A ∨ z = x := fun z =>
    (mem_sepB (k := 2) ((BDef.mem 0 1).or (BDef.eq 0 2)) (Lev γ) ![A, x] z).trans
      ⟨fun h => h.2, fun h => ⟨by
        rcases h with h | h
        · exact lev_tr hγ.1 A hAγ z h
        · rw [h]
          exact hxγ, h⟩⟩
  have hGc : Con G := con_sepB _ hLc _ (by
    intro i
    match i with
    | 0 => exact hA
    | 1 => exact hx)
  let j : V := sepB (k := 5) ((BDef.bex 1 (BDef.bex 3 (BDef.bex 4 ((prB.comp ![6, 2, 1]).and
    ((isOpB.comp ![0, 1, 1]).and (isOpB.comp ![3, 2, 0])))))).or (isOpB.comp ![0, 4, 5]))
    (Lev (scn 4 γ)) ![A, S, F₁, x, cx]
  have hjz : ∀ q, q ∈ j ↔ q ∈ Lev (scn 4 γ) ∧ ((∃ u, u ∈ A ∧ ∃ c, c ∈ S ∧ ∃ C, C ∈ S ∧
      (Pr F₁ u c ∧ (IsOp C c c ∧ IsOp q u C))) ∨ IsOp q x cx) := fun q => mem_sepB _ _ _ q
  have hjc : Con j := con_sepB _ (con_lev (big_scn hγ 4).1) _ (by
    intro i
    match i with
    | 0 => exact hA
    | 1 => exact hS
    | 2 => exact hF₁c
    | 3 => exact hx
    | 4 => exact ⟨γ, hγ.1, lev_tr hγ.1 S hSγ cx hcx⟩)
  have hpair : ∀ u C, u ∈ G → C ∈ S → kp u C ∈ Lev (scn 4 γ) := by
    intro u C hu hC
    refine kp_mem_lev hγ ?_ (lev_tr hγ.1 S hSγ C hC)
    rcases (hG u).mp hu with h | h
    · exact lev_tr hγ.1 A hAγ u h
    · rw [h]
      exact hxγ
  have hne : kp (∅ : V) ∅ ≠ ∅ := by
    intro e
    obtain ⟨w, hw⟩ := isOp_nonempty (isOp_kp (∅ : V) ∅)
    rw [e] at hw
    exact absurd hw (by simp)
  have hinv : ∀ u v, kp u v ∈ j → (u ∈ A ∧ ∃ c, c ∈ S ∧ (Pr F₁ u c ∧ v = kp c c)) ∨
      (u = x ∧ v = cx) := by
    intro u v h
    rcases ((hjz _).mp h).2 with ⟨u₁, hu₁, c, hc, C, -, hpr, hC, hop⟩ | hop
    · obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      exact Or.inl ⟨hu₁, c, hc, hpr, isOp_iff.mp hC⟩
    · exact Or.inr (kp_inj (isOp_iff.mp hop))
  refine ⟨G, hGc, hG, j, hjc, fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
  · rcases (hG u).mp hu with h | h
    · obtain ⟨v, hv, hr⟩ := hF₁.1 u h
      have hvv := hSp v v hv hv
      exact ⟨kp v v, hvv, hin_rl_iff.mpr ((hjz _).mpr ⟨hpair u _ hu hvv,
        Or.inl ⟨u, h, v, hv, kp v v, hvv, pr_iff.mpr (hin_rl_iff.mp hr), isOp_kp v v,
          isOp_kp u _⟩⟩)⟩
    · exact ⟨cx, hcx, hin_rl_iff.mpr ((hjz _).mpr ⟨hpair u cx hu hcx, Or.inr (by
        rw [h]
        exact isOp_kp x cx)⟩)⟩
  · rcases hinv u v (hin_rl_iff.mp h1) with ⟨huA, c, -, hpr, ev⟩ | ⟨eu, ev⟩
    · rcases hinv u' v (hin_rl_iff.mp h2) with ⟨huA', c', -, hpr', ev'⟩ | ⟨-, ev'⟩
      · obtain ⟨ec, -⟩ := kp_inj (ev.symm.trans ev')
        rw [← ec] at hpr'
        exact hF₁.2 u u' c huA huA' (hin_rl_iff.mpr (pr_iff.mp hpr))
          (hin_rl_iff.mpr (pr_iff.mp hpr'))
      · obtain ⟨e1, e2⟩ := kp_inj (ev.symm.trans ev')
        exact absurd (e2.symm.trans e1) hne
    · rcases hinv u' v (hin_rl_iff.mp h2) with ⟨-, c', -, -, ev'⟩ | ⟨eu', -⟩
      · obtain ⟨e1, e2⟩ := kp_inj (ev'.symm.trans ev)
        exact absurd (e2.symm.trans e1) hne
      · rw [eu, eu']

/-- **Composition.** If `A` maps one-to-one into `S` by a constructible relation, and a
constructible set `I` relates, to every member of `B`, a member of `A` that it relates to no
other member of `B`, then `B` maps one-to-one into `S` by a constructible relation. -/
theorem linj_via {A B S I J : V} (hA : Con A) (hB : Con B) (hS : Con S) (hI : Con I)
    (hJ : Con J) (hJi : InjS J A S) (hsurj : ∀ z, z ∈ B → ∃ b, b ∈ A ∧ kp b z ∈ I)
    (hfun : ∀ b, b ∈ A → ∀ z, z ∈ B → ∀ z', z' ∈ B → kp b z ∈ I → kp b z' ∈ I → z = z') :
    LInj B S := by
  obtain ⟨γ, hγ, hBγ, hSγ⟩ := con_big2 hB hS
  let K : V := sepB (k := 5) (BDef.bex 1 (BDef.bex 3 (BDef.bex 5 ((isOpB.comp ![3, 2, 1]).and
    ((prB.comp ![7, 0, 2]).and (prB.comp ![8, 0, 1]))))))
    (Lev (scn 4 γ)) ![B, S, A, I, J]
  have hKz : ∀ q, q ∈ K ↔ q ∈ Lev (scn 4 γ) ∧ ∃ z, z ∈ B ∧ ∃ c, c ∈ S ∧ ∃ b, b ∈ A ∧
      (IsOp q z c ∧ (Pr I b z ∧ Pr J b c)) := fun q => mem_sepB _ _ _ q
  have hKc : Con K := con_sepB _ (con_lev (big_scn hγ 4).1) _ (by
    intro i
    match i with
    | 0 => exact hB
    | 1 => exact hS
    | 2 => exact hA
    | 3 => exact hI
    | 4 => exact hJ)
  have hinv : ∀ z v, kp z v ∈ K → ∃ b, b ∈ A ∧ (Pr I b z ∧ Pr J b v) := by
    intro z v h
    obtain ⟨-, z₁, -, c, -, b, hb, hop, h1, h2⟩ := (hKz _).mp h
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact ⟨b, hb, h1, h2⟩
  refine ⟨K, hKc, fun z hz => ?_, fun z z' v hz hz' h1 h2 => ?_⟩
  · obtain ⟨b, hb, hbz⟩ := hsurj z hz
    obtain ⟨c, hc, hr⟩ := hJi.1 b hb
    exact ⟨c, hc, hin_rl_iff.mpr ((hKz _).mpr ⟨kp_mem_lev hγ (lev_tr hγ.1 B hBγ z hz)
      (lev_tr hγ.1 S hSγ c hc), z, hz, c, hc, b, hb, isOp_kp z c, pr_iff.mpr hbz,
      pr_iff.mpr (hin_rl_iff.mp hr)⟩)⟩
  · obtain ⟨b, hb, hbz, hbv⟩ := hinv z v (hin_rl_iff.mp h1)
    obtain ⟨b', hb', hbz', hbv'⟩ := hinv z' v (hin_rl_iff.mp h2)
    have e : b = b' := hJi.2 b b' v hb hb' (hin_rl_iff.mpr (pr_iff.mp hbv))
      (hin_rl_iff.mpr (pr_iff.mp hbv'))
    rw [← e] at hbz'
    exact hfun b hb z hz z' hz' (pr_iff.mp hbz) (pr_iff.mp hbz')

/-- **Sharp condensation at the next height.** Let `κ` be the next height after the limit
ordinal `ν` above `ω`. Every constructible subset of a member of the level at `κ` is a member
of the level at `κ`. -/
theorem lnext_sub {ν κ : V} (hν : Lim ν) (hom : (om : V) ∈ ν) (hκ : Lim κ) (hνκ : ν ∈ κ)
    (hn : ¬LInj (Lev κ) (Lev ν)) (hall : ∀ δ, δ ∈ κ → LInj (Lev δ) (Lev ν)) :
    ∀ a x : V, a ∈ Lev κ → Con x → (∀ z, z ∈ x → z ∈ a) → x ∈ Lev κ := by
  intro a x ha hxc hxa
  have homκ : (om : V) ∈ κ := hκ.1.1 ν hνκ om hom
  have hSc : Con (Lev ν) := con_lev hν.1
  have hSp : ∀ a b, a ∈ Lev ν → b ∈ Lev ν → kp a b ∈ Lev ν :=
    fun a b ha hb => kp_mem_lev_lim hν hom ha hb
  have h0 : (∅ : V) ∈ Lev ν := ord_mem_lev_lim hν ∅ (hν.1.1 om hom ∅ empty_mem_om)
  obtain ⟨δ, hδκ, hδb, haδ⟩ := lev_lim_exists hκ homκ ha
  have hxδ : ∀ z, z ∈ x → z ∈ Lev δ := fun z hz => lev_tr hδb.1 a haδ z (hxa z hz)
  obtain ⟨δ₁, hδ₁, hxδ₁⟩ := hxc
  obtain ⟨δ', hlim, hδ₁δ', hδδ'⟩ := exists_lim2 hδ₁ hδb.1
  obtain ⟨F, hF⟩ := exists_hier hlim.1
  have su : Setup δ δ' F x := ⟨hδb, hlim, hδδ', hF, lev_mono hlim.1 hδ₁δ' x hxδ₁, hxδ⟩
  -- the generators and their codes
  have hscδ : sc δ ∈ κ := hκ.2.2 δ hδκ
  have hscO : Ord (sc δ) := ord_sc hδb.1
  obtain ⟨G₀, hG₀c, hG₀, j₀, hj₀c, hj₀⟩ := linj_adj (con_lev hscO) hSc ⟨δ₁, hδ₁, hxδ₁⟩ hSp h0
    (hall (sc δ) hscδ)
  obtain ⟨lam, hlam, hδ'lam, hνlam⟩ := exists_lim2 hlim.1 hν.1
  have hGW : ∀ z, z ∈ G₀ → z ∈ Lev δ' := by
    intro z hz
    rcases (hG₀ z).mp hz with h | h
    · exact lev_mono hlim.1 (hlim.2.2 δ hδδ') z h
    · rw [h]
      exact su.mem
  have hgf : ∀ y₀ y₁ y₂ y₃ z z' : V, Ap4 (gSet (Lev δ') F (sc δ') (LtS δ')) y₀ y₁ y₂ y₃ z →
      Ap4 (gSet (Lev δ') F (sc δ') (LtS δ')) y₀ y₁ y₂ y₃ z' → z = z' :=
    fun y₀ y₁ y₂ y₃ z z' h h' => su.gh_fun (ap4_gSet.mp h).2.1 (ap4_gSet.mp h).2.2.2.2.2
      (ap4_gSet.mp h').2.2.2.2.2
  obtain ⟨N, hNc, hNW, hNG, hNclo, J, hJc, hJ⟩ := exists_chull (lim_big hlam) (con_lev hlim.1)
    hSc (con_gSet hlim.1 hF) hj₀c hG₀c (lev_mono hlam.1 hδ'lam) (lev_mono hlam.1 hνlam) hGW
    (injV_of_injS hj₀).1
    (fun u hu u' hu' c h1 h2 => hj₀.2 u u' c hu hu' (hin_rl_iff.mpr (pr_iff.mp h1))
      (hin_rl_iff.mpr (pr_iff.mp h2)))
    hSp h0 hgf
  have hd : HullData δ δ' F x N := ⟨su, hNW,
    fun b hb => hNG b ((hG₀ b).mpr (Or.inl (lev_mono hscO (self_mem_sc δ) b hb))),
    hNG _ ((hG₀ _).mpr (Or.inl (lev_mem hscO (self_mem_sc δ)))),
    hNG x ((hG₀ x).mpr (Or.inr rfl)),
    fun y₀ y₁ y₂ y₃ z k0 k1 k2 k3 hz hGH => hNclo y₀ y₁ y₂ y₃ z k0 k1 k2 k3 hz
      (ap4_gSet.mpr ⟨hNW _ k0, hNW _ k1, hNW _ k2, hNW _ k3, hz, hGH⟩)⟩
  -- the collapse of the hull
  obtain ⟨T, hT⟩ := hc_of_models (V := V) N
  obtain ⟨P, hP⟩ := hT.2 (memR N) (wf_memR N)
  obtain ⟨Q, hQ⟩ := hT.2 (levR N F (sc δ')) (wf_levR hd)
  have cd : CollData δ δ' F x N T P Q := ⟨hd, hT.1, hP, hQ⟩
  obtain ⟨ρ, hρ, hr⟩ := rkL_exists su.ord su.mem
  obtain ⟨-, hLρ⟩ := hd.rk_mem hd.gen3 hr
  have hS : InS N δ' ρ := ⟨hρ, hLρ⟩
  obtain ⟨hA, hC⟩ := cd.main_ind ρ hS
  have h1 := cd.pi_inDef hS hA hC hd.gen3 hr
  rw [cd.pi_x0] at h1
  have hcO := cd.cc_ord hS
  have h3 : x ∈ Lev (sc (ccF Q ρ)) := inDef_mem hcO h1
  -- the collapsed ordinal is below `κ`
  have hcκ : ccF Q ρ ∈ κ := by
    by_contra hcon
    have hle : κ = ccF Q ρ ∨ κ ∈ ccF Q ρ := by
      rcases ord_tri hcO hκ.1 with e | e | e
      · exact absurd e hcon
      · exact Or.inl e.symm
      · exact Or.inr e
    have hsubκ : ∀ z, z ∈ Lev κ → z ∈ Lev (ccF Q ρ) := lev_sub_of_le hκ.1 hcO hle
    obtain ⟨A, hAc, hAz⟩ := con_inter hNc (con_lev (ord_mem su.ord hρ))
    have hOI : OIso P A (Lev (ccF Q ρ)) := by
      refine ⟨fun b hb => ?_, fun z hz => ?_, fun b hb b' hb' z _ z' _ hbz hbz' => ?_⟩
      · obtain ⟨hbN, hbρ⟩ := (hAz b).mp hb
        exact ⟨piF P b, (hA _).mpr ⟨b, hbN, hbρ, rfl⟩, (piF_eq hP hbN).mpr rfl⟩
      · obtain ⟨b, hbN, hbρ, e⟩ := (hA z).mp hz
        exact ⟨b, (hAz b).mpr ⟨hbN, hbρ⟩, (piF_eq hP hbN).mpr e⟩
      · obtain ⟨hbN, hbρ⟩ := (hAz b).mp hb
        obtain ⟨hbN', hbρ'⟩ := (hAz b').mp hb'
        rw [(piF_eq hP hbN).mp hbz, (piF_eq hP hbN').mp hbz']
        exact hC b b' hbN hbN' hbρ hbρ'
    obtain ⟨lam₂, hlam₂, k1, k2⟩ := exists_lim2 hlim.1 hcO
    obtain ⟨I, hIc, hI⟩ := oiso_con hlam₂ hAc (con_lev hcO)
      (fun b hb => lev_mono hlam₂.1 k1 b (lev_mono su.ord hρ b ((hAz b).mp hb).2))
      (lev_mono hlam₂.1 k2) hOI
    refine hn (linj_via hAc (con_lev hκ.1) hSc hIc hJc
      (injS_dom_mono hJ (fun z hz => ((hAz z).mp hz).1)) (fun z hz => ?_)
      (fun b hb z hz z' hz' h h' => ?_))
    · obtain ⟨b, hbN, hbρ, e⟩ := (hA z).mp (hsubκ z hz)
      have hbA : b ∈ A := (hAz b).mpr ⟨hbN, hbρ⟩
      exact ⟨b, hbA, (hI b z hbA (hsubκ z hz)).mpr ((piF_eq hP hbN).mpr e)⟩
    · have hbN := ((hAz b).mp hb).1
      rw [(piF_eq hP hbN).mp ((hI b z hb (hsubκ z hz)).mp h),
        (piF_eq hP hbN).mp ((hI b z' hb (hsubκ z' hz')).mp h')]
  exact lev_mono hκ.1 (hκ.2.2 _ hcκ) x h3

/-- **Above every limit ordinal above `ω` there is a height whose level is a host.** -/
theorem exists_full {ν : V} (hν : Lim ν) (hom : (om : V) ∈ ν) : ∃ κ : V, Full κ ∧ ν ∈ κ := by
  obtain ⟨κ, hκ, hνκ, hn, hall⟩ := lnext_spec hν hom
  exact ⟨κ, full_of_sub hν hom hκ hνκ hn hall (lnext_sub hν hom hκ hνκ hn hall), hνκ⟩

/-- **Above every ordinal there is a height whose level is a host.** -/
theorem exists_full_above {γ : V} (hγ : Ord γ) : ∃ κ : V, Full κ ∧ γ ∈ κ := by
  obtain ⟨ν, hν, hγν, homν⟩ := exists_lim2 hγ (ord_om (V := V))
  obtain ⟨κ, hκ, hνκ⟩ := exists_full hν homν
  exact ⟨κ, hκ, hκ.lim.1.1 ν hνκ γ hγν⟩

/-- **Every model of `𝗠𝗛` has a host with a closed level**: a level of its constructible sets,
with the level at a smaller height of the same kind as a member. -/
theorem exists_closed_host : ∃ (κ μ : V) (hκ : Full κ) (hμκ : μ ∈ κ),
    (levHost hκ).Closed (hmk hκ (Lev μ) (lev_mem hκ.lim.1 hμκ)) := by
  obtain ⟨μ, hμ, -⟩ := exists_full_above (V := V) ord_om
  obtain ⟨κ, hκ, hμκ⟩ := exists_full_above hμ.lim.1
  exact ⟨κ, μ, hκ, hμκ, closed_lev hκ hμ hμκ⟩

end full

end MH

end FFL.FirstOrder.SetTheory
