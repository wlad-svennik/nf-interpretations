module

public import MHHgt

@[expose] public section

set_option autoImplicit false

/-!
# A constructible ladder of full heights

In a model of `𝗠𝗛`. A *ladder* (`Ladder θ Sq U γ₀`) is a set `Sq` that relates every member
`γ` of the ordinal `θ` to a set `S`, with these properties: every such `S` satisfies `BaseS`,
is included in `U`, has `U` far above it, and the level at `γ₀` maps one-to-one into it; and
the set at a larger member of `θ` is far above the set at a smaller one.

**`exists_ladder`**: then there are a full height `K` and a *constructible* set `Lam` of pairs
`(α, A)`, `α ∈ θ`, such that for every `α ∈ θ` there is a full height `μ` below `K` and above
`γ₀` for which `Lam` relates `α` to the level at `μ` and to nothing else, and the level at a
smaller `α` is a member of the level at a larger one.

The sets of the ladder need not be constructible, so the heights `HgtF` that they give are not
used as the values. Instead:

* `fullB_iff`: below a full height `K`, being a full height is a bounded condition, so the set
  `FF` of the full heights below `K` and above `γ₀` is constructible.
* The collapse of `(FF, ∈)` (collapse axiom) counts `FF`: `piF Pc a` is the order type of the
  members of `FF` below `a` (`piO_lt_iff`, `piO_ord`).
* For `γ ∈ θ` let `a` be the least member of `FF` whose level does not map one-to-one into a
  set of the ladder at `γ` (`EmbR`). These increase with `γ` (`hgtF_far`), so `γ` is at most
  the order type at `a` (induction on `γ`), and so `γ` is the order type at some member of
  `FF`.
* The map from the first `θ` members of `FF` to their order types preserves the order of the
  constructible sets, so it is constructible (`oiso_con`); composing with the constructible
  map from the ordinals to the levels (`con_levmap`) gives `Lam`.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- Bounded form of `Full μ`, for `μ` below a full height `K`: `I` is the map from the
ordinals below `K` to the levels, `LK` the level at `K`, `omv` is `ω`. -/
def FullB {V : Type} [SetStructure V] (μ I LK omv : V) : Prop :=
  Ord μ ∧ ((∀ b, b ∈ μ → ∃ s, s ∈ μ ∧ SuccR s b) ∧ (omv ∈ μ ∧
    ∃ A, A ∈ LK ∧ (Pr I μ A ∧
      ((∀ a, a ∈ A → ∀ x, x ∈ LK → ((∀ z, z ∈ x → z ∈ a) → x ∈ A)) ∧
        (∀ a, a ∈ A → ∀ R, R ∈ LK → ((∀ u, u ∈ a → ∃ v, v ∈ A ∧ Pr R u v) →
          ∃ b, b ∈ A ∧ ∀ u, u ∈ a → ∃ v, v ∈ b ∧ Pr R u v))))))

def fullB : BDef (k := 4) (fun V _ v ↦ FullB (v 0) (v 1) (v 2) (v 3)) :=
  ((ordB.comp ![0]).and ((BDef.ball 0 (BDef.bex 1 (succB.comp ![0, 1]))).and
    ((BDef.mem 3 0).and (BDef.bex 2 ((prB.comp ![2, 1, 0]).and
      ((BDef.ball 0 (BDef.ball 4 ((BDef.ball 0 (BDef.mem 0 2)).imp (BDef.mem 0 2)))).and
        (BDef.ball 0 (BDef.ball 4 ((BDef.ball 1 (BDef.bex 3 (prB.comp ![2, 1, 0]))).imp
          (BDef.bex 2 (BDef.ball 2 (BDef.bex 1 (prB.comp ![3, 1, 0]))))))))))))).congr
    fun _ _ _ => Iff.rfl

/-- `a` is the least member of `FF` whose level does not map one-to-one into a set that `Sq`
relates to `γ` (bounded form). -/
def EmbR {V : Type} [SetStructure V] (γ a Sq FF Fh LL P RS : V) : Prop :=
  ∃ S, S ∈ RS ∧ (Pr Sq γ S ∧ (NoInjAt a Fh LL P S ∧
    ∀ a', a' ∈ FF → (NoInjAt a' Fh LL P S → (a = a' ∨ a ∈ a'))))

def embRB : BDef (k := 8) (fun V _ v ↦
    EmbR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  (BDef.bex 7 ((prB.comp ![3, 1, 0]).and ((noInjAtB.comp ![2, 5, 6, 7, 0]).and
    (BDef.ball 4 ((noInjAtB.comp ![0, 6, 7, 8, 1]).imp
      ((BDef.eq 3 0).or (BDef.mem 3 0))))))).congr fun _ _ _ => Iff.rfl

/-- `γ` is a counterexample: it is not at most the value of the collapse `Pc` at a member of
`FF` that `EmbR` gives for it. -/
def BadR {V : Type} [SetStructure V] (γ Sq FF Fh LL P RS T Pc : V) : Prop :=
  ∃ a, a ∈ FF ∧ (EmbR γ a Sq FF Fh LL P RS ∧ ∃ v, v ∈ T ∧ (Pr Pc a v ∧ ¬(γ = v ∨ γ ∈ v)))

def badRB : BDef (k := 9) (fun V _ v ↦
    BadR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  (BDef.bex 2 ((embRB.comp ![1, 0, 2, 3, 4, 5, 6, 7]).and (BDef.bex 8
    ((prB.comp ![10, 1, 0]).and ((BDef.eq 2 0).or (BDef.mem 2 0)).not)))).congr
    fun _ _ _ => Iff.rfl

section enum

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-! ### The collapse of a set of ordinals -/

section coll

variable {N T P : V} (hN : ∀ a, a ∈ N → Ord a) (hP : IsColl P (memR N) N T)

include hP in
theorem piO_lt {a b : V} (ha : a ∈ N) (hb : b ∈ N) (h : a ∈ b) : piF P a ∈ piF P b :=
  (pi_mem hP hb _).mpr ⟨a, ha, h, rfl⟩

include hN hP in
theorem piO_lt_iff {a b : V} (ha : a ∈ N) (hb : b ∈ N) : piF P a ∈ piF P b ↔ a ∈ b := by
  refine ⟨fun h => ?_, piO_lt hP ha hb⟩
  rcases ord_tri (hN a ha) (hN b hb) with e | e | e
  · exact e
  · rw [e] at h
    exact absurd h (mem_irrefl _)
  · exact absurd (piO_lt hP hb ha e) (mem_asymm h)

include hN hP in
theorem piO_inj {a b : V} (ha : a ∈ N) (hb : b ∈ N) (h : piF P a = piF P b) : a = b := by
  rcases ord_tri (hN a ha) (hN b hb) with e | e | e
  · have := piO_lt hP ha hb e
    rw [h] at this
    exact absurd this (mem_irrefl _)
  · exact e
  · have := piO_lt hP hb ha e
    rw [h] at this
    exact absurd this (mem_irrefl _)

include hN hP in
theorem piO_tr {a : V} (ha : a ∈ N) : Tr (piF P a) := by
  intro y hy z hz
  obtain ⟨b, hb, hba, e⟩ := (pi_mem hP ha y).mp hy
  rw [e] at hz
  obtain ⟨c, hc, hcb, e'⟩ := (pi_mem hP hb z).mp hz
  exact (pi_mem hP ha z).mpr ⟨c, hc, (hN a ha).1 b hba c hcb, e'⟩

include hN hP in
theorem piO_ord {a : V} (ha : a ∈ N) : Ord (piF P a) :=
  ⟨piO_tr hN hP ha, fun y hy => by
    obtain ⟨b, hb, -, e⟩ := (pi_mem hP ha y).mp hy
    rw [e]
    exact piO_tr hN hP hb⟩

end coll

/-! ### Full heights below a full height -/

theorem noInjAt_iff {lam Fh S U κ : V} (hl : Ord lam) (hFh : IsHier Fh lam)
    (hSU : ∀ z, z ∈ S → z ∈ U) (hκ : κ ∈ sc lam) :
    NoInjAt κ Fh (Lev (sc lam)) (℘ (prodS (Lev lam) U)) S ↔ ¬VInj (Lev κ) S := by
  have hscO : Ord (sc lam) := ord_sc hl
  have hκO := ord_mem hscO hκ
  have hsub : ∀ x, x ∈ Lev κ → x ∈ Lev lam := lev_sub_of_le hκO hl (mem_sc.mp hκ)
  constructor
  · rintro ⟨A, -, hA, hn⟩ hv
    have eA : A = Lev κ := (levAt_lev hl hFh hκ).mp hA
    rw [eA] at hn
    obtain ⟨F, hFP, hF⟩ := vinj_trim hv
    refine hn ⟨F, mem_power_iff.mpr fun z hz => ?_, hF⟩
    obtain ⟨u, hu, v, hv', e⟩ := mem_prodS.mp (mem_power_iff.mp hFP z hz)
    exact mem_prodS.mpr ⟨u, hsub u hu, v, hSU v hv', e⟩
  · intro hn
    refine ⟨Lev κ, lev_mem hscO hκ, (levAt_lev hl hFh hκ).mpr rfl, ?_⟩
    rintro ⟨F, -, hF⟩
    exact hn (vinj_of_injV hF)

/-- **Below a full height, being a full height is a bounded condition.** -/
theorem fullB_iff {K I μ : V} (hK : Full K) (hI : ∀ γ A, γ ∈ K → (Pr I γ A ↔ A = Lev γ))
    (hμ : μ ∈ K) : FullB μ I (Lev K) (om : V) ↔ Full μ := by
  have hKO := hK.lim.1
  have hμO := ord_mem hKO hμ
  have hup : ∀ x, x ∈ Lev μ → x ∈ Lev K := lev_mono hKO hμ
  constructor
  · rintro ⟨hO, hsucc, hom, A, -, hIA, hsub, hbd⟩
    have eA : A = Lev μ := (hI μ A hμ).mp hIA
    rw [eA] at hsub hbd
    have hlim : Lim μ := ⟨hO, ⟨om, hom⟩, fun β hβ => by
      obtain ⟨s, hs, e⟩ := hsucc β hβ
      rw [← succR_iff_sc.mp e]
      exact hs⟩
    refine ⟨hlim, hom, fun a x ha hx hxa => hsub a ha x (hK.sub a x (hup a ha) hx hxa) hxa,
      fun a R ha hR htot => ?_⟩
    have hac : Con a := ⟨μ, hμO, ha⟩
    obtain ⟨R', hR'c, hR'⟩ := con_inter hR (con_prodS hac (con_lev hμO))
    have h4 : scn 4 μ ∈ K := hK.lim.2.2 _ (hK.lim.2.2 _ (hK.lim.2.2 _ (hK.lim.2.2 μ hμ)))
    have hR'K : R' ∈ Lev K := hK.sub (Lev (scn 4 μ)) R' (lev_mem hKO h4) hR'c (fun z hz => by
      obtain ⟨u, hu, v, hv, e⟩ := mem_prodS.mp ((hR' z).mp hz).2
      rw [e]
      exact kp_mem_lev (lim_big hlim) (lev_tr hμO a ha u hu) hv)
    obtain ⟨b, hb, hbt⟩ := hbd a ha R' hR'K (fun u hu => by
      obtain ⟨v, hv, h⟩ := htot u hu
      exact ⟨v, hv, pr_iff.mpr ((hR' _).mpr ⟨h, mem_prodS.mpr ⟨u, hu, v, hv, rfl⟩⟩)⟩)
    exact ⟨b, hb, fun u hu => let ⟨v, hv, h⟩ := hbt u hu
      ⟨v, hv, ((hR' _).mp (pr_iff.mp h)).1⟩⟩
  · intro hF
    refine ⟨hμO, fun b hb => ⟨sc b, hF.lim.2.2 b hb, succR_iff_sc.mpr rfl⟩, hF.omega, Lev μ,
      lev_mem hKO hμ, (hI μ _ hμ).mpr rfl,
      fun a ha x hx hxa => hF.sub a x ha ⟨K, hKO, hx⟩ hxa, fun a ha R hR htot => ?_⟩
    obtain ⟨b, hb, hbt⟩ := hF.bd a R ha ⟨K, hKO, hR⟩
      (fun u hu => let ⟨v, hv, h⟩ := htot u hu; ⟨v, hv, pr_iff.mp h⟩)
    exact ⟨b, hb, fun u hu => let ⟨v, hv, h⟩ := hbt u hu; ⟨v, hv, pr_iff.mpr h⟩⟩

/-! ### Ladders -/

/-- **A ladder of sets**, indexed by the members of `θ`, below `U`, with base `γ₀`. -/
structure Ladder (θ Sq U γ₀ : V) : Prop where
  tot : ∀ γ : V, γ ∈ θ → ∃ S : V, Pr Sq γ S
  base : ∀ γ S : V, γ ∈ θ → Pr Sq γ S → BaseS S
  sub : ∀ γ S : V, γ ∈ θ → Pr Sq γ S → ∀ z, z ∈ S → z ∈ U
  top : ∀ γ S : V, γ ∈ θ → Pr Sq γ S → Far S U
  far : ∀ γ γ' S S' : V, γ ∈ γ' → γ' ∈ θ → Pr Sq γ S → Pr Sq γ' S' → Far S S'
  low : ∀ γ S : V, γ ∈ θ → Pr Sq γ S → VInj (Lev γ₀) S
  baseU : BaseS U

/-- **A ladder gives a constructible sequence of levels at full heights**: the levels at the
first `θ` full heights above `γ₀`, in increasing order. `K` is the full height of `U`, and the
heights at `α` and `α + 1` are consecutive among the full heights above `γ₀`. -/
theorem exists_ladder' {θ Sq U γ₀ : V} (hθ : Ord θ) (hγ₀ : Ord γ₀) (lad : Ladder θ Sq U γ₀) :
    ∃ K Lam : V, Full K ∧ Con Lam ∧ (∀ q, q ∈ Lam → q ∈ prodS θ (Lev K)) ∧
      (∀ α, α ∈ θ → ∃ μ, μ ∈ K ∧ Full μ ∧ γ₀ ∈ μ ∧ ∀ A, (Pr Lam α A ↔ A = Lev μ)) ∧
      (∀ α β A B, α ∈ β → β ∈ θ → Pr Lam α A → Pr Lam β B → A ∈ B) ∧ HgtF U K ∧
      (∀ α, sc α ∈ θ → ∃ a a', a ∈ K ∧ a' ∈ K ∧ Full a ∧ Full a' ∧ a ∈ a' ∧
        Pr Lam α (Lev a) ∧ Pr Lam (sc α) (Lev a') ∧
        ∀ ν, ν ∈ K → Full ν → γ₀ ∈ ν → a ∈ ν → (a' = ν ∨ a' ∈ ν)) := by
  obtain ⟨K, hKF⟩ := hgtF_exists lad.baseU
  have hK : Full K := hgtF_full lad.baseU hKF
  have hKO := hK.lim.1
  have hμ : ∀ γ S, γ ∈ θ → Pr Sq γ S → ∃ μ, HgtF S μ ∧ μ ∈ K ∧ Full μ ∧ γ₀ ∈ μ := by
    intro γ S hγ hS
    have hb := lad.base γ S hγ hS
    obtain ⟨μ, hμ⟩ := hgtF_exists hb
    exact ⟨μ, hμ, hgtF_lt hb hμ hKF (lad.top γ S hγ hS), hgtF_full hb hμ,
      hgtF_gt hμ hγ₀ (lad.low γ S hγ hS)⟩
  obtain ⟨I, hIc, hI⟩ := con_levmap hK.lim
  obtain ⟨Fh, hFh⟩ := exists_hier hKO
  let LL : V := Lev (sc K)
  let P : V := ℘ (prodS (Lev K) U)
  let RS : V := ℘ U
  -- the full heights below `K` and above `γ₀`
  let FF : V := sepB (k := 4) ((BDef.mem 4 0).and (fullB.comp ![0, 1, 2, 3])) K
    ![I, Lev K, om, γ₀]
  have hFF0 : ∀ μ, μ ∈ FF ↔ μ ∈ K ∧ (γ₀ ∈ μ ∧ FullB μ I (Lev K) om) :=
    fun μ => mem_sepB _ _ _ μ
  have hFF : ∀ μ, μ ∈ FF ↔ μ ∈ K ∧ (γ₀ ∈ μ ∧ Full μ) := fun μ => (hFF0 μ).trans
    ⟨fun h => ⟨h.1, h.2.1, (fullB_iff hK hI h.1).mp h.2.2⟩,
      fun h => ⟨h.1, h.2.1, (fullB_iff hK hI h.1).mpr h.2.2⟩⟩
  have hFFc : Con FF := con_sepB _ (con_ord hKO) _ (by
    intro i
    match i with
    | 0 => exact hIc
    | 1 => exact con_lev hKO
    | 2 => exact con_ord ord_om
    | 3 => exact con_ord hγ₀)
  have hFFK : ∀ a, a ∈ FF → a ∈ K := fun a ha => ((hFF a).mp ha).1
  have hFFO : ∀ a, a ∈ FF → Ord a := fun a ha => ord_mem hKO (hFFK a ha)
  have hni : ∀ a S, a ∈ FF → (∀ z, z ∈ S → z ∈ U) →
      (NoInjAt a Fh LL P S ↔ ¬VInj (Lev a) S) :=
    fun a S ha hS => noInjAt_iff hKO hFh hS (mem_sc.mpr (Or.inr (hFFK a ha)))
  -- the least full height for a member of `θ`
  have hE1 : ∀ γ, γ ∈ θ → ∃ a, a ∈ FF ∧ EmbR γ a Sq FF Fh LL P RS := by
    intro γ hγ
    obtain ⟨S, hS⟩ := lad.tot γ hγ
    have hSU := lad.sub γ S hγ hS
    obtain ⟨μ, hμF, hμK, hμfull, hμγ⟩ := hμ γ S hγ hS
    have hμFF : μ ∈ FF := (hFF μ).mpr ⟨hμK, hμγ, hμfull⟩
    let Zs : V := sepB (k := 4) noInjAtB FF ![Fh, LL, P, S]
    have hZs : ∀ a, a ∈ Zs ↔ a ∈ FF ∧ NoInjAt a Fh LL P S := fun a => mem_sepB _ _ _ a
    obtain ⟨a, ha, hmin⟩ := ord_least Zs (fun z hz => hFFO z ((hZs z).mp hz).1)
      ⟨μ, (hZs μ).mpr ⟨hμFF, (hni μ S hμFF hSU).mpr (hgtF_not hμF)⟩⟩
    exact ⟨a, ((hZs a).mp ha).1, S, mem_power_iff.mpr hSU, hS, ((hZs a).mp ha).2,
      fun a' ha' hn => hmin a' ((hZs a').mpr ⟨ha', hn⟩)⟩
  have hE2 : ∀ γ γ' a a', γ ∈ γ' → γ' ∈ θ → a ∈ FF → a' ∈ FF →
      EmbR γ a Sq FF Fh LL P RS → EmbR γ' a' Sq FF Fh LL P RS → a ∈ a' := by
    rintro γ γ' a a' hγγ' hγ' ha ha' ⟨S, -, hS, -, hmin⟩ ⟨S', -, hS', hno', -⟩
    have hγ : γ ∈ θ := hθ.1 γ' hγ' γ hγγ'
    obtain ⟨μ, hμF, hμK, hμfull, hμγ⟩ := hμ γ S hγ hS
    have hμFF : μ ∈ FF := (hFF μ).mpr ⟨hμK, hμγ, hμfull⟩
    have hSU := lad.sub γ S hγ hS
    have hS'U := lad.sub γ' S' hγ' hS'
    have hle : a = μ ∨ a ∈ μ := hmin μ hμFF ((hni μ S hμFF hSU).mpr (hgtF_not hμF))
    have hv : VInj (Lev a) S' := vinj_dom_mono
      (hgtF_far (lad.base γ S hγ hS) hμF (lad.far γ γ' S S' hγγ' hγ' hS hS'))
      (lev_sub_of_le (hFFO a ha) (hgtF_ord hμF) hle)
    have hnv : ¬VInj (Lev a') S' := (hni a' S' ha' hS'U).mp hno'
    rcases ord_tri (hFFO a ha) (hFFO a' ha') with e | e | e
    · exact e
    · rw [e] at hv
      exact absurd hv hnv
    · exact absurd (vinj_dom_mono hv (lev_mono (hFFO a ha) e)) hnv
  -- the collapse of the set of the full heights
  obtain ⟨T, hT⟩ := hc_of_models (V := V) FF
  obtain ⟨Pc, hPc⟩ := hT.2 (memR FF) (wf_memR FF)
  have hInv : ∀ γ, γ ∈ θ → ∀ a, a ∈ FF → EmbR γ a Sq FF Fh LL P RS →
      (γ = piF Pc a ∨ γ ∈ piF Pc a) := by
    by_contra hcon
    let Wc : V := sepB (k := 8) badRB θ ![Sq, FF, Fh, LL, P, RS, T, Pc]
    have hWc : ∀ γ, γ ∈ Wc ↔ γ ∈ θ ∧ BadR γ Sq FF Fh LL P RS T Pc := fun γ => mem_sepB _ _ _ γ
    have hbad : ∀ γ, BadR γ Sq FF Fh LL P RS T Pc ↔ ∃ a, a ∈ FF ∧
        (EmbR γ a Sq FF Fh LL P RS ∧ ¬(γ = piF Pc a ∨ γ ∈ piF Pc a)) := by
      intro γ
      constructor
      · rintro ⟨a, ha, hE, v, -, hPv, hn⟩
        rw [(piF_eq hPc ha).mp hPv] at hn
        exact ⟨a, ha, hE, hn⟩
      · rintro ⟨a, ha, hE, hn⟩
        exact ⟨a, ha, hE, piF Pc a, (piF_mem hPc ha).1, (piF_eq hPc ha).mpr rfl, hn⟩
    have hne : ∃ γ, γ ∈ Wc := by
      by_contra h
      apply hcon
      intro γ hγ a ha hE
      by_contra hn
      exact h ⟨γ, (hWc γ).mpr ⟨hγ, (hbad γ).mpr ⟨a, ha, hE, hn⟩⟩⟩
    obtain ⟨γ, hγW, hmin⟩ := ord_least Wc (fun z hz => ord_mem hθ ((hWc z).mp hz).1) hne
    obtain ⟨hγ, hb⟩ := (hWc γ).mp hγW
    obtain ⟨a, ha, hE, hn⟩ := (hbad γ).mp hb
    have hsub : ∀ γ₁, γ₁ ∈ γ → γ₁ ∈ piF Pc a := by
      intro γ₁ hγ₁
      have hγ₁θ := hθ.1 γ hγ γ₁ hγ₁
      obtain ⟨a₁, ha₁, hE₁⟩ := hE1 γ₁ hγ₁θ
      have h1 : γ₁ = piF Pc a₁ ∨ γ₁ ∈ piF Pc a₁ := by
        by_contra hn₁
        rcases hmin γ₁ ((hWc γ₁).mpr ⟨hγ₁θ, (hbad γ₁).mpr ⟨a₁, ha₁, hE₁, hn₁⟩⟩) with e | e
        · rw [e] at hγ₁
          exact mem_irrefl _ hγ₁
        · exact mem_asymm hγ₁ e
      have h2 : piF Pc a₁ ∈ piF Pc a :=
        piO_lt hPc ha₁ ha (hE2 γ₁ γ a₁ a hγ₁ hγ ha₁ ha hE₁ hE)
      rcases h1 with e | e
      · rw [e]
        exact h2
      · exact (piO_ord hFFO hPc ha).1 _ h2 γ₁ e
    apply hn
    rcases ord_tri (ord_mem hθ hγ) (piO_ord hFFO hPc ha) with e | e | e
    · exact Or.inr e
    · exact Or.inl e
    · exact absurd (hsub _ e) (mem_irrefl _)
  -- every member of `θ` is the order type at a member of `FF`
  have hθR : ∀ γ, γ ∈ θ → ∃ b, b ∈ FF ∧ γ = piF Pc b := by
    intro γ hγ
    obtain ⟨a, ha, hE⟩ := hE1 γ hγ
    rcases hInv γ hγ a ha hE with e | e
    · exact ⟨a, ha, e⟩
    · obtain ⟨b, hb, -, e'⟩ := (pi_mem hPc ha γ).mp e
      exact ⟨b, hb, e'⟩
  -- the members of `FF` with order type in `θ` are those below an ordinal
  obtain ⟨β, hβ, hβiff⟩ : ∃ β : V, Ord β ∧ ∀ a, a ∈ FF → (piF Pc a ∈ θ ↔ a ∈ β) := by
    by_cases hc : ∃ a, a ∈ FF ∧ piF Pc a = θ
    · obtain ⟨a', ha', e⟩ := hc
      refine ⟨a', hFFO a' ha', fun a ha => ?_⟩
      rw [← e]
      exact piO_lt_iff hFFO hPc ha ha'
    · refine ⟨K, hKO, fun a ha => ⟨fun _ => hFFK a ha, fun _ => ?_⟩⟩
      rcases ord_tri (piO_ord hFFO hPc ha) hθ with e | e | e
      · exact e
      · exact absurd ⟨a, ha, e⟩ hc
      · obtain ⟨b, hb, -, e'⟩ := (pi_mem hPc ha θ).mp e
        exact absurd ⟨b, hb, e'.symm⟩ hc
  let B₁ : V := sepB (k := 1) (BDef.mem 0 1) FF ![β]
  have hB₁ : ∀ a, a ∈ B₁ ↔ a ∈ FF ∧ a ∈ β := fun a => mem_sepB _ _ _ a
  have hB₁c : Con B₁ := con_sepB _ hFFc _ (by
    intro i
    match i with
    | 0 => exact con_ord hβ)
  obtain ⟨lam, hlam, hKlam, hθlam⟩ := exists_lim2 hKO hθ
  have hordl : ∀ ξ, ξ ∈ lam → ξ ∈ Lev lam := ord_mem_lev_lim hlam
  have hFFl : ∀ a, a ∈ FF → a ∈ Lev lam := fun a ha => hordl a (hlam.1.1 K hKlam a (hFFK a ha))
  have hθl : ∀ b, b ∈ θ → b ∈ Lev lam := fun b hb => hordl b (hlam.1.1 θ hθlam b hb)
  have hOI : OIso Pc B₁ θ := by
    refine ⟨fun a ha => ?_, fun γ hγ => ?_, fun a ha a' ha' b hb b' hb' hab hab' => ?_⟩
    · obtain ⟨haF, haβ⟩ := (hB₁ a).mp ha
      exact ⟨piF Pc a, (hβiff a haF).mpr haβ, (piF_eq hPc haF).mpr rfl⟩
    · obtain ⟨b, hb, e⟩ := hθR γ hγ
      have hbθ : piF Pc b ∈ θ := e ▸ hγ
      exact ⟨b, (hB₁ b).mpr ⟨hb, (hβiff b hb).mp hbθ⟩, (piF_eq hPc hb).mpr e⟩
    · have haF := ((hB₁ a).mp ha).1
      have ha'F := ((hB₁ a').mp ha').1
      have e := (piF_eq hPc haF).mp hab
      have e' := (piF_eq hPc ha'F).mp hab'
      rw [ltL_ord_iff hlam.1 (hFFO a haF) (hFFO a' ha'F) (hFFl a haF) (hFFl a' ha'F),
        ltL_ord_iff hlam.1 (ord_mem hθ hb) (ord_mem hθ hb') (hθl b hb) (hθl b' hb'), e, e']
      exact (piO_lt_iff hFFO hPc haF ha'F).symm
  obtain ⟨I₁, hI₁c, hI₁⟩ := oiso_con hlam hB₁c (con_ord hθ)
    (fun a ha => hFFl a ((hB₁ a).mp ha).1) hθl hOI
  obtain ⟨LEV, hLEVc, hLEV⟩ := con_levels hK.lim
  -- the ladder of levels
  let Lam : V := sepB (k := 5) (BDef.bex 1 (BDef.bex 3 (BDef.bex 5 ((isOpB.comp ![3, 2, 0]).and
    ((prB.comp ![7, 1, 2]).and (prB.comp ![8, 1, 0])))))) (prodS θ LEV) ![θ, B₁, LEV, I₁, I]
  have hLamz : ∀ q, q ∈ Lam ↔ q ∈ prodS θ LEV ∧ ∃ α, α ∈ θ ∧ ∃ a, a ∈ B₁ ∧ ∃ A, A ∈ LEV ∧
      (IsOp q α A ∧ (Pr I₁ a α ∧ Pr I a A)) := fun q => mem_sepB _ _ _ q
  have hLamc : Con Lam := con_sepB _ (con_prodS (con_ord hθ) hLEVc) _ (by
    intro i
    match i with
    | 0 => exact con_ord hθ
    | 1 => exact hB₁c
    | 2 => exact hLEVc
    | 3 => exact hI₁c
    | 4 => exact hIc)
  have hLampr : ∀ α A, Pr Lam α A ↔ α ∈ θ ∧ ∃ a, a ∈ B₁ ∧ (α = piF Pc a ∧ A = Lev a) := by
    intro α A
    rw [pr_iff, hLamz]
    constructor
    · rintro ⟨-, α₁, hα₁, a, ha, A₁, -, hop, h1, h2⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      have haF := ((hB₁ a).mp ha).1
      exact ⟨hα₁, a, ha, (piF_eq hPc haF).mp ((hI₁ a α₁ ha hα₁).mp (pr_iff.mp h1)),
        (hI a A₁ (hFFK a haF)).mp h2⟩
    · rintro ⟨hα, a, ha, e, eA⟩
      have haF := ((hB₁ a).mp ha).1
      have hAL : A ∈ LEV := (hLEV A).mpr ⟨a, hFFK a haF, eA⟩
      exact ⟨mem_prodS.mpr ⟨α, hα, A, hAL, rfl⟩, α, hα, a, ha, A, hAL, isOp_kp α A,
        pr_iff.mpr ((hI₁ a α ha hα).mpr ((piF_eq hPc haF).mpr e)),
        (hI a A (hFFK a haF)).mpr eA⟩
  refine ⟨K, Lam, hK, hLamc, fun q hq => ?_, fun α hα => ?_, fun α β' A B hαβ hβ' hA hB => ?_,
    hKF, fun α hsα => ?_⟩
  · obtain ⟨α, hα, A, hA, e⟩ := mem_prodS.mp ((hLamz q).mp hq).1
    obtain ⟨γ, hγ, eA⟩ := (hLEV A).mp hA
    rw [eA] at e
    exact mem_prodS.mpr ⟨α, hα, Lev γ, lev_mem hKO hγ, e⟩
  · obtain ⟨b, hb, e⟩ := hθR α hα
    have hbθ : piF Pc b ∈ θ := e ▸ hα
    have hbB : b ∈ B₁ := (hB₁ b).mpr ⟨hb, (hβiff b hb).mp hbθ⟩
    obtain ⟨hbK, hbγ, hbfull⟩ := (hFF b).mp hb
    refine ⟨b, hbK, hbfull, hbγ, fun A => ?_⟩
    rw [hLampr]
    constructor
    · rintro ⟨-, a, ha, ea, eA⟩
      rw [eA, piO_inj hFFO hPc ((hB₁ a).mp ha).1 hb (ea.symm.trans e)]
    · intro eA
      exact ⟨hα, b, hbB, e, eA⟩
  · obtain ⟨-, a, ha, ea, eA⟩ := (hLampr α A).mp hA
    obtain ⟨-, a', ha', ea', eB⟩ := (hLampr β' B).mp hB
    have haF := ((hB₁ a).mp ha).1
    have ha'F := ((hB₁ a').mp ha').1
    rw [ea, ea'] at hαβ
    rw [eA, eB]
    exact lev_mem (hFFO a' ha'F) ((piO_lt_iff hFFO hPc haF ha'F).mp hαβ)
  · have hα : α ∈ θ := hθ.1 (sc α) hsα α (self_mem_sc α)
    obtain ⟨b, hb, e⟩ := hθR α hα
    obtain ⟨b', hb', e'⟩ := hθR (sc α) hsα
    have hbθ : piF Pc b ∈ θ := e ▸ hα
    have hb'θ : piF Pc b' ∈ θ := e' ▸ hsα
    have hbB : b ∈ B₁ := (hB₁ b).mpr ⟨hb, (hβiff b hb).mp hbθ⟩
    have hb'B : b' ∈ B₁ := (hB₁ b').mpr ⟨hb', (hβiff b' hb').mp hb'θ⟩
    obtain ⟨hbK, -, hbfull⟩ := (hFF b).mp hb
    obtain ⟨hb'K, -, hb'full⟩ := (hFF b').mp hb'
    have hbb' : b ∈ b' := (piO_lt_iff hFFO hPc hb hb').mp (by
      rw [← e, ← e']
      exact self_mem_sc α)
    refine ⟨b, b', hbK, hb'K, hbfull, hb'full, hbb', (hLampr α _).mpr ⟨hα, b, hbB, e, rfl⟩,
      (hLampr (sc α) _).mpr ⟨hsα, b', hb'B, e', rfl⟩, fun ν hνK hνfull hγν hbν => ?_⟩
    have hν : ν ∈ FF := (hFF ν).mpr ⟨hνK, hγν, hνfull⟩
    have h1 : α ∈ piF Pc ν := by
      rw [e]
      exact piO_lt hPc hb hν hbν
    rcases ord_tri (ord_sc (ord_mem hθ hα)) (piO_ord hFFO hPc hν) with k | k | k
    · rw [e'] at k
      exact Or.inr ((piO_lt_iff hFFO hPc hb' hν).mp k)
    · rw [e'] at k
      exact Or.inl (piO_inj hFFO hPc hb' hν k)
    · exfalso
      rcases mem_sc.mp k with k' | k'
      · rw [k'] at h1
        exact mem_irrefl _ h1
      · exact mem_asymm h1 k'

/-- **A ladder gives a constructible sequence of levels at full heights.** -/
theorem exists_ladder {θ Sq U γ₀ : V} (hθ : Ord θ) (hγ₀ : Ord γ₀) (lad : Ladder θ Sq U γ₀) :
    ∃ K Lam : V, Full K ∧ Con Lam ∧ (∀ q, q ∈ Lam → q ∈ prodS θ (Lev K)) ∧
      (∀ α, α ∈ θ → ∃ μ, μ ∈ K ∧ Full μ ∧ γ₀ ∈ μ ∧ ∀ A, (Pr Lam α A ↔ A = Lev μ)) ∧
      (∀ α β A B, α ∈ β → β ∈ θ → Pr Lam α A → Pr Lam β B → A ∈ B) :=
  let ⟨K, Lam, h1, h2, h3, h4, h5, _, _⟩ := exists_ladder' hθ hγ₀ lad
  ⟨K, Lam, h1, h2, h3, h4, h5⟩

end enum

end MH

end FFL.FirstOrder.SetTheory
