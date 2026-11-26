module

public import MHSupply
public import HostER

@[expose] public section

set_option autoImplicit false

/-!
# The partition theorem in a level of the constructible sets

In a model of `𝗠𝗛`. The levels at consecutive next heights, as elements of the host at a full
height above them, are a sequence of consecutive closed levels in the sense of `HostER.lean`
(`levSeq_lev`): a member of the level at a next height maps one-to-one into the level before
by a constructible *function* (the least value, in the order of the constructible sets, of the
constructible one-to-one relation), and a constructible subset of a member of the host is a
member of the host.

**`supply_er`**: a supply of sets for `n + 1` gives a host with a tower of height `d` and
consecutive closed levels `Ms 0 ∈ … ∈ Ms n` such that the ordinals of `Ms n` are `d`, with the
level at the base height `ν₀` a member of `Ms 0`. So `Host.er_seq` applies to the colourings of
the sets of `n` levels of the tower with colours in the level at `ν₀`.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section er

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

omit [Nonempty V] hH in
theorem inDef_sub {A lt x : V} (h : InDef A lt x) : ∀ z, z ∈ x → z ∈ A := by
  rcases h with e | ⟨s, -, y₁, -, y₂, -, y₃, -, hD⟩
  · rw [e]
    exact fun z hz => hz
  · exact fun z hz => (hD.1 z hz).1

/-- An ordinal is not a member of its own level. -/
theorem ord_not_mem_lev {ξ : V} (hξ : Ord ξ) : ξ ∉ Lev ξ := by
  intro hcon
  obtain ⟨F, hF⟩ := exists_hier hξ
  have hscO : Ord (sc ξ) := ord_sc hξ
  let Z : V := sepB (k := 2) (BDef.bex 2 ((levAtB.comp ![2, 1, 0]).and (BDef.mem 1 0))) (sc ξ)
    ![F, Lev (sc ξ)]
  have hZ : ∀ β, β ∈ Z ↔ β ∈ sc ξ ∧ ∃ A, A ∈ Lev (sc ξ) ∧ (LevAt F β A ∧ β ∈ A) :=
    fun β => mem_sepB _ _ _ β
  have hZ' : ∀ β, β ∈ sc ξ → (β ∈ Z ↔ β ∈ Lev β) := by
    intro β hβ
    rw [hZ]
    constructor
    · rintro ⟨-, A, -, hA, hβA⟩
      rw [(levAt_lev hξ hF hβ).mp hA] at hβA
      exact hβA
    · intro h
      exact ⟨hβ, Lev β, lev_mem hscO hβ, (levAt_lev hξ hF hβ).mpr rfl, h⟩
  obtain ⟨β₀, hβ₀, hmin⟩ := ord_least Z (fun z hz => ord_mem hscO ((hZ z).mp hz).1)
    ⟨ξ, (hZ' ξ (self_mem_sc ξ)).mpr hcon⟩
  have hβ₀s := ((hZ β₀).mp hβ₀).1
  have hβ₀O := ord_mem hscO hβ₀s
  obtain ⟨β, hβ, hin⟩ := (mem_lev hβ₀O).mp ((hZ' β₀ hβ₀s).mp hβ₀)
  have hβs : β ∈ sc ξ := hscO.1 β₀ hβ₀s β hβ
  have hββ : β ∈ Lev β := inDef_sub hin β hβ
  rcases hmin β ((hZ' β hβs).mpr hββ) with e | e
  · rw [e] at hβ
    exact mem_irrefl _ hβ
  · exact mem_asymm hβ e

/-- An ordinal that is a member of the level at `γ` is a member of `γ`. -/
theorem ord_mem_of_lev {γ z : V} (hγ : Ord γ) (hz : Ord z) (h : z ∈ Lev γ) : z ∈ γ := by
  rcases ord_tri hz hγ with e | e | e
  · exact e
  · rw [e] at h
    exact absurd h (ord_not_mem_lev hγ)
  · exact absurd (lev_mono hz e z h) (ord_not_mem_lev hz)

/-! ### The dictionary between the host and the model, continued -/

section dict

variable {κ : V} (hκ : Full κ)

theorem app_val (f a b : (levHost hκ).W) :
    (levHost hκ).App f a b ↔ Pr (hval hκ f) (hval hκ a) (hval hκ b) := by
  rw [(levHost hκ).app_iff, pr_iff, ← op_val]
  exact Iff.rfl

/-- The element of the host that `x` is, or the empty set if `x` is not in the level. -/
noncomputable def hmkT (x : V) : (levHost hκ).W :=
  open Classical in if h : x ∈ Lev κ then hmk hκ x h else (levHost hκ).emp

theorem hmkT_val {x : V} (h : x ∈ Lev κ) : hval hκ (hmkT hκ x) = x := by
  unfold hmkT
  rw [dif_pos h]
  rfl

theorem hmkT_eq {x : V} (h : x ∈ Lev κ) : hmkT hκ x = hmk hκ x h := by
  unfold hmkT
  rw [dif_pos h]

theorem on_val (a : (levHost hκ).W) : (levHost hκ).On a ↔ Ord (hval hκ a) := by
  constructor
  · intro h
    refine ⟨fun y hy z hz => ?_, fun y hy z hz w hw => ?_⟩
    · obtain ⟨y', rfl, hy'⟩ := hlift hκ hy
      obtain ⟨z', rfl, hz'⟩ := hlift hκ hz
      exact h.1 z' y' hz' hy'
    · obtain ⟨y', rfl, hy'⟩ := hlift hκ hy
      obtain ⟨z', rfl, hz'⟩ := hlift hκ hz
      obtain ⟨w', rfl, hw'⟩ := hlift hκ hw
      exact h.2 y' hy' w' z' hw' hz'
  · intro h
    exact ⟨fun x y hxy hy => h.1 (hval hκ y) hy (hval hκ x) hxy,
      fun y hy x z hxz hzy => h.2 (hval hκ y) hy (hval hκ z) hzy (hval hκ x) hxz⟩

/-- The ordinals of the level at a limit ordinal `μ`, in the host, are `μ`. -/
theorem ords_val {μ : V} (hμ : Lim μ) (hμκ : μ ∈ κ) :
    hval hκ ((levHost hκ).ords (hmkT hκ (Lev μ))) = μ := by
  have hL : Lev μ ∈ Lev κ := lev_mem hκ.lim.1 hμκ
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨a, rfl, ha⟩ := hlift hκ hz
    obtain ⟨haM, haO⟩ := (levHost hκ).mem_ords.mp ha
    have h1 : hval hκ a ∈ hval hκ (hmkT hκ (Lev μ)) := haM
    rw [hmkT_val hκ hL] at h1
    exact ord_mem_of_lev hμ.1 ((on_val hκ a).mp haO) h1
  · have hzL : z ∈ Lev μ := ord_mem_lev_lim hμ z hz
    have hzK : z ∈ Lev κ := lev_mono hκ.lim.1 hμκ z hzL
    have h1 : hmk hκ z hzK ∈ (levHost hκ).ords (hmkT hκ (Lev μ)) :=
      (levHost hκ).mem_ords.mpr ⟨by
        show z ∈ hval hκ (hmkT hκ (Lev μ))
        rw [hmkT_val hκ hL]
        exact hzL, (on_val hκ _).mpr (ord_mem hμ.1 hz)⟩
    exact h1

/-- **A member of the level at a next height maps one-to-one into the level before, by a
function of the host.** -/
theorem cons_lev {μ μ' : V} (hμ : Lim μ) (hom : (om : V) ∈ μ) (hn : NextH μ μ') (hμ'κ : μ' ∈ κ)
    (x : (levHost hκ).W) (hx : hval hκ x ∈ Lev μ') :
    ∃ g, (levHost hκ).IsFun g ∧
      (∀ a, a ∈ x → ∃ c, hval hκ c ∈ Lev μ ∧ (levHost hκ).App g a c) ∧
      ∀ a a' c, a ∈ x → a' ∈ x → (levHost hκ).App g a c → (levHost hκ).App g a' c → a = a' := by
  have hκO := hκ.lim.1
  have hμ'l : Lim μ' := hn.1
  have hμμ' : μ ∈ μ' := hn.2.1
  have hom' : (om : V) ∈ μ' := hμ'l.1.1 μ hμμ' om hom
  obtain ⟨δ, hδ, hδb, hxδ⟩ := lev_lim_exists hμ'l hom' hx
  obtain ⟨F, hFc, hF⟩ := hn.2.2.2 δ hδ
  have hXδ : ∀ u, u ∈ hval hκ x → u ∈ Lev δ := lev_tr hδb.1 _ hxδ
  have hXc : Con (hval hκ x) := ⟨μ', hμ'l.1, hx⟩
  have hlt : ∀ a b : V, Pr (LtS μ) a b ↔ a ∈ Lev μ ∧ (b ∈ Lev μ ∧ LtL a b) := fun a b => lts_iff hμ.1
  let g : V := sepB (k := 4) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    ((prB.comp ![5, 1, 0]).and (BDef.ball 4 ((prB.comp ![6, 2, 0]).imp
      (prB.comp ![7, 0, 1]).not)))))) (prodS (hval hκ x) (Lev μ))
    ![hval hκ x, Lev μ, F, LtS μ]
  have hgz : ∀ q, q ∈ g ↔ q ∈ prodS (hval hκ x) (Lev μ) ∧ ∃ u, u ∈ hval hκ x ∧ ∃ v, v ∈ Lev μ ∧
      (IsOp q u v ∧ (Pr F u v ∧ ∀ v', v' ∈ Lev μ → (Pr F u v' → ¬Pr (LtS μ) v' v))) :=
    fun q => mem_sepB _ _ _ q
  have hgpr : ∀ u v, Pr g u v ↔ u ∈ hval hκ x ∧ (v ∈ Lev μ ∧ (Pr F u v ∧
      ∀ v', v' ∈ Lev μ → Pr F u v' → ¬LtL v' v)) := by
    intro u v
    rw [pr_iff, hgz]
    constructor
    · rintro ⟨-, u₁, hu₁, v₁, hv₁, hop, hF₁, hmin⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      exact ⟨hu₁, hv₁, hF₁, fun v' hv' hFv' hl => hmin v' hv' hFv' ((hlt v' v₁).mpr ⟨hv', hv₁, hl⟩)⟩
    · rintro ⟨hu, hv, hFuv, hmin⟩
      exact ⟨mem_prodS.mpr ⟨u, hu, v, hv, rfl⟩, u, hu, v, hv, isOp_kp u v, hFuv,
        fun v' hv' hFv' hl => hmin v' hv' hFv' ((hlt v' v).mp hl).2.2⟩
  have hgc : Con g := con_sepB _ (con_prodS hXc (con_lev hμ.1)) _ (by
    intro i
    match i with
    | 0 => exact hXc
    | 1 => exact con_lev hμ.1
    | 2 => exact hFc
    | 3 => exact con_lts' hμ.1)
  have hup : ∀ z, z ∈ Lev μ' → z ∈ Lev κ := lev_mono hκO hμ'κ
  have hupμ : ∀ z, z ∈ Lev μ → z ∈ Lev μ' := lev_mono hμ'l.1 hμμ'
  have hXμ' : ∀ u, u ∈ hval hκ x → u ∈ Lev μ' := lev_tr hμ'l.1 _ hx
  have hgK : g ∈ Lev κ := hκ.sub (Lev μ') g (lev_mem hκO hμ'κ) hgc (fun q hq => by
    obtain ⟨u, hu, v, hv, e⟩ := mem_prodS.mp ((hgz q).mp hq).1
    rw [e]
    exact kp_mem_lev_lim hμ'l hom' (hXμ' u hu) (hupμ v hv))
  have hgtot : ∀ u, u ∈ hval hκ x → ∃ v, Pr g u v := by
    intro u hu
    obtain ⟨v₀, hv₀, hr⟩ := hF.1 u (hXδ u hu)
    let Zs : V := sepB (k := 2) (prB.comp ![1, 2, 0]) (Lev μ) ![F, u]
    have hZs : ∀ v, v ∈ Zs ↔ v ∈ Lev μ ∧ Pr F u v := fun v => mem_sepB _ _ _ v
    obtain ⟨m, hm, hmin⟩ := ltL_least hμ.1 Zs (fun z hz => ((hZs z).mp hz).1)
      ⟨v₀, (hZs v₀).mpr ⟨hv₀, pr_iff.mpr (hin_rl_iff.mp hr)⟩⟩
    obtain ⟨hmL, hmF⟩ := (hZs m).mp hm
    exact ⟨m, (hgpr u m).mpr ⟨hu, hmL, hmF, fun v' hv' hFv' => hmin v' ((hZs v').mpr ⟨hv', hFv'⟩)⟩⟩
  have hgfun : ∀ u v v', Pr g u v → Pr g u v' → v = v' := by
    intro u v v' h h'
    obtain ⟨-, hv, hFv, hmin⟩ := (hgpr u v).mp h
    obtain ⟨-, hv', hFv', hmin'⟩ := (hgpr u v').mp h'
    rcases ltL_tri hμ.1 hv hv' with k | k | k
    · exact absurd k (hmin' v hv hFv)
    · exact k
    · exact absurd k (hmin v' hv' hFv')
  have hginj : ∀ u u' v, Pr g u v → Pr g u' v → u = u' := by
    intro u u' v h h'
    obtain ⟨hu, -, hFv, -⟩ := (hgpr u v).mp h
    obtain ⟨hu', -, hFv', -⟩ := (hgpr u' v).mp h'
    exact hF.2 u u' v (hXδ u hu) (hXδ u' hu') (hin_rl_iff.mpr (pr_iff.mp hFv))
      (hin_rl_iff.mpr (pr_iff.mp hFv'))
  refine ⟨hmk hκ g hgK, ⟨fun p hp => ?_, fun a b b' h h' => ?_⟩, fun a ha => ?_,
    fun a a' c _ _ h h' => ?_⟩
  · have hp' : hval hκ p ∈ g := hp
    obtain ⟨u, hu, v, hv, e⟩ := mem_prodS.mp ((hgz _).mp hp').1
    refine ⟨hmk hκ u (hup u (hXμ' u hu)), hmk hκ v (hup v (hupμ v hv)),
      (levHost hκ).isOp_iff.mpr (hval_inj hκ _ _ ?_)⟩
    rw [op_val]
    exact e
  · exact hval_inj hκ _ _ (hgfun _ _ _ ((app_val hκ _ a b).mp h) ((app_val hκ _ a b').mp h'))
  · obtain ⟨v, hv⟩ := hgtot (hval hκ a) ha
    have hvL : v ∈ Lev μ := ((hgpr _ v).mp hv).2.1
    exact ⟨hmk hκ v (hup v (hupμ v hvL)), hvL, (app_val hκ _ a _).mpr hv⟩
  · exact hval_inj hκ _ _ (hginj _ _ _ ((app_val hκ _ a c).mp h) ((app_val hκ _ a' c).mp h'))

end dict

/-- The heights of an iterated next height, as a sequence. -/
theorem iterH_seq {ν₀ : V} : ∀ (n : ℕ) (d : V), IterH (n + 1) ν₀ d →
    ∃ μs : ℕ → V, NextH ν₀ (μs 0) ∧ (∀ j, j < n → NextH (μs j) (μs (j + 1))) ∧ μs n = d
  | 0, d, ⟨μ', h', hn⟩ => by
    rw [show μ' = ν₀ from h'] at hn
    exact ⟨fun _ => d, hn, fun j hj => absurd hj (by omega), rfl⟩
  | n + 1, d, ⟨μ', h', hn⟩ => by
    obtain ⟨μs, h0, hs, hlast⟩ := iterH_seq n μ' h'
    refine ⟨fun j => if j ≤ n then μs j else d, ?_, fun j hj => ?_, ?_⟩
    · simpa using h0
    · by_cases hjn : j < n
      · have h1 : j ≤ n := by omega
        have h2 : j + 1 ≤ n := by omega
        simp only [h1, h2, if_true]
        exact hs j hjn
      · have e : j = n := by omega
        have h2 : ¬ (n + 1 ≤ n) := by omega
        simp only [e, le_refl, if_true, h2, if_false]
        rw [hlast]
        exact hn
    · have h2 : ¬ (n + 1 ≤ n) := by omega
      simp only [h2, if_false]

/-- **The levels at consecutive next heights are consecutive closed levels of the host.** -/
theorem levSeq_lev {κ : V} (hκ : Full κ) {ν₀ : V} (hν : Lim ν₀) (hom : (om : V) ∈ ν₀)
    (μs : ℕ → V) (n : ℕ) (h0 : NextH ν₀ (μs 0)) (hs : ∀ j, j < n → NextH (μs j) (μs (j + 1)))
    (hK : μs n ∈ κ) :
    (levHost hκ).LevSeq (fun j => hmkT hκ (Lev (μs j))) (hmkT hκ (Lev ν₀)) n := by
  have hκO := hκ.lim.1
  have hlim : ∀ j, j ≤ n → Lim (μs j) ∧ (om : V) ∈ μs j := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨h0.1, h0.1.1.1 ν₀ h0.2.1 om hom⟩
    | succ j ih =>
      intro hj
      have hn := hs j (by omega)
      exact ⟨hn.1, hn.1.1.1 _ hn.2.1 om (ih (by omega)).2⟩
  have hfull : ∀ j, j ≤ n → Full (μs j) := by
    intro j hj
    rcases j with _ | j
    · exact nextH_full hν hom h0
    · exact nextH_full (hlim j (by omega)).1 (hlim j (by omega)).2 (hs j (by omega))
  have hin : ∀ k j, j + k = n → μs j ∈ κ := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have e : j = n := by omega
      rw [e]
      exact hK
    | succ k ih =>
      intro j hj
      exact hκO.1 _ (ih (j + 1) (by omega)) _ (hs j (by omega)).2.1
  have hinK : ∀ j, j ≤ n → μs j ∈ κ := fun j hj => hin (n - j) j (by omega)
  have hLK : ∀ j, j ≤ n → Lev (μs j) ∈ Lev κ := fun j hj => lev_mem hκO (hinK j hj)
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj x hx => ?_, ?_⟩
  · rw [hmkT_eq hκ (hLK j hj)]
    exact closed_lev hκ (hfull j hj) (hinK j hj)
  · show hval hκ (hmkT hκ (Lev (μs j))) ∈ hval hκ (hmkT hκ (Lev (μs (j + 1))))
    rw [hmkT_val hκ (hLK j (by omega)), hmkT_val hκ (hLK (j + 1) (by omega))]
    exact lev_mem (hlim (j + 1) (by omega)).1.1 (hs j hj).2.1
  · have hx' : hval hκ x ∈ hval hκ (hmkT hκ (Lev (μs (j + 1)))) := hx
    rw [hmkT_val hκ (hLK (j + 1) (by omega))] at hx'
    obtain ⟨g, hg, hgt, hgi⟩ := cons_lev hκ (hlim j (by omega)).1 (hlim j (by omega)).2 (hs j hj)
      (hinK (j + 1) (by omega)) x hx'
    refine ⟨g, hg, fun a ha => ?_, hgi⟩
    obtain ⟨c, hc, hac⟩ := hgt a ha
    refine ⟨c, ?_, hac⟩
    show hval hκ c ∈ hval hκ (hmkT hκ (Lev (μs j)))
    rw [hmkT_val hκ (hLK j (by omega))]
    exact hc
  · have hν₀K : ν₀ ∈ κ := hκO.1 _ (hinK 0 (by omega)) _ h0.2.1
    show hval hκ (hmkT hκ (Lev ν₀)) ∈ hval hκ (hmkT hκ (Lev (μs 0)))
    rw [hmkT_val hκ (lev_mem hκO hν₀K), hmkT_val hκ (hLK 0 (by omega))]
    exact lev_mem h0.1.1 h0.2.1

/-- **A supply for `n + 1` gives a tower and consecutive closed levels for the partition
theorem.** The ordinals of the last level are the height of the tower, and the level at the
base height is a member of the first level. -/
theorem supply_er {n : ℕ} {T : ℕ → V} {ρ Sq : V} (sup : Supply (n + 1) T ρ Sq) :
    ∃ (ν₀ K' : V) (hK' : Full K') (Tw : Host.Tower (levHost hK'))
      (Ms : ℕ → (levHost hK').W) (C : (levHost hK').W),
      Lim ν₀ ∧ (om : V) ∈ ν₀ ∧ (levHost hK').LevSeq Ms C n ∧
        (levHost hK').ords (Ms n) = Tw.d ∧ hval hK' C = Lev ν₀ := by
  obtain ⟨ν₀, d, hν, hit, K', hK', Tw, hTd, hdK'⟩ := supply_tower sup
  obtain ⟨hl, hom⟩ := hgtV_lim (sup.base 0 (by omega)) hν
  obtain ⟨μs, h0, hs, hlast⟩ := iterH_seq n d hit
  have hK : μs n ∈ K' := hlast ▸ hdK'
  have hseq := levSeq_lev hK' hl hom μs n h0 hs hK
  have hdl : Lim d := (iterH_lim hl hom (n + 1) d hit).1
  have aux : ∀ i, i ≤ n → ν₀ ∈ μs i := by
    intro i
    induction i with
    | zero => exact fun _ => h0.2.1
    | succ i ih =>
      intro hi
      exact (hs i (by omega)).1.1.1 _ (hs i (by omega)).2.1 _ (ih (by omega))
  have hν₀K : ν₀ ∈ K' := hK'.lim.1.1 _ hK _ (aux n le_rfl)
  refine ⟨ν₀, K', hK', Tw, fun j => hmkT hK' (Lev (μs j)), hmkT hK' (Lev ν₀), hl, hom, hseq, ?_,
    hmkT_val hK' (lev_mem hK'.lim.1 hν₀K)⟩
  apply hval_inj hK'
  show hval hK' ((levHost hK').ords (hmkT hK' (Lev (μs n)))) = hval hK' Tw.d
  rw [hlast, ords_val hK' hdl hdK', hTd]

end er

end MH

end FFL.FirstOrder.SetTheory
