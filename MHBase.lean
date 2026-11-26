module

public import MHHgt
public import HostArith

@[expose] public section

/-!
# The base sets of a supply: the level at `ω` maps one-to-one into the natural numbers' sets

In a model of `𝗠𝗛`:

* `vinj_succ_p`: the step from a level to the next, for a target `S` that has a pairing given by
  a set `P` (in place of the closure of `S` under the pairs of the model), and three distinct
  members that tag the three kinds of code.

* `exists_npair`: the natural numbers have such a pairing. It is `(a + b)² + a`, taken from the
  arithmetic of a host (`HostArith.lean`) at a level that satisfies Separation and Collection.

* `vinj_fin`: **every level at a natural number maps one-to-one into `ω`.** The proof takes the
  height of `ω` (`hgtV_exists`): it is not zero, and it is not a successor below `ω` by the
  step, so it is not below `ω`.

* `vinj_lev_om`: the level at `ω` maps one-to-one into every `T` that has every set of
  relations on `ω` as a member; so such a `T` satisfies `BaseS`.

* `bT`: the sets `T₀ = ℘℘(ω × ω) ∪ ω`, `Tᵢ₊₁ = ℘℘(Tᵢ × Tᵢ) ∪ ω`, with `bT_base` and `bT_step`:
  the first two conditions of a supply (`MHSupply.lean`).
-/

namespace Host

variable {H : Host}

/-- The pair of two numbers of the host, as a number: `(a + b)² + a`. -/
noncomputable def npr (H : Host) (a b : H.W) : H.W :=
  H.addW (H.mulW (H.addW a b) (H.addW a b)) a

theorem npr_om {a b : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) : H.npr a b ∈ H.om :=
  H.addW_om (H.mulW_om (H.addW_om ha hb) (H.addW_om ha hb)) ha

theorem npr_inj {a b a' b' : H.W} (ha : a ∈ H.om) (hb : b ∈ H.om) (ha' : a' ∈ H.om)
    (hb' : b' ∈ H.om) (h : H.npr a b = H.npr a' b') : a = a' ∧ b = b' := by
  have := Nm.pair_inj (⟨a, ha⟩ : Nm H) ⟨b, hb⟩ ⟨a', ha'⟩ ⟨b', hb'⟩ (Nm.ext h)
  exact ⟨congrArg Nm.val this.1, congrArg Nm.val this.2⟩

/-- The graph of the pairing of numbers, as a set of the host. -/
noncomputable def nprG (H : Host) : H.W :=
  H.sepS (H.prod (H.prod H.om H.om) H.om)
    (fun t => ∃ a b, t = H.op (H.op a b) (H.addW (H.mulW (H.addW a b) (H.addW a b)) a))
    (by hdef)

theorem mem_nprG {t : H.W} : t ∈ H.nprG ↔
    ∃ a b, a ∈ H.om ∧ b ∈ H.om ∧ t = H.op (H.op a b) (H.npr a b) := by
  unfold nprG
  rw [H.mem_sepS]
  constructor
  · rintro ⟨hp, a, b, rfl⟩
    have h1 := (H.op_mem_prod.mp hp).1
    exact ⟨a, b, (H.op_mem_prod.mp h1).1, (H.op_mem_prod.mp h1).2, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨H.op_mem_prod.mpr ⟨H.op_mem_prod.mpr ⟨ha, hb⟩, H.npr_om ha hb⟩, a, b, rfl⟩

end Host

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- `c` is the value at `a`, `b` of the pairing given by the set `P`; `SS` bounds the pairs. -/
def Pt {V : Type} [SetStructure V] (P SS c a b : V) : Prop :=
  ∃ p, p ∈ SS ∧ (IsOp p a b ∧ Pr P p c)

def ptB : BDef (k := 5) (fun V _ v ↦ Pt (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 1 ((isOpB.comp ![0, 4, 5]).and (prB.comp ![1, 0, 3]))).congr fun _ _ _ => Iff.rfl

/-- **The codes of the members of the next level, for a target with a pairing.** `c` is a code
of `x`, given codes `G` of the members of the level `L` with order `lt`: the pair of `e0` and
`e0` for `L` itself; the pair of `e1` and a code for a member of `L`; the pair of `e2` and the
pair of two pairs of codes of the parameters of a definition of `x` over `L`. -/
def CdP {V : Type} [SetStructure V] (x c G L lt S P SS e0 e1 e2 : V) : Prop :=
  (x = L ∧ Pt P SS c e0 e0) ∨
  ((x ∈ L ∧ ∃ g, g ∈ S ∧ (Pr G x g ∧ Pt P SS c e1 g)) ∨
    (∃ s, s ∈ L ∧ ∃ y₁, y₁ ∈ L ∧ ∃ y₂, y₂ ∈ L ∧ ∃ y₃, y₃ ∈ L ∧ ∃ s', s' ∈ S ∧ ∃ t₁, t₁ ∈ S ∧
      ∃ t₂, t₂ ∈ S ∧ ∃ t₃, t₃ ∈ S ∧ ∃ p₁, p₁ ∈ S ∧ ∃ p₂, p₂ ∈ S ∧ ∃ p₃, p₃ ∈ S ∧
      (Pr G s s' ∧ (Pr G y₁ t₁ ∧ (Pr G y₂ t₂ ∧ (Pr G y₃ t₃ ∧ (IsD L lt s y₁ y₂ y₃ x ∧
        (Pt P SS p₁ s' t₁ ∧ (Pt P SS p₂ t₂ t₃ ∧ (Pt P SS p₃ p₁ p₂ ∧ Pt P SS c e2 p₃))))))))))

def cdPB : BDef (k := 11) (fun V _ v ↦
    CdP (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) :=
  (((BDef.eq 0 3).and (ptB.comp ![6, 7, 1, 8, 8])).or
    (((BDef.mem 0 3).and (BDef.bex 5 ((prB.comp ![3, 1, 0]).and
      (ptB.comp ![7, 8, 2, 10, 0])))).or
    (BDef.bex 3 (BDef.bex 4 (BDef.bex 5 (BDef.bex 6 (BDef.bex 9 (BDef.bex 10 (BDef.bex 11
      (BDef.bex 12 (BDef.bex 13 (BDef.bex 14 (BDef.bex 15
        ((prB.comp ![13, 10, 6]).and ((prB.comp ![13, 9, 5]).and ((prB.comp ![13, 8, 4]).and
          ((prB.comp ![13, 7, 3]).and ((isDB.comp ![14, 15, 10, 9, 8, 7, 11]).and
            ((ptB.comp ![17, 18, 2, 6, 5]).and ((ptB.comp ![17, 18, 1, 4, 3]).and
              ((ptB.comp ![17, 18, 0, 2, 1]).and
                (ptB.comp ![17, 18, 12, 21, 0])))))))))))))))))))))).congr
    fun _ _ _ => Iff.rfl

section base

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- A code is the code of one set only. -/
theorem cdP_inj {x x' c G L lt S P SS e0 e1 e2 : V}
    (hP : ∀ c a b a' b' : V, Pt P SS c a b → Pt P SS c a' b' → a = a' ∧ b = b')
    (h01 : e0 ≠ e1) (h02 : e0 ≠ e2) (h12 : e1 ≠ e2)
    (hG : ∀ u, u ∈ L → ∀ u', u' ∈ L → ∀ v, Pr G u v → Pr G u' v → u = u')
    (h : CdP x c G L lt S P SS e0 e1 e2) (h' : CdP x' c G L lt S P SS e0 e1 e2) : x = x' := by
  rcases h with ⟨e, k0⟩ | ⟨hx, g, -, hg, k1⟩ |
    ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, s', -, t₁, -, t₂, -, t₃, -, p₁, -, p₂, -, p₃, -,
      g0, g1, g2, g3, hD, q1, q2, q3, k2⟩
  · rcases h' with ⟨e', -⟩ | ⟨-, g', -, -, k1'⟩ |
      ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, p₃', -,
        -, -, -, -, -, -, -, -, k2'⟩
    · rw [e, e']
    · exact (h01 (hP c _ _ _ _ k0 k1').1).elim
    · exact (h02 (hP c _ _ _ _ k0 k2').1).elim
  · rcases h' with ⟨-, k0'⟩ | ⟨hx', g', -, hg', k1'⟩ |
      ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, p₃', -,
        -, -, -, -, -, -, -, -, k2'⟩
    · exact (h01 (hP c _ _ _ _ k0' k1).1).elim
    · have ee := (hP c _ _ _ _ k1 k1').2
      rw [← ee] at hg'
      exact hG x hx x' hx' g hg hg'
    · exact (h12 (hP c _ _ _ _ k1 k2').1).elim
  · rcases h' with ⟨-, k0'⟩ | ⟨-, g', -, -, k1'⟩ |
      ⟨z, hz, z₁, k1z, z₂, k2z, z₃, k3z, u', -, v₁, -, v₂, -, v₃, -, r₁, -, r₂, -, r₃, -,
        f0, f1, f2, f3, hD', q1', q2', q3', k2'⟩
    · exact (h02 (hP c _ _ _ _ k0' k2).1).elim
    · exact (h12 (hP c _ _ _ _ k1' k2).1).elim
    · have e3 := (hP c _ _ _ _ k2 k2').2
      rw [← e3] at q3'
      obtain ⟨e1', e2'⟩ := hP p₃ _ _ _ _ q3 q3'
      rw [← e1'] at q1'
      rw [← e2'] at q2'
      obtain ⟨a1, a2⟩ := hP p₁ _ _ _ _ q1 q1'
      obtain ⟨a3, a4⟩ := hP p₂ _ _ _ _ q2 q2'
      rw [← a1] at f0
      rw [← a2] at f1
      rw [← a3] at f2
      rw [← a4] at f3
      rw [← hG s hs z hz s' g0 f0, ← hG y₁ h1 z₁ k1z t₁ g1 f1, ← hG y₂ h2 z₂ k2z t₂ g2 f2,
        ← hG y₃ h3 z₃ k3z t₃ g3 f3] at hD'
      exact isD_unique hD hD'

/-- **If a level maps one-to-one into `S`, so does the next level**, when `S` has a pairing
given by a set and three distinct members. -/
theorem vinj_succ_p {S δ P SS e0 e1 e2 : V} (hδ : Ord δ)
    (hPt : ∀ a b : V, a ∈ S → b ∈ S → ∃ c, c ∈ S ∧ Pt P SS c a b)
    (hP : ∀ c a b a' b' : V, Pt P SS c a b → Pt P SS c a' b' → a = a' ∧ b = b')
    (he0 : e0 ∈ S) (he1 : e1 ∈ S) (he2 : e2 ∈ S)
    (h01 : e0 ≠ e1) (h02 : e0 ≠ e2) (h12 : e1 ≠ e2)
    (h : VInj (Lev δ) S) : VInj (Lev (sc δ)) S := by
  obtain ⟨G, hG⟩ := h
  let F : V := sepB (k := 10)
    (BDef.bex 1 (BDef.bex 6 ((isOpB.comp ![2, 1, 0]).and
      (cdPB.comp ![1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12]))))
    (prodS (Lev (sc δ)) S) ![Lev (sc δ), G, Lev δ, LtS δ, S, P, SS, e0, e1, e2]
  have hFz : ∀ z, z ∈ F ↔ z ∈ prodS (Lev (sc δ)) S ∧ ∃ x, x ∈ Lev (sc δ) ∧ ∃ c, c ∈ S ∧
      (IsOp z x c ∧ CdP x c G (Lev δ) (LtS δ) S P SS e0 e1 e2) := fun z => mem_sepB _ _ _ z
  have hto : ∀ x c, x ∈ Lev (sc δ) → c ∈ S → CdP x c G (Lev δ) (LtS δ) S P SS e0 e1 e2 →
      kp x c ∈ F :=
    fun x c hx hc hcd => (hFz _).mpr ⟨mem_prodS.mpr ⟨x, hx, c, hc, rfl⟩, x, hx, c, hc,
      isOp_kp x c, hcd⟩
  have hfrom : ∀ x c, kp x c ∈ F → CdP x c G (Lev δ) (LtS δ) S P SS e0 e1 e2 := by
    intro x c hxc
    obtain ⟨-, x', -, c', -, hop, hcd⟩ := (hFz _).mp hxc
    obtain ⟨e1', e2'⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1', e2']
    exact hcd
  have hGinj : ∀ u, u ∈ Lev δ → ∀ u', u' ∈ Lev δ → ∀ v, Pr G u v → Pr G u' v → u = u' :=
    fun u hu u' hu' v h1 h2 => hG.2 u u' v hu hu' (hin_rl_iff.mpr (pr_iff.mp h1))
      (hin_rl_iff.mpr (pr_iff.mp h2))
  have hGtot : ∀ u, u ∈ Lev δ → ∃ v, v ∈ S ∧ Pr G u v := fun u hu =>
    let ⟨v, hv, hr⟩ := hG.1 u hu
    ⟨v, hv, pr_iff.mpr (hin_rl_iff.mp hr)⟩
  refine ⟨F, fun x hx => ?_, fun x x' v _ _ h1 h2 =>
    cdP_inj hP h01 h02 h12 hGinj (hfrom x v (hin_rl_iff.mp h1)) (hfrom x' v (hin_rl_iff.mp h2))⟩
  rcases lev_sc_cases hδ hx with hxδ | hin
  · obtain ⟨g, hg, hpr⟩ := hGtot x hxδ
    obtain ⟨c, hc, hcp⟩ := hPt e1 g he1 hg
    exact ⟨c, hc, hin_rl_iff.mpr (hto x c hx hc (Or.inr (Or.inl ⟨hxδ, g, hg, hpr, hcp⟩)))⟩
  · rcases hin with e | ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, hD⟩
    · obtain ⟨c, hc, hcp⟩ := hPt e0 e0 he0 he0
      exact ⟨c, hc, hin_rl_iff.mpr (hto x c hx hc (Or.inl ⟨e, hcp⟩))⟩
    · obtain ⟨s', hs', p0⟩ := hGtot s hs
      obtain ⟨t₁, ht1, p1⟩ := hGtot y₁ h1
      obtain ⟨t₂, ht2, p2⟩ := hGtot y₂ h2
      obtain ⟨t₃, ht3, p3⟩ := hGtot y₃ h3
      obtain ⟨p₁, hp1, q1⟩ := hPt s' t₁ hs' ht1
      obtain ⟨p₂, hp2, q2⟩ := hPt t₂ t₃ ht2 ht3
      obtain ⟨p₃, hp3, q3⟩ := hPt p₁ p₂ hp1 hp2
      obtain ⟨c, hc, hcp⟩ := hPt e2 p₃ he2 hp3
      exact ⟨c, hc, hin_rl_iff.mpr (hto x c hx hc
        (Or.inr (Or.inr ⟨s, hs, y₁, h1, y₂, h2, y₃, h3, s', hs', t₁, ht1, t₂, ht2, t₃, ht3,
          p₁, hp1, p₂, hp2, p₃, hp3, p0, p1, p2, p3, hD, q1, q2, q3, hcp⟩)))⟩

/-- **The natural numbers have a pairing given by a set.** -/
theorem exists_npair : ∃ P : V,
    (∀ a b : V, a ∈ (om : V) → b ∈ (om : V) →
      ∃ c, c ∈ (om : V) ∧ Pt P (prodS (om : V) om) c a b) ∧
    (∀ c a b a' b' : V, Pt P (prodS (om : V) om) c a b → Pt P (prodS (om : V) om) c a' b' →
      a = a' ∧ b = b') := by
  obtain ⟨κ, hκ, -⟩ := exists_full_above (ord_om (V := V))
  let H := levHost hκ
  have hmem : ∀ {a b : H.W}, a ∈ b → hval hκ a ∈ hval hκ b := fun h => h
  have key : ∀ a b c : V, kp (kp a b) c ∈ hval hκ H.nprG →
      ∃ a₀ b₀ : H.W, a₀ ∈ H.om ∧ b₀ ∈ H.om ∧ hval hκ a₀ = a ∧ hval hκ b₀ = b ∧
        hval hκ (H.npr a₀ b₀) = c := by
    intro a b c h
    obtain ⟨t, ht, htm⟩ := hlift hκ h
    obtain ⟨a₀, b₀, ha₀, hb₀, rfl⟩ := Host.mem_nprG.mp htm
    rw [op_val, op_val] at ht
    obtain ⟨e1, e2⟩ := kp_inj ht
    obtain ⟨e3, e4⟩ := kp_inj e1
    exact ⟨a₀, b₀, ha₀, hb₀, e3, e4, e2⟩
  refine ⟨hval hκ H.nprG, fun a b ha hb => ?_, fun c a b a' b' h h' => ?_⟩
  · rw [← om_val hκ] at ha hb
    obtain ⟨a₀, rfl, ha₀⟩ := hlift hκ ha
    obtain ⟨b₀, rfl, hb₀⟩ := hlift hκ hb
    refine ⟨hval hκ (H.npr a₀ b₀), ?_, kp (hval hκ a₀) (hval hκ b₀), ?_, isOp_kp _ _, ?_⟩
    · rw [← om_val hκ]
      exact hmem (H.npr_om ha₀ hb₀)
    · exact mem_prodS.mpr ⟨_, om_val hκ ▸ hmem ha₀, _, om_val hκ ▸ hmem hb₀, rfl⟩
    · refine pr_iff.mpr ?_
      rw [← op_val, ← op_val]
      exact hmem (Host.mem_nprG.mpr ⟨a₀, b₀, ha₀, hb₀, rfl⟩)
  · obtain ⟨p, -, hop, hpr⟩ := h
    obtain ⟨p', -, hop', hpr'⟩ := h'
    rw [isOp_iff.mp hop] at hpr
    rw [isOp_iff.mp hop'] at hpr'
    obtain ⟨a₀, b₀, ha₀, hb₀, rfl, rfl, e⟩ := key a b c (pr_iff.mp hpr)
    obtain ⟨a₁, b₁, ha₁, hb₁, rfl, rfl, e'⟩ := key a' b' c (pr_iff.mp hpr')
    have := H.npr_inj ha₀ hb₀ ha₁ hb₁ (Subtype.ext (e.trans e'.symm))
    exact ⟨congrArg (hval hκ) this.1, congrArg (hval hκ) this.2⟩

/-- **Every level at a natural number maps one-to-one into `ω`.** -/
theorem vinj_fin {n : V} (hn : n ∈ (om : V)) : VInj (Lev n) (om : V) := by
  obtain ⟨P, hPt, hP⟩ := exists_npair (V := V)
  obtain ⟨κ, hκ⟩ := hgtV_exists (om : V)
  have h0 : (∅ : V) ∈ (om : V) := empty_mem_om
  have h1 : sc (∅ : V) ∈ (om : V) := sc_mem_om h0
  have h2 : sc (sc (∅ : V)) ∈ (om : V) := sc_mem_om h1
  have n01 : (∅ : V) ≠ sc ∅ := fun e => sc_ne_empty _ e.symm
  have n02 : (∅ : V) ≠ sc (sc ∅) := fun e => sc_ne_empty _ e.symm
  have n12 : sc (∅ : V) ≠ sc (sc ∅) := fun e => n01 (sc_inj e)
  have hnot : ¬ κ ∈ (om : V) := by
    intro hκom
    rcases om_cases hκom with e | ⟨m, hm, e⟩
    · refine hκ.2.1 (vinj_of_sub fun z hz => ?_)
      rw [e, lev_empty] at hz
      exact absurd hz (by simp)
    · have hmκ : m ∈ κ := by
        rw [e]
        exact self_mem_sc m
      have := vinj_succ_p (ord_mem ord_om hm) hPt hP h0 h1 h2 n01 n02 n12 (hκ.2.2 m hmκ)
      rw [← e] at this
      exact hκ.2.1 this
  rcases ord_tri (ord_mem ord_om hn) hκ.1 with k | k | k
  · exact hκ.2.2 n k
  · rw [← k] at hnot
    exact (hnot hn).elim
  · exact (hnot (om_tr n hn κ k)).elim

/-- **The level at `ω` maps one-to-one into `T`**, when every set of relations on `ω` is a
member of `T`. -/
theorem vinj_lev_om {T : V} (hT : SupRel (om : V) T) : VInj (Lev (om : V)) T :=
  vinj_lim lim_om (fun _ hδ => vinj_fin hδ) hT

theorem baseS_of_sup {T : V} (hT : SupRel (om : V) T) : BaseS T := ⟨vinj_lev_om hT⟩

/-! ### Four steps of the power set give every set of relations -/

/-- If every set of members of `Lⱼ` is a member of `Lⱼ₊₁`, for four steps, then every set of
relations on `L₀` is a member of `L₄`. -/
theorem supRel_of_pow4 {L₀ L₁ L₂ L₃ L₄ : V}
    (h1 : ∀ x : V, (∀ z, z ∈ x → z ∈ L₀) → x ∈ L₁)
    (h2 : ∀ x : V, (∀ z, z ∈ x → z ∈ L₁) → x ∈ L₂)
    (h3 : ∀ x : V, (∀ z, z ∈ x → z ∈ L₂) → x ∈ L₃)
    (h4 : ∀ x : V, (∀ z, z ∈ x → z ∈ L₃) → x ∈ L₄) : SupRel L₀ L₄ := by
  intro C hC
  refine h4 C fun w hw => h3 w fun p hp => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prodS.mp (hC w hw p hp)
  refine h2 _ fun s hs => h1 s fun t ht => ?_
  rcases (by simpa [kp] using hs : s = {a} ∨ s = {a, b}) with rfl | rfl
  · rw [show t = a by simpa using ht]
    exact ha
  · rcases (by simpa using ht : t = a ∨ t = b) with rfl | rfl
    · exact ha
    · exact hb

/-! ### The base sets -/

/-- The sets `T₀ = ℘℘(ω × ω) ∪ ω` and `Tᵢ₊₁ = ℘℘(Tᵢ × Tᵢ) ∪ ω`. -/
noncomputable def bT : ℕ → V
  | 0 => ℘ (℘ (prodS (om : V) om)) ∪ om
  | i + 1 => ℘ (℘ (prodS (bT i) (bT i))) ∪ om

theorem mem_bT_zero {x : V} :
    x ∈ (bT 0 : V) ↔ (∀ w, w ∈ x → ∀ p, p ∈ w → p ∈ prodS (om : V) om) ∨ x ∈ (om : V) := by
  show x ∈ ℘ (℘ (prodS (om : V) om)) ∪ om ↔ _
  rw [mem_union_iff, mem_power_iff]
  refine or_congr ⟨fun h w hw => mem_power_iff.mp (h w hw), fun h w hw =>
    mem_power_iff.mpr (h w hw)⟩ Iff.rfl

theorem mem_bT_succ {i : ℕ} {x : V} :
    x ∈ (bT (i + 1) : V) ↔
      (∀ w, w ∈ x → ∀ p, p ∈ w → p ∈ prodS (bT i : V) (bT i)) ∨ x ∈ (om : V) := by
  show x ∈ ℘ (℘ (prodS (bT i : V) (bT i))) ∪ om ↔ _
  rw [mem_union_iff, mem_power_iff]
  refine or_congr ⟨fun h w hw => mem_power_iff.mp (h w hw), fun h w hw =>
    mem_power_iff.mpr (h w hw)⟩ Iff.rfl

theorem om_sub_bT (i : ℕ) {x : V} (hx : x ∈ (om : V)) : x ∈ (bT i : V) := by
  cases i with
  | zero => exact mem_bT_zero.mpr (Or.inr hx)
  | succ i => exact mem_bT_succ.mpr (Or.inr hx)

/-- Every set of relations on `Tᵢ` is a member of `Tᵢ₊₁`. -/
theorem bT_step (i : ℕ) : SupRel (bT i : V) (bT (i + 1)) :=
  fun _ hC => mem_bT_succ.mpr (Or.inl hC)

theorem bT_sup (i : ℕ) : SupRel (om : V) (bT i) := by
  intro C hC
  cases i with
  | zero => exact mem_bT_zero.mpr (Or.inl hC)
  | succ i =>
    refine mem_bT_succ.mpr (Or.inl fun w hw p hp => ?_)
    obtain ⟨a, ha, b, hb, e⟩ := mem_prodS.mp (hC w hw p hp)
    exact mem_prodS.mpr ⟨a, om_sub_bT i ha, b, om_sub_bT i hb, e⟩

/-- **The level at `ω` maps one-to-one into each of the base sets.** -/
theorem bT_base (i : ℕ) : BaseS (bT i : V) := baseS_of_sup (bT_sup i)

end base

end MH

end FFL.FirstOrder.SetTheory
