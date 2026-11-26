module

public import MHER
public import MHBase
public import HostCountI
public import CountMap

@[expose] public section

set_option autoImplicit false

/-!
# The clauses below a bound that is a number of the model of `𝗠𝗛`

`MHCountSound.lean` derives the clauses below a standard bound `q` from a supply for the
standard number `10q + 15`, by inductions in Lean. For the interpretation `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖` the
bound is a number of the model, possibly nonstandard. This file does the part inside a model
of `𝗠𝗛`.

* `full_not_linj`: the level at a full height does not map one-to-one, by a constructible
  relation, into a level below. `nextH_of_consec`: so two consecutive full heights are a height
  and its next height.
* `addW_val_eq`, `mulW_val_eq`, `nmMap`: the numbers of the hosts at two full heights are the
  same semiring: the map that keeps the value is a homomorphism of semirings that preserves the
  order.
-/

namespace Host

variable {H : Host}

/-- The graph of addition on the numbers, as a set of the host. -/
noncomputable def addG (H : Host) : H.W :=
  H.sepS (H.prod (H.prod H.om H.om) H.om)
    (fun t => ∃ a b, t = H.op (H.op a b) (H.addW a b)) (by hdef)

theorem mem_addG {t : H.W} : t ∈ H.addG ↔
    ∃ a b, a ∈ H.om ∧ b ∈ H.om ∧ t = H.op (H.op a b) (H.addW a b) := by
  unfold addG
  rw [H.mem_sepS]
  constructor
  · rintro ⟨hp, a, b, rfl⟩
    have h1 := (H.op_mem_prod.mp hp).1
    exact ⟨a, b, (H.op_mem_prod.mp h1).1, (H.op_mem_prod.mp h1).2, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨H.op_mem_prod.mpr ⟨H.op_mem_prod.mpr ⟨ha, hb⟩, H.addW_om ha hb⟩, a, b, rfl⟩

/-- The graph of multiplication on the numbers, as a set of the host. -/
noncomputable def mulG (H : Host) : H.W :=
  H.sepS (H.prod (H.prod H.om H.om) H.om)
    (fun t => ∃ a b, t = H.op (H.op a b) (H.mulW a b)) (by hdef)

theorem mem_mulG {t : H.W} : t ∈ H.mulG ↔
    ∃ a b, a ∈ H.om ∧ b ∈ H.om ∧ t = H.op (H.op a b) (H.mulW a b) := by
  unfold mulG
  rw [H.mem_sepS]
  constructor
  · rintro ⟨hp, a, b, rfl⟩
    have h1 := (H.op_mem_prod.mp hp).1
    exact ⟨a, b, (H.op_mem_prod.mp h1).1, (H.op_mem_prod.mp h1).2, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨H.op_mem_prod.mpr ⟨H.op_mem_prod.mpr ⟨ha, hb⟩, H.mulW_om ha hb⟩, a, b, rfl⟩

end Host

namespace FFL.FirstOrder.SetTheory

namespace MH

section internal

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-! ### Consecutive full heights -/

/-- **The level at a full height does not map one-to-one, by a constructible relation, into a
level below it**: the inverse of such a relation would be a constructible relation from a
member of the level that is not bounded in it. -/
theorem full_not_linj {μ μ' : V} (hμ' : Full μ') (hμ : Ord μ) (hμμ' : μ ∈ μ') :
    ¬LInj (Lev μ') (Lev μ) := by
  rintro ⟨F, hFc, hF1, hF2⟩
  have hμ'O := hμ'.lim.1
  let R : V := sepB (k := 3) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    ((prB.comp ![5, 0, 1]).or ((BDef.ball 4 ((prB.comp ![6, 0, 2]).not)).and
      (BDef.ball 0 BDef.fls)))))) (prodS (Lev μ) (Lev μ')) ![Lev μ, Lev μ', F]
  have hRz : ∀ q, q ∈ R ↔ q ∈ prodS (Lev μ) (Lev μ') ∧ ∃ u, u ∈ Lev μ ∧ ∃ v, v ∈ Lev μ' ∧
      (IsOp q u v ∧ (Pr F v u ∨ ((∀ w, w ∈ Lev μ' → ¬Pr F w u) ∧ ∀ z, z ∈ v → False))) :=
    fun q => mem_sepB _ _ _ q
  have hRc : Con R := con_sepB _ (con_prodS (con_lev hμ) (con_lev hμ'O)) _ (by
    intro i
    match i with
    | 0 => exact con_lev hμ
    | 1 => exact con_lev hμ'O
    | 2 => exact hFc)
  have hRpr : ∀ u v, kp u v ∈ R →
      v ∈ Lev μ' ∧ (Pr F v u ∨ (∀ w, w ∈ Lev μ' → ¬Pr F w u)) := by
    intro u v h
    obtain ⟨-, u', -, v', hv', hop, hor⟩ := (hRz _).mp h
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [e1, e2]
    exact ⟨hv', hor.imp id fun h => h.1⟩
  have h0 : (∅ : V) ∈ Lev μ' := empty_mem_lev hμ'O hμ'.lim.2.1
  obtain ⟨b, hb, hbt⟩ := hμ'.bd (Lev μ) R (lev_mem hμ'O hμμ') hRc (fun u hu => by
    by_cases hc : ∃ w, w ∈ Lev μ' ∧ Pr F w u
    · obtain ⟨w, hw, hwu⟩ := hc
      exact ⟨w, hw, (hRz _).mpr ⟨mem_prodS.mpr ⟨u, hu, w, hw, rfl⟩, u, hu, w, hw,
        isOp_kp u w, Or.inl hwu⟩⟩
    · exact ⟨∅, h0, (hRz _).mpr ⟨mem_prodS.mpr ⟨u, hu, ∅, h0, rfl⟩, u, hu, ∅, h0, isOp_kp u ∅,
        Or.inr ⟨fun w hw hwu => hc ⟨w, hw, hwu⟩, fun z hz => absurd hz (by simp)⟩⟩⟩)
  have hsub : ∀ v₀, v₀ ∈ Lev μ' → v₀ ∈ b := by
    intro v₀ hv₀
    obtain ⟨u, hu, hr⟩ := hF1 v₀ hv₀
    have hpr : Pr F v₀ u := pr_iff.mpr (hin_rl_iff.mp hr)
    obtain ⟨v, hvb, hkv⟩ := hbt u hu
    obtain ⟨hv, hor⟩ := hRpr u v hkv
    rcases hor with h | h
    · have e : v = v₀ := hF2 v v₀ u hv hv₀ (hin_rl_iff.mpr (pr_iff.mp h)) hr
      rw [← e]
      exact hvb
    · exact (h v₀ hv₀ hpr).elim
  exact mem_irrefl b (hsub b hb)

/-- **Two consecutive full heights are a height and its next height.** -/
theorem nextH_of_consec {μ μ' K γ₀ : V} (hμ : Full μ) (hμ' : Full μ') (hμμ' : μ ∈ μ')
    (hK : Ord K) (hμ'K : μ' ∈ K) (hγ : γ₀ ∈ μ)
    (hmin : ∀ ν, ν ∈ K → Full ν → γ₀ ∈ ν → μ ∈ ν → (μ' = ν ∨ μ' ∈ ν)) : NextH μ μ' := by
  obtain ⟨ν, hl, hmem, hn, hall⟩ := lnext_spec hμ.lim hμ.omega
  have hfull : Full ν := nextH_full hμ.lim hμ.omega ⟨hl, hmem, hn, hall⟩
  have e : ν = μ' := by
    rcases ord_tri hl.1 hμ'.lim.1 with k | k | k
    · exfalso
      rcases hmin ν (hK.1 μ' hμ'K ν k) hfull (hl.1.1 μ hmem γ₀ hγ) hmem with k' | k'
      · rw [k'] at k
        exact mem_irrefl _ k
      · exact mem_asymm k k'
    · exact k
    · exact (full_not_linj hμ' hμ.lim.1 hμμ' (hall μ' k)).elim
  rw [← e]
  exact ⟨hl, hmem, hn, hall⟩

/-! ### The numbers of the hosts at two full heights -/

section num

variable {κ : V} (hκ : Full κ)

include hκ in
theorem om_sub_lev (x : V) (hx : x ∈ (om : V)) : x ∈ Lev κ :=
  lev_tr hκ.lim.1 _ (ord_mem_lev_lim hκ.lim om hκ.omega) x hx

/-- The number of the host with a given value. -/
noncomputable def hnum (x : V) (hx : x ∈ (om : V)) : (levHost hκ).W :=
  hmk hκ x (om_sub_lev hκ x hx)

theorem hnum_val (x : V) (hx : x ∈ (om : V)) : hval hκ (hnum hκ x hx) = x := rfl

theorem hnum_om (x : V) (hx : x ∈ (om : V)) : hnum hκ x hx ∈ (levHost hκ).om := by
  show hval hκ (hnum hκ x hx) ∈ hval hκ (levHost hκ).om
  rw [om_val]
  exact hx

theorem val_om {a : (levHost hκ).W} (ha : a ∈ (levHost hκ).om) : hval hκ a ∈ (om : V) := by
  have h : hval hκ a ∈ hval hκ (levHost hκ).om := ha
  rwa [om_val] at h

/-- The graph of an operation on the numbers of the host, as a set of the model. -/
theorem pt_graph {G : (levHost hκ).W}
    {f : (levHost hκ).W → (levHost hκ).W → (levHost hκ).W}
    (hG : ∀ t, t ∈ G ↔ ∃ a b, a ∈ (levHost hκ).om ∧ b ∈ (levHost hκ).om ∧
      t = (levHost hκ).op ((levHost hκ).op a b) (f a b)) {a b c : V} :
    Pt (hval hκ G) (prodS (om : V) om) c a b ↔
      ∃ a₀ b₀ : (levHost hκ).W, a₀ ∈ (levHost hκ).om ∧ b₀ ∈ (levHost hκ).om ∧
        hval hκ a₀ = a ∧ hval hκ b₀ = b ∧ hval hκ (f a₀ b₀) = c := by
  have hmem : ∀ {x y : (levHost hκ).W}, x ∈ y → hval hκ x ∈ hval hκ y := fun h => h
  constructor
  · rintro ⟨p, -, hop, hpr⟩
    rw [isOp_iff.mp hop] at hpr
    obtain ⟨t, ht, htm⟩ := hlift hκ (pr_iff.mp hpr)
    obtain ⟨a₀, b₀, ha₀, hb₀, rfl⟩ := (hG t).mp htm
    rw [op_val, op_val] at ht
    obtain ⟨e1, e2⟩ := kp_inj ht
    obtain ⟨e3, e4⟩ := kp_inj e1
    exact ⟨a₀, b₀, ha₀, hb₀, e3, e4, e2⟩
  · rintro ⟨a₀, b₀, ha₀, hb₀, rfl, rfl, rfl⟩
    refine ⟨kp (hval hκ a₀) (hval hκ b₀),
      mem_prodS.mpr ⟨_, val_om hκ ha₀, _, val_om hκ hb₀, rfl⟩, isOp_kp _ _, pr_iff.mpr ?_⟩
    rw [← op_val, ← op_val]
    exact hmem ((hG _).mpr ⟨a₀, b₀, ha₀, hb₀, rfl⟩)

end num

/-- Induction for the comparison of two graphs on the natural numbers. -/
theorem graph_ind {G₁ G₂ : V}
    (h0 : ∀ a c c' : V, a ∈ (om : V) → Pt G₁ (prodS (om : V) om) c a ∅ →
      Pt G₂ (prodS (om : V) om) c' a ∅ → c = c')
    (hs : ∀ n : V, n ∈ (om : V) →
      (∀ a : V, a ∈ (om : V) → ∀ c : V, c ∈ (om : V) → ∀ c' : V, c' ∈ (om : V) →
        Pt G₁ (prodS (om : V) om) c a n → Pt G₂ (prodS (om : V) om) c' a n → c = c') →
      ∀ a : V, a ∈ (om : V) → ∀ c : V, c ∈ (om : V) → ∀ c' : V, c' ∈ (om : V) →
        Pt G₁ (prodS (om : V) om) c a (sc n) → Pt G₂ (prodS (om : V) om) c' a (sc n) →
        c = c') :
    ∀ n : V, n ∈ (om : V) → ∀ a : V, a ∈ (om : V) → ∀ c : V, c ∈ (om : V) →
      ∀ c' : V, c' ∈ (om : V) → Pt G₁ (prodS (om : V) om) c a n →
        Pt G₂ (prodS (om : V) om) c' a n → c = c' :=
  om_ind (k := 4)
    (BDef.ball 1 (BDef.ball 2 (BDef.ball 3 ((ptB.comp ![5, 7, 1, 2, 3]).imp
      ((ptB.comp ![6, 7, 0, 2, 3]).imp (BDef.eq 1 0))))))
    ![(om : V), G₁, G₂, prodS (om : V) om]
    (fun a ha c _ c' _ h1 h2 => h0 a c c' ha h1 h2) hs

/-- **Addition on the numbers does not depend on the host.** -/
theorem addW_val_eq {κ₁ κ₂ : V} (h₁ : Full κ₁) (h₂ : Full κ₂)
    {a₁ b₁ : (levHost h₁).W} {a₂ b₂ : (levHost h₂).W}
    (ha₁ : a₁ ∈ (levHost h₁).om) (hb₁ : b₁ ∈ (levHost h₁).om)
    (ha₂ : a₂ ∈ (levHost h₂).om) (hb₂ : b₂ ∈ (levHost h₂).om)
    (ea : hval h₁ a₁ = hval h₂ a₂) (eb : hval h₁ b₁ = hval h₂ b₂) :
    hval h₁ ((levHost h₁).addW a₁ b₁) = hval h₂ ((levHost h₂).addW a₂ b₂) := by
  have g1 := @pt_graph V _ _ _ κ₁ h₁ _ _ (fun t => (levHost h₁).mem_addG (t := t))
  have g2 := @pt_graph V _ _ _ κ₂ h₂ _ _ (fun t => (levHost h₂).mem_addG (t := t))
  refine graph_ind (G₁ := hval h₁ (levHost h₁).addG) (G₂ := hval h₂ (levHost h₂).addG)
    (fun a c c' _ k1 k2 => ?_) (fun n hn ih a ha c _ c' _ k1 k2 => ?_)
    (hval h₁ b₁) (val_om h₁ hb₁) (hval h₁ a₁) (val_om h₁ ha₁) _
    (val_om h₁ ((levHost h₁).addW_om ha₁ hb₁)) _ (val_om h₂ ((levHost h₂).addW_om ha₂ hb₂))
    (g1.mpr ⟨a₁, b₁, ha₁, hb₁, rfl, rfl, rfl⟩) (g2.mpr ⟨a₂, b₂, ha₂, hb₂, ea.symm, eb.symm, rfl⟩)
  · obtain ⟨x, y, -, -, e1, e2, e3⟩ := g1.mp k1
    obtain ⟨x', y', -, -, e1', e2', e3'⟩ := g2.mp k2
    have hy : y = (levHost h₁).emp := Subtype.ext (e2.trans (emp_val h₁).symm)
    have hy' : y' = (levHost h₂).emp := Subtype.ext (e2'.trans (emp_val h₂).symm)
    rw [hy, (levHost h₁).addW_zero, e1] at e3
    rw [hy', (levHost h₂).addW_zero, e1'] at e3'
    exact e3.symm.trans e3'
  · obtain ⟨x, y, hx, -, e1, e2, e3⟩ := g1.mp k1
    obtain ⟨x', y', hx', -, e1', e2', e3'⟩ := g2.mp k2
    have hy : y = (levHost h₁).suc (hnum h₁ n hn) :=
      Subtype.ext (e2.trans (suc_val h₁ (hnum h₁ n hn)).symm)
    have hy' : y' = (levHost h₂).suc (hnum h₂ n hn) :=
      Subtype.ext (e2'.trans (suc_val h₂ (hnum h₂ n hn)).symm)
    rw [hy, (levHost h₁).addW_suc _ (hnum_om h₁ n hn), suc_val] at e3
    rw [hy', (levHost h₂).addW_suc _ (hnum_om h₂ n hn), suc_val] at e3'
    have := ih a ha _ (val_om h₁ ((levHost h₁).addW_om hx (hnum_om h₁ n hn))) _
      (val_om h₂ ((levHost h₂).addW_om hx' (hnum_om h₂ n hn)))
      (g1.mpr ⟨x, hnum h₁ n hn, hx, hnum_om h₁ n hn, e1, rfl, rfl⟩)
      (g2.mpr ⟨x', hnum h₂ n hn, hx', hnum_om h₂ n hn, e1', rfl, rfl⟩)
    rw [← e3, ← e3', this]

/-- **Multiplication on the numbers does not depend on the host.** -/
theorem mulW_val_eq {κ₁ κ₂ : V} (h₁ : Full κ₁) (h₂ : Full κ₂)
    {a₁ b₁ : (levHost h₁).W} {a₂ b₂ : (levHost h₂).W}
    (ha₁ : a₁ ∈ (levHost h₁).om) (hb₁ : b₁ ∈ (levHost h₁).om)
    (ha₂ : a₂ ∈ (levHost h₂).om) (hb₂ : b₂ ∈ (levHost h₂).om)
    (ea : hval h₁ a₁ = hval h₂ a₂) (eb : hval h₁ b₁ = hval h₂ b₂) :
    hval h₁ ((levHost h₁).mulW a₁ b₁) = hval h₂ ((levHost h₂).mulW a₂ b₂) := by
  have g1 := @pt_graph V _ _ _ κ₁ h₁ _ _ (fun t => (levHost h₁).mem_mulG (t := t))
  have g2 := @pt_graph V _ _ _ κ₂ h₂ _ _ (fun t => (levHost h₂).mem_mulG (t := t))
  refine graph_ind (G₁ := hval h₁ (levHost h₁).mulG) (G₂ := hval h₂ (levHost h₂).mulG)
    (fun a c c' _ k1 k2 => ?_) (fun n hn ih a ha c _ c' _ k1 k2 => ?_)
    (hval h₁ b₁) (val_om h₁ hb₁) (hval h₁ a₁) (val_om h₁ ha₁) _
    (val_om h₁ ((levHost h₁).mulW_om ha₁ hb₁)) _ (val_om h₂ ((levHost h₂).mulW_om ha₂ hb₂))
    (g1.mpr ⟨a₁, b₁, ha₁, hb₁, rfl, rfl, rfl⟩) (g2.mpr ⟨a₂, b₂, ha₂, hb₂, ea.symm, eb.symm, rfl⟩)
  · obtain ⟨x, y, -, -, e1, e2, e3⟩ := g1.mp k1
    obtain ⟨x', y', -, -, e1', e2', e3'⟩ := g2.mp k2
    have hy : y = (levHost h₁).emp := Subtype.ext (e2.trans (emp_val h₁).symm)
    have hy' : y' = (levHost h₂).emp := Subtype.ext (e2'.trans (emp_val h₂).symm)
    rw [hy, (levHost h₁).mulW_zero, emp_val] at e3
    rw [hy', (levHost h₂).mulW_zero, emp_val] at e3'
    exact e3.symm.trans e3'
  · obtain ⟨x, y, hx, -, e1, e2, e3⟩ := g1.mp k1
    obtain ⟨x', y', hx', -, e1', e2', e3'⟩ := g2.mp k2
    have hy : y = (levHost h₁).suc (hnum h₁ n hn) :=
      Subtype.ext (e2.trans (suc_val h₁ (hnum h₁ n hn)).symm)
    have hy' : y' = (levHost h₂).suc (hnum h₂ n hn) :=
      Subtype.ext (e2'.trans (suc_val h₂ (hnum h₂ n hn)).symm)
    rw [hy, (levHost h₁).mulW_suc _ (hnum_om h₁ n hn)] at e3
    rw [hy', (levHost h₂).mulW_suc _ (hnum_om h₂ n hn)] at e3'
    have ih' := ih a ha _ (val_om h₁ ((levHost h₁).mulW_om hx (hnum_om h₁ n hn))) _
      (val_om h₂ ((levHost h₂).mulW_om hx' (hnum_om h₂ n hn)))
      (g1.mpr ⟨x, hnum h₁ n hn, hx, hnum_om h₁ n hn, e1, rfl, rfl⟩)
      (g2.mpr ⟨x', hnum h₂ n hn, hx', hnum_om h₂ n hn, e1', rfl, rfl⟩)
    rw [← e3, ← e3']
    exact addW_val_eq h₁ h₂ ((levHost h₁).mulW_om hx (hnum_om h₁ n hn)) hx
      ((levHost h₂).mulW_om hx' (hnum_om h₂ n hn)) hx' ih' (e1.trans e1'.symm)

/-- **The numbers of the hosts at two full heights are the same semiring**: the map that keeps
the value of a number. -/
noncomputable def nmMap {κ₁ κ₂ : V} (h₁ : Full κ₁) (h₂ : Full κ₂) :
    (levHost h₁).Nm →+* (levHost h₂).Nm where
  toFun i := ⟨hnum h₂ (hval h₁ i.val) (val_om h₁ i.prop), hnum_om h₂ _ _⟩
  map_one' := Host.Nm.ext (Subtype.ext (by
    show hval h₁ ((levHost h₁).suc (levHost h₁).emp) = hval h₂ ((levHost h₂).suc (levHost h₂).emp)
    rw [suc_val, suc_val, emp_val, emp_val]))
  map_mul' i j := Host.Nm.ext (Subtype.ext (by
    show hval h₁ ((levHost h₁).mulW i.val j.val) = hval h₂ ((levHost h₂).mulW _ _)
    exact mulW_val_eq h₁ h₂ i.prop j.prop (hnum_om h₂ _ (val_om h₁ i.prop))
      (hnum_om h₂ _ (val_om h₁ j.prop)) rfl rfl))
  map_zero' := Host.Nm.ext (Subtype.ext (by
    show hval h₁ (levHost h₁).emp = hval h₂ (levHost h₂).emp
    rw [emp_val, emp_val]))
  map_add' i j := Host.Nm.ext (Subtype.ext (by
    show hval h₁ ((levHost h₁).addW i.val j.val) = hval h₂ ((levHost h₂).addW _ _)
    exact addW_val_eq h₁ h₂ i.prop j.prop (hnum_om h₂ _ (val_om h₁ i.prop))
      (hnum_om h₂ _ (val_om h₁ j.prop)) rfl rfl))

theorem nmMap_val {κ₁ κ₂ : V} (h₁ : Full κ₁) (h₂ : Full κ₂) (i : (levHost h₁).Nm) :
    hval h₂ (nmMap h₁ h₂ i).val = hval h₁ i.val := rfl

theorem nmMap_le {κ₁ κ₂ : V} (h₁ : Full κ₁) (h₂ : Full κ₂) (a b : (levHost h₁).Nm)
    (h : a ≤ b) : nmMap h₁ h₂ a ≤ nmMap h₁ h₂ b := by
  obtain ⟨c, rfl⟩ := (Host.Nm.le_iff a b).mp h
  rw [map_add]
  exact (Host.Nm.le_iff _ _).mpr ⟨_, rfl⟩

/-! ### The values of the numbers of a host -/

section nv

variable {κ₀ : V} (h₀ : Full κ₀)

theorem nv_om (a : (levHost h₀).Nm) : hval h₀ a.val ∈ (om : V) := val_om h₀ a.prop

theorem nv_surj {x : V} (hx : x ∈ (om : V)) : ∃ a : (levHost h₀).Nm, hval h₀ a.val = x :=
  ⟨⟨hnum h₀ x hx, hnum_om h₀ x hx⟩, rfl⟩

theorem nv_inj {a b : (levHost h₀).Nm} (h : hval h₀ a.val = hval h₀ b.val) : a = b :=
  Host.Nm.ext (Subtype.ext h)

theorem nv_succ (a : (levHost h₀).Nm) : hval h₀ (a + 1).val = sc (hval h₀ a.val) := by
  rw [Host.Nm.val_succ, suc_val]

theorem nv_zero : hval h₀ (0 : (levHost h₀).Nm).val = (∅ : V) := emp_val h₀

theorem nv_mem {a b : (levHost h₀).Nm} : hval h₀ a.val ∈ hval h₀ b.val ↔ a + 1 ≤ b :=
  ((levHost h₀).arithNm).num_mem

end nv

theorem sc_mem_sc_of_mem {x y : V} (hx : Ord (sc x)) (hy : Ord y) (h : x ∈ y) :
    sc x ∈ sc y := by
  rcases ord_tri hx hy with k | k | k
  · exact mem_sc.mpr (Or.inr k)
  · exact mem_sc.mpr (Or.inl k)
  · exfalso
    rcases mem_sc.mp k with k' | k'
    · rw [k'] at h
      exact mem_irrefl _ h
    · exact mem_asymm h k'

/-! ### The supply for a number of the model -/

/-- **A supply of sets for a number `r` of the model**: sets `P 0, …, P r`, given by a set
`PP` of the model, each including `ω` and having every set of members of the one before as a
member; an ordinal `ρ` with all the ordinals that map one-to-one into `P r` as members; and a
sequence of sets indexed by `ρ`, each including `P r`, the later far above the earlier. -/
structure ISupply (r PP ρ Sq : V) : Prop where
  r_om : r ∈ (om : V)
  tot : ∀ m : V, m ∈ sc r → ∃ S : V, Pr PP m S
  fn : ∀ m S S' : V, Pr PP m S → Pr PP m S' → S = S'
  om_sub : ∀ m S : V, Pr PP m S → ∀ z, z ∈ (om : V) → z ∈ S
  step : ∀ m S S' : V, m ∈ r → Pr PP m S → Pr PP (sc m) S' →
    ∀ x : V, (∀ z, z ∈ x → z ∈ S) → x ∈ S'
  mono : ∀ m m' S S' : V, m ∈ m' → m' ∈ sc r → Pr PP m S → Pr PP m' S' →
    ∀ z, z ∈ S → z ∈ S'
  rho : Ord ρ
  hart : ∀ ξ T : V, Pr PP r T → Ord ξ → VInj ξ T → ξ ∈ ρ
  qtot : ∀ α : V, α ∈ ρ → ∃ S : V, Pr Sq α S
  low : ∀ α S T : V, α ∈ ρ → Pr Sq α S → Pr PP r T → ∀ z, z ∈ T → z ∈ S
  qmono : ∀ α β S S' : V, α ∈ β → β ∈ ρ → Pr Sq α S → Pr Sq β S' →
    (∀ z, z ∈ S → z ∈ S') ∧ Far S S'

set_option maxHeartbeats 1600000 in
/-- **The clauses below a number `q` of the model, from a supply for `8(10q + 13) + 28`.** The
truth assignment is a set of the model. The numbers are those of the host at any full height
`κ₀`. -/
theorem isupply_clauses {κ₀ : V} (h₀ : Full κ₀) (q : (levHost h₀).Nm) {r PP ρ Sq : V}
    (hr : r = hval h₀ (8 * ((5 * q + 6) + (5 * q + 6) + 1) + 28 : (levHost h₀).Nm).val)
    (sup : ISupply r PP ρ Sq) :
    ∃ S : V, NSat (fun i : (levHost h₀).Nm => hval h₀ i.val ∈ S) q ∧
      CSat (fun i : (levHost h₀).Nm => hval h₀ i.val ∈ S) q := by
  obtain ⟨n, hn⟩ : ∃ n : (levHost h₀).Nm, n = (5 * q + 6) + (5 * q + 6) + 1 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (levHost h₀).Nm, R = 8 * n + 28 := ⟨_, rfl⟩
  rw [← hn, ← hR] at hr
  have le_of : ∀ {a b : (levHost h₀).Nm} (c : (levHost h₀).Nm), a + c = b → a ≤ b :=
    fun c h => (Host.Nm.le_iff _ _).mpr ⟨c, h⟩
  have ex_of : ∀ {a b : (levHost h₀).Nm}, a ≤ b → ∃ c, a + c = b :=
    fun h => (Host.Nm.le_iff _ _).mp h
  have nf := (Host.Nm.nfacts (H := levHost h₀))
  -- the sets `P a`
  have hsr : ∀ a : (levHost h₀).Nm, a ≤ R → hval h₀ a.val ∈ sc r := by
    intro a ha
    rcases nf.eq_or_succ_le a R ha with e | e
    · rw [e, hr]
      exact self_mem_sc _
    · rw [hr]
      exact mem_sc.mpr (Or.inr ((nv_mem h₀).mpr e))
  have hP : ∀ a : (levHost h₀).Nm, a ≤ R → ∃ S, Pr PP (hval h₀ a.val) S :=
    fun a ha => sup.tot _ (hsr a ha)
  have hmonoP : ∀ (a b : (levHost h₀).Nm) (S S' : V), a ≤ b → b ≤ R →
      Pr PP (hval h₀ a.val) S → Pr PP (hval h₀ b.val) S' → ∀ z, z ∈ S → z ∈ S' := by
    intro a b S S' hab hb hS hS' z hz
    rcases nf.eq_or_succ_le a b hab with e | e
    · rw [e] at hS
      rw [← sup.fn _ _ _ hS hS']
      exact hz
    · exact sup.mono _ _ S S' ((nv_mem h₀).mpr e) (hsr b hb) hS hS' z hz
  have hstepP : ∀ (a : (levHost h₀).Nm) (S S' : V), a + 1 ≤ R →
      Pr PP (hval h₀ a.val) S → Pr PP (hval h₀ (a + 1).val) S' →
      ∀ x : V, (∀ z, z ∈ x → z ∈ S) → x ∈ S' := by
    intro a S S' ha hS hS'
    rw [nv_succ] at hS'
    exact sup.step _ S S' (hr ▸ (nv_mem h₀).mpr ha) hS hS'
  have hsup4 : ∀ (a : (levHost h₀).Nm) (S S' : V), a + 1 + 1 + 1 + 1 ≤ R →
      Pr PP (hval h₀ a.val) S → Pr PP (hval h₀ (a + 1 + 1 + 1 + 1).val) S' → SupRel S S' := by
    intro a S S' ha hS hS'
    have h3 : a + 1 + 1 + 1 ≤ R := le_trans (nf.le_add _ 1) ha
    have h2 : a + 1 + 1 ≤ R := le_trans (nf.le_add _ 1) h3
    have h1 : a + 1 ≤ R := le_trans (nf.le_add _ 1) h2
    obtain ⟨S₁, hS₁⟩ := hP _ h1
    obtain ⟨S₂, hS₂⟩ := hP _ h2
    obtain ⟨S₃, hS₃⟩ := hP _ h3
    exact supRel_of_pow4 (hstepP a S S₁ h1 hS hS₁) (hstepP _ S₁ S₂ h2 hS₁ hS₂)
      (hstepP _ S₂ S₃ h3 hS₂ hS₃) (hstepP _ S₃ S' ha hS₃ hS')
  have e4 : ∀ a : (levHost h₀).Nm, a + 1 + 1 + 1 + 1 = a + 4 := fun a => by ring
  have hfar8 : ∀ (a b : (levHost h₀).Nm) (S S' : V), a + 8 ≤ b → b ≤ R →
      Pr PP (hval h₀ a.val) S → Pr PP (hval h₀ b.val) S' → Far S S' := by
    intro a b S S' hab hb hS hS'
    have h8 : a + 4 + 4 ≤ R := le_trans (by rw [show a + 4 + 4 = a + 8 from by ring]; exact hab) hb
    have h4 : a + 4 ≤ R := le_trans (nf.le_add _ 4) h8
    obtain ⟨M, hM⟩ := hP _ h4
    obtain ⟨T, hT⟩ := hP _ h8
    have s1 : SupRel S M := hsup4 a S M (by rw [e4]; exact h4) hS (by rw [e4]; exact hM)
    have s2 : SupRel M T := hsup4 (a + 4) M T (by rw [e4]; exact h8) hM (by rw [e4]; exact hT)
    exact ⟨M, s1, fun C hC => hmonoP (a + 4 + 4) b T S'
      (by rw [show a + 4 + 4 = a + 8 from by ring]; exact hab) hb hT hS' C (s2 C hC)⟩
  have hbase : ∀ (a : (levHost h₀).Nm) (S : V), 4 ≤ a → a ≤ R →
      Pr PP (hval h₀ a.val) S → BaseS S := by
    intro a S h4a ha hS
    have h4R : (0 : (levHost h₀).Nm) + 4 ≤ R := by
      rw [zero_add]
      exact le_trans h4a ha
    obtain ⟨S₀, hS₀⟩ := hP 0 (nf.zero_le R)
    obtain ⟨S₄, hS₄⟩ := hP _ h4R
    have s : SupRel S₀ S₄ := hsup4 0 S₀ S₄ (by rw [e4]; exact h4R) hS₀ (by rw [e4]; exact hS₄)
    have s' : SupRel (om : V) S₄ := fun C hC => s C fun w hw p hp => by
      obtain ⟨x, hx, y, hy, e⟩ := mem_prodS.mp (hC w hw p hp)
      exact mem_prodS.mpr ⟨x, sup.om_sub _ S₀ hS₀ x hx, y, sup.om_sub _ S₀ hS₀ y hy, e⟩
    exact ⟨vinj_mono (vinj_lev_om s') (hmonoP (0 + 4) a S₄ S
      (by rw [zero_add]; exact h4a) ha hS₄ hS)⟩
  -- the graph of `a ↦ 8a + 4`, as a set of the model
  let H₀ := levHost h₀
  have hmem₀ : ∀ {x y : H₀.W}, x ∈ y → hval h₀ x ∈ hval h₀ y := fun h => h
  let E8h : H₀.W := H₀.sepS (H₀.prod H₀.om H₀.om)
    (fun t => ∃ j, t = H₀.op j (H₀.addW (H₀.mulW (8 : H₀.Nm).val j) (4 : H₀.Nm).val)) (by hdef)
  have hE8 : ∀ j m : V, Pr (hval h₀ E8h) j m ↔
      ∃ a : (levHost h₀).Nm, j = hval h₀ a.val ∧ m = hval h₀ (8 * a + 4).val := by
    intro j m
    constructor
    · intro h
      obtain ⟨t, ht, htm⟩ := hlift h₀ (pr_iff.mp h)
      obtain ⟨hp, j₀, rfl⟩ := H₀.mem_sepS.mp htm
      rw [op_val] at ht
      obtain ⟨e1, e2⟩ := kp_inj ht
      exact ⟨⟨j₀, (H₀.op_mem_prod.mp hp).1⟩, e1.symm, e2.symm⟩
    · rintro ⟨a, rfl, rfl⟩
      refine pr_iff.mpr ?_
      rw [← op_val]
      exact hmem₀ (H₀.mem_sepS.mpr ⟨H₀.op_mem_prod.mpr ⟨a.prop, (8 * a + 4).prop⟩, a.val, rfl⟩)
  -- the first ladder
  have hnO : Ord (hval h₀ n.val) := ord_mem ord_om (nv_om h₀ n)
  have hθO : Ord (sc (sc (hval h₀ n.val))) := ord_sc (ord_sc hnO)
  have hθom : ∀ γ, γ ∈ sc (sc (hval h₀ n.val)) → γ ∈ (om : V) := by
    intro γ hγ
    have h1 : sc (hval h₀ n.val) ∈ (om : V) := sc_mem_om (nv_om h₀ n)
    rcases mem_sc.mp hγ with e | e
    · rw [e]
      exact h1
    · exact om_tr _ h1 γ e
  have hθ : ∀ a : (levHost h₀).Nm, hval h₀ a.val ∈ sc (sc (hval h₀ n.val)) → a ≤ n + 1 := by
    intro a ha
    rcases mem_sc.mp ha with e | e
    · rw [← nv_succ] at e
      rw [nv_inj h₀ e]
    · rcases mem_sc.mp e with e' | e'
      · rw [nv_inj h₀ e']
        exact nf.le_add n 1
      · exact le_trans (nf.le_add a 1) (le_trans ((nv_mem h₀).mp e') (nf.le_add n 1))
  have i1 : ∀ a : (levHost h₀).Nm, a ≤ n + 1 → 8 * a + 4 ≤ R := by
    intro a ha
    obtain ⟨c, e⟩ := ex_of ha
    refine le_of (8 * c + 16) ?_
    rw [hR]
    calc 8 * a + 4 + (8 * c + 16) = 8 * (a + c) + 20 := by ring
      _ = 8 * (n + 1) + 20 := by rw [e]
      _ = 8 * n + 28 := by ring
  have i2 : ∀ a : (levHost h₀).Nm, a ≤ n + 1 → 8 * a + 4 + 8 ≤ 8 * (n + 2) + 4 := by
    intro a ha
    obtain ⟨c, e⟩ := ex_of ha
    refine le_of (8 * c) ?_
    calc 8 * a + 4 + 8 + 8 * c = 8 * (a + c) + 12 := by ring
      _ = 8 * (n + 1) + 12 := by rw [e]
      _ = 8 * (n + 2) + 4 := by ring
  have i3 : 8 * (n + 2) + 4 + 8 ≤ R := le_of 0 (by rw [hR]; ring)
  have i4 : 8 * (n + 2) + 4 ≤ R := le_trans (nf.le_add _ 8) i3
  have i5 : ∀ a a' : (levHost h₀).Nm, a + 1 ≤ a' → 8 * a + 4 + 8 ≤ 8 * a' + 4 := by
    intro a a' h
    obtain ⟨c, e⟩ := ex_of h
    refine le_of (8 * c) ?_
    rw [← e]
    ring
  have i6 : ∀ a : (levHost h₀).Nm, 4 ≤ 8 * a + 4 := fun a => le_of (8 * a) (by ring)
  have i7 : (4 : (levHost h₀).Nm) ≤ R := le_of (8 * n + 24) (by rw [hR]; ring)
  obtain ⟨TR, hTR⟩ := hP R (le_refl R)
  rw [← hr] at hTR
  obtain ⟨UA, hUA⟩ := hP _ i4
  let SqA : V := sepB (k := 5) (BDef.bex 1 (BDef.bex 3 (BDef.bex 5 ((isOpB.comp ![3, 2, 1]).and
    ((prB.comp ![7, 2, 0]).and (prB.comp ![8, 0, 1]))))))
    (prodS (sc (sc (hval h₀ n.val))) (℘ TR))
    ![sc (sc (hval h₀ n.val)), ℘ TR, (om : V), hval h₀ E8h, PP]
  have hSqAz : ∀ p, p ∈ SqA ↔ p ∈ prodS (sc (sc (hval h₀ n.val))) (℘ TR) ∧
      ∃ j, j ∈ sc (sc (hval h₀ n.val)) ∧ ∃ S, S ∈ ℘ TR ∧ ∃ m, m ∈ (om : V) ∧
        (IsOp p j S ∧ (Pr (hval h₀ E8h) j m ∧ Pr PP m S)) := fun p => mem_sepB _ _ _ p
  have hSqA : ∀ j S : V, Pr SqA j S ↔ j ∈ sc (sc (hval h₀ n.val)) ∧
      ∃ a : (levHost h₀).Nm, j = hval h₀ a.val ∧ Pr PP (hval h₀ (8 * a + 4).val) S := by
    intro j S
    rw [pr_iff, hSqAz]
    constructor
    · rintro ⟨-, j', hj', S', -, m, -, hop, h1, h2⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      obtain ⟨a, ea, em⟩ := (hE8 j' m).mp h1
      rw [em] at h2
      exact ⟨hj', a, ea, h2⟩
    · rintro ⟨hj, a, rfl, hS⟩
      have ha := hθ a hj
      have hSTR : S ∈ ℘ TR := mem_power_iff.mpr
        (hmonoP (8 * a + 4) R S TR (i1 a ha) (le_refl R) hS (hr ▸ hTR))
      exact ⟨mem_prodS.mpr ⟨_, hj, S, hSTR, rfl⟩, _, hj, S, hSTR, _, nv_om h₀ (8 * a + 4),
        isOp_kp _ _, (hE8 _ _).mpr ⟨a, rfl, rfl⟩, hS⟩
  have hSqA' : ∀ γ S : V, γ ∈ sc (sc (hval h₀ n.val)) → Pr SqA γ S →
      ∃ a : (levHost h₀).Nm, γ = hval h₀ a.val ∧ a ≤ n + 1 ∧
        Pr PP (hval h₀ (8 * a + 4).val) S := by
    intro γ S hγ hS
    obtain ⟨-, a, rfl, hS'⟩ := (hSqA γ S).mp hS
    exact ⟨a, rfl, hθ a hγ, hS'⟩
  have hbaseA : ∀ γ S : V, γ ∈ sc (sc (hval h₀ n.val)) → Pr SqA γ S → BaseS S := by
    intro γ S hγ hS
    obtain ⟨a, -, ha, hS'⟩ := hSqA' γ S hγ hS
    exact hbase _ S (i6 a) (i1 a ha) hS'
  have hbaseUA : BaseS UA := hbase _ UA (le_trans (i6 (n + 2)) (le_refl _)) i4 hUA
  have ladA : Ladder (sc (sc (hval h₀ n.val))) SqA UA (om : V) :=
    { tot := fun γ hγ => by
        obtain ⟨a, rfl⟩ := nv_surj h₀ (hθom γ hγ)
        obtain ⟨S, hS⟩ := hP _ (i1 a (hθ a hγ))
        exact ⟨S, (hSqA _ S).mpr ⟨hγ, a, rfl, hS⟩⟩
      base := hbaseA
      sub := fun γ S hγ hS => by
        obtain ⟨a, -, ha, hS'⟩ := hSqA' γ S hγ hS
        exact hmonoP _ _ S UA (le_trans (nf.le_add _ 8) (i2 a ha)) i4 hS' hUA
      top := fun γ S hγ hS => by
        obtain ⟨a, -, ha, hS'⟩ := hSqA' γ S hγ hS
        exact hfar8 _ _ S UA (i2 a ha) i4 hS' hUA
      far := fun γ γ' S S' hγγ' hγ' hS hS' => by
        have hγ : γ ∈ sc (sc (hval h₀ n.val)) := hθO.1 γ' hγ' γ hγγ'
        obtain ⟨a, rfl, ha, hSa⟩ := hSqA' γ S hγ hS
        obtain ⟨a', rfl, ha', hSa'⟩ := hSqA' γ' S' hγ' hS'
        exact hfar8 _ _ S S' (i5 a a' ((nv_mem h₀).mp hγγ')) (i1 a' ha') hSa hSa'
      low := fun γ S hγ hS => (hbaseA γ S hγ hS).om
      baseU := hbaseUA }
  obtain ⟨KA, LamA, hKA, hLamc, hLamsub, hLamf, hLammono, hKAF, hcons⟩ :=
    exists_ladder' hθO ord_om ladA
  have hKAO := hKA.lim.1
  -- the height of the tower
  obtain ⟨d, hdK, hdfull, -, hdA⟩ := hLamf (sc (hval h₀ n.val)) (self_mem_sc _)
  have hdO := hdfull.lim.1
  have hd0 : d ≠ ∅ := by
    intro e
    have := hdfull.omega
    rw [e] at this
    exact absurd this (by simp)
  -- the second ladder
  have hfarTR : Far UA TR := hfar8 _ _ UA TR i3 (le_refl R) hUA (hr ▸ hTR)
  have hbaseTR : BaseS TR := hbase R TR i7 (le_refl R) (hr ▸ hTR)
  have hvK : VInj (Lev KA) TR := hgtF_far hbaseUA hKAF hfarTR
  have hρ : ∀ ξ, ξ ∈ KA → ξ ∈ ρ := fun ξ hξ => sup.hart ξ TR hTR (ord_mem hKAO hξ)
    (vinj_dom_mono hvK fun z hz => ord_mem_lev_lim hKA.lim z (hKAO.1 ξ hξ z hz))
  have hτK : sc (sc d) ∈ KA := hKA.lim.2.2 _ (hKA.lim.2.2 d hdK)
  have hτO : Ord (sc (sc d)) := ord_sc (ord_sc hdO)
  have hτρ : sc (sc d) ∈ ρ := hρ _ hτK
  have hin : ∀ γ, γ ∈ sc (sc d) → γ ∈ ρ := fun γ hγ => hρ γ (hKAO.1 _ hτK γ hγ)
  obtain ⟨U, hU⟩ := sup.qtot _ hτρ
  have hfarS : ∀ S : V, (∀ z, z ∈ TR → z ∈ S) → Far UA S := fun S hS =>
    let ⟨M, k1, k2⟩ := hfarTR
    ⟨M, k1, fun C hC => hS C (k2 C hC)⟩
  have sbase : ∀ α S : V, α ∈ ρ → Pr Sq α S → BaseS S := fun α S hα hS =>
    ⟨vinj_mono hbaseTR.om (sup.low α S TR hα hS hTR)⟩
  have ladB : Ladder (sc (sc d)) Sq U (sc (sc d)) :=
    { tot := fun γ hγ => sup.qtot γ (hin γ hγ)
      base := fun γ S hγ hS => sbase γ S (hin γ hγ) hS
      sub := fun γ S hγ hS => (sup.qmono γ _ S U hγ hτρ hS hU).1
      top := fun γ S hγ hS => (sup.qmono γ _ S U hγ hτρ hS hU).2
      far := fun γ γ' S S' hγγ' hγ' hS hS' => (sup.qmono γ γ' S S' hγγ' (hin γ' hγ') hS hS').2
      low := fun γ S hγ hS => vinj_mono (vinj_dom_mono hvK (lev_mono hKAO hτK))
        (sup.low γ S TR (hin γ hγ) hS hTR)
      baseU := sbase _ U hτρ hU }
  obtain ⟨KB, hKBF, htow⟩ := exists_level_tower_at hdO hd0 hτO (self_mem_sc (sc d)) ladB
  have hKAKB : KA ∈ KB := hgtF_lt hbaseUA hKAF hKBF (hfarS U (sup.low _ U TR hτρ hU hTR))
  obtain ⟨K', hK', hKBK'⟩ := exists_full_above (hgtF_ord hKBF)
  have hK'O := hK'.lim.1
  have hKAK' : KA ∈ K' := hK'O.1 KB hKBK' KA hKAKB
  obtain ⟨Tw, hTwd, hdK'⟩ := htow K' hK' hKBK'
  -- the host and the sequence of levels in it
  have hupK : ∀ x, x ∈ Lev KA → x ∈ Lev K' := lev_mono hK'O hKAK'
  have hθLK : ∀ α, α ∈ sc (sc (hval h₀ n.val)) → α ∈ Lev KA := fun α hα =>
    ord_mem_lev_lim hKA.lim α (hKAO.1 om hKA.omega α (hθom α hα))
  have hLamK' : LamA ∈ Lev K' := hK'.sub (Lev KA) LamA (lev_mem hK'O hKAK') hLamc (fun p hp => by
    obtain ⟨α, hα, A, hA, e⟩ := mem_prodS.mp (hLamsub p hp)
    rw [e]
    exact kp_mem_lev_lim hKA.lim hKA.omega (hθLK α hα) hA)
  have hdomθ : ∀ α A, Pr LamA α A → α ∈ sc (sc (hval h₀ n.val)) := by
    intro α A h
    obtain ⟨α', hα', A', -, e⟩ := mem_prodS.mp (hLamsub _ (pr_iff.mp h))
    rw [(kp_inj e).1]
    exact hα'
  let H := levHost hK'
  have hmem : ∀ {x y : H.W}, x ∈ y → hval hK' x ∈ hval hK' y := fun h => h
  have happ : ∀ a b : H.W, H.App (hmk hK' LamA hLamK') a b ↔
      Pr LamA (hval hK' a) (hval hK' b) := fun a b => app_val hK' _ a b
  have hlev : ∀ α, α ∈ sc (sc (hval h₀ n.val)) → ∃ μ, μ ∈ K' ∧ Full μ ∧
      ∀ A, (Pr LamA α A ↔ A = Lev μ) := fun α hα =>
    let ⟨μ, hμK, hμfull, _, hA⟩ := hLamf α hα
    ⟨μ, hK'O.1 KA hKAK' μ hμK, hμfull, hA⟩
  have hn' : hval hK' ((5 * nmMap h₀ hK' q + 6) + (5 * nmMap h₀ hK' q + 6) + 1 :
      (levHost hK').Nm).val = hval h₀ n.val := by
    have e : ((5 * nmMap h₀ hK' q + 6) + (5 * nmMap h₀ hK' q + 6) + 1 : (levHost hK').Nm) =
        nmMap h₀ hK' n := by
      rw [hn]
      simp only [map_add, map_mul, map_one, map_ofNat]
    rw [e]
    rfl
  obtain ⟨n', hn'def⟩ : ∃ n' : (levHost hK').Nm,
      n' = (5 * nmMap h₀ hK' q + 6) + (5 * nmMap h₀ hK' q + 6) + 1 := ⟨_, rfl⟩
  rw [← hn'def] at hn'
  have hRd : Def2 H (fun j M => ∃ s, H.IsSuc s j ∧ H.App (hmk hK' LamA hLamK') s M) := by hdef
  have hRfun : ∀ u ∈ H.suc n'.val, ∀ v v',
      (∃ s, H.IsSuc s u ∧ H.App (hmk hK' LamA hLamK') s v) →
      (∃ s, H.IsSuc s u ∧ H.App (hmk hK' LamA hLamK') s v') → v = v' := by
    rintro u - v v' ⟨s, hs, h1⟩ ⟨s', hs', h2⟩
    rw [H.isSuc_iff.mp hs] at h1
    rw [H.isSuc_iff.mp hs'] at h2
    have k1 := (happ _ _).mp h1
    have k2 := (happ _ _).mp h2
    obtain ⟨μ, -, -, hA⟩ := hlev _ (hdomθ _ _ k1)
    exact Subtype.ext (((hA _).mp k1).trans ((hA _).mp k2).symm)
  obtain ⟨Ms, hMsdef⟩ : ∃ Ms, Ms = H.mkFun (H.suc n'.val) _ hRd hRfun := ⟨_, rfl⟩
  have hMs : ∀ j M : H.W, H.App Ms j M ↔
      j ∈ H.suc n'.val ∧ Pr LamA (sc (hval hK' j)) (hval hK' M) := by
    intro j M
    rw [hMsdef, H.app_mkFun]
    refine and_congr Iff.rfl ⟨?_, fun h => ⟨H.suc j, H.isSuc_iff.mpr rfl, ?_⟩⟩
    · rintro ⟨s, hs, h⟩
      rw [H.isSuc_iff.mp hs] at h
      have := (happ _ _).mp h
      rwa [suc_val] at this
    · refine (happ _ _).mpr ?_
      rw [suc_val]
      exact h
  have hjθ : ∀ j : H.W, j ∈ H.suc n'.val → sc (hval hK' j) ∈ sc (sc (hval h₀ n.val)) := by
    intro j hj
    have h : hval hK' j ∈ hval hK' (H.suc n'.val) := hj
    rw [suc_val, hn'] at h
    rcases mem_sc.mp h with e | e
    · rw [e]
      exact self_mem_sc _
    · exact sc_mem_sc_of_mem (ord_sc (ord_mem hnO e)) (ord_sc hnO) (mem_sc.mpr (Or.inr e))
  -- the first level is the member `C`
  have h0θ : (∅ : V) ∈ sc (sc (hval h₀ n.val)) := by
    rcases ord_tri ord_empty hθO with k | k | k
    · exact k
    · exact absurd k.symm (sc_ne_empty _)
    · exact absurd k (by simp)
  obtain ⟨μ₀, hμ₀K', hμ₀full, hA₀⟩ := hlev ∅ h0θ
  have hLemp : Pr LamA ∅ (Lev μ₀) := (hA₀ _).mpr rfl
  have hl : H.LevSeqI Ms (hmk hK' (Lev μ₀) (lev_mem hK'O hμ₀K')) n'.val :=
    { n_om := n'.prop
      tot := fun j hj => by
        obtain ⟨μ, hμK', -, hA⟩ := hlev _ (hjθ j hj)
        exact ⟨hmk hK' (Lev μ) (lev_mem hK'O hμK'), (hMs _ _).mpr ⟨hj, (hA _).mpr rfl⟩⟩
      closed := fun j M hj hM => by
        obtain ⟨μ, hμK', hμfull, hA⟩ := hlev _ (hjθ j hj)
        have e : M = hmk hK' (Lev μ) (lev_mem hK'O hμK') :=
          Subtype.ext ((hA _).mp ((hMs _ _).mp hM).2)
        rw [e]
        exact closed_lev hK' hμfull hμK'
      mem := fun j M M' hj hM hM' => by
        have h1 := ((hMs _ _).mp hM).2
        have h2 := ((hMs _ _).mp hM').2
        rw [suc_val] at h2
        exact hLammono _ _ _ _ (self_mem_sc _) (hdomθ _ _ h2) h1 h2
      cons := fun j M M' hj hM hM' x hx => by
        have h1 := ((hMs _ _).mp hM).2
        have h2 := ((hMs _ _).mp hM').2
        rw [suc_val] at h2
        obtain ⟨a, a', haK, ha'K, hafull, ha'full, haa', hpa, hpa', hmin⟩ :=
          hcons _ (hdomθ _ _ h2)
        obtain ⟨μ, -, -, hA⟩ := hlev _ (hdomθ _ _ h1)
        obtain ⟨μ', -, -, hA'⟩ := hlev _ (hdomθ _ _ h2)
        have eM : hval hK' M = Lev a := ((hA _).mp h1).trans ((hA _).mp hpa).symm
        have eM' : hval hK' M' = Lev a' := ((hA' _).mp h2).trans ((hA' _).mp hpa').symm
        have hnx : NextH a a' :=
          nextH_of_consec hafull ha'full haa' hKAO ha'K hafull.omega hmin
        have hx' : hval hK' x ∈ Lev a' := by
          rw [← eM']
          exact hx
        obtain ⟨g, hg, hgt, hgi⟩ := cons_lev hK' hafull.lim hafull.omega hnx
          (hK'O.1 KA hKAK' a' ha'K) x hx'
        refine ⟨g, hg, fun z hz => ?_, hgi⟩
        obtain ⟨c, hc, hzc⟩ := hgt z hz
        refine ⟨c, ?_, hzc⟩
        show hval hK' c ∈ hval hK' M
        rw [eM]
        exact hc
      hC := fun M hM => by
        have h1 := ((hMs _ _).mp hM).2
        rw [emp_val] at h1
        have h2 : Lev μ₀ ∈ hval hK' M :=
          hLammono ∅ (sc ∅) _ _ (self_mem_sc ∅) (hdomθ _ _ h1) hLemp h1
        exact h2 }
  have hdK'2 : d ∈ K' := hK'O.1 KA hKAK' d hdK
  have hMtop : H.App Ms n'.val (hmk hK' (Lev d) (lev_mem hK'O hdK'2)) :=
    (hMs _ _).mpr ⟨H.mem_suc.mpr (Or.inr rfl), by
      rw [hn']
      exact (hdA _).mpr rfl⟩
  have hCcl : H.Closed (hmk hK' (Lev μ₀) (lev_mem hK'O hμ₀K')) :=
    closed_lev hK' hμ₀full hμ₀K'
  have hords : H.ords (hmk hK' (Lev d) (lev_mem hK'O hdK'2)) = Tw.d := by
    refine Subtype.ext ?_
    have h1 := ords_val hK' hdfull.lim hdK'2
    rw [hmkT_eq hK' (lev_mem hK'O hdK'2)] at h1
    exact h1.trans hTwd.symm
  subst hn'def
  obtain ⟨Sh, hNS, hCS⟩ := Tw.count_clausesI (nmMap h₀ hK' q) hl hMtop hCcl hords
  exact ⟨hval hK' Sh, hNS.map (nmMap h₀ hK') (nmMap_le h₀ hK'),
    hCS.map (nmMap h₀ hK') (nmMap_le h₀ hK')⟩

end internal

end MH

end FFL.FirstOrder.SetTheory
