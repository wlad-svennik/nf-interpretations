module

public import NFUSupply
public import MHInternal
public import ConNF.NF.NFUCut

@[expose] public section

set_option autoImplicit false

/-!
# The supply for a number in a cut, in a model of `𝗡𝗙𝗨𝗜𝗖`

For the interpretation `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖` the truth assignments are needed below every bound in a
definable cut of the numbers of the model, and not only below the standard bounds.

* `InJ0 m`: `m` is a finite ordinal among the types such that every type in the level `m` of
  the hierarchy over the finite ordinals (the level `V_{ω+m}`) is fixed by the type-raising
  map. This is not a stratified condition. With the Axiom of Counting it holds of zero
  (`inJ0_zero`) and is closed under successor (`inJ0_succ`) and downwards (`inJ0_down`).
* `lev_low`: the level `m` over the finite ordinals is included in the level of the pair
  `(0, m)` of a hierarchy over a lexicographic index set.
* **`exists_isupply`**: for a number `r` of the structure on the domain with `InJ0 r`, the
  structure has a supply for `r` in the sense of `MHInternal.lean` (`MH.ISupply`).
* **`sound_J`**: so there is a truth assignment, a set of the structure, that satisfies the
  instances of N and of the nine clauses below `q`, when `InJ0` holds of `8(10q + 13) + 28`.
-/

namespace Host.Nm

variable {H : Host}

instance instIsOrderedRing : IsOrderedRing (Nm H) where
  add_le_add_left := fun a b h c => by
    obtain ⟨d, hd⟩ := (le_iff a b).mp h
    exact (le_iff _ _).mpr ⟨d, by rw [← hd]; ring⟩
  zero_le_one := (le_iff 0 1).mpr ⟨1, zero_add 1⟩
  mul_le_mul_of_nonneg_left := fun a _ b c h => by
    obtain ⟨d, hd⟩ := (le_iff b c).mp h
    exact (le_iff _ _).mpr ⟨a * d, by rw [← hd]; ring⟩
  mul_le_mul_of_nonneg_right := fun a _ b c h => by
    obtain ⟨d, hd⟩ := (le_iff b c).mp h
    exact (le_iff _ _).mpr ⟨d * a, by rw [← hd]; ring⟩

instance instCanonicallyOrderedAdd : CanonicallyOrderedAdd (Nm H) where
  exists_add_of_le := fun {a b} h => by
    obtain ⟨d, hd⟩ := (le_iff a b).mp h
    exact ⟨d, hd.symm⟩
  le_add_self := fun a b => (le_iff _ _).mpr ⟨b, add_comm a b⟩
  le_self_add := fun a b => (le_iff _ _).mpr ⟨b, rfl⟩

end Host.Nm

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD Dom)

/-! ### The cut -/

section defs

variable {V : Type} [SetStructure V]

/-- **The cut**: every type in the level `m` over the finite ordinals is fixed. -/
def InJ0 (m : V) : Prop :=
  InOm m ∧ ∀ g B A RH W : V, IsEg g → IsB 0 B → (∀ α : V, α ∈ A ↔ InH B α) → IsRH A RH →
    IsWG A RH W → ∀ x : V, InLev W m x → Fixed g x

end defs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

theorem inJ0_zero (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {z : V} (hz : IsZero z) :
    InJ0 z := by
  refine ⟨om_zero hz, fun g B A RH W hg hB hA hRH hW x hx => ?_⟩
  obtain ⟨-, hxZ, h'⟩ := levG_inv hW hx
  refine om_fixed hC hg ?_
  rcases h' with h | h
  · exact h
  · refine om_zero ⟨hxZ, fun u hu => ?_⟩
    obtain ⟨b, hb, -⟩ := h u hu
    exact hz.2 b ((rl_isRH hRH b z).mp hb).2.2

theorem inJ0_succ (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {y w : V} (hy : InJ0 y)
    (hw : Succ y w) : InJ0 w := by
  refine ⟨om_succ hy.1 hw, fun g B A RH W hg hB hA hRH hW x hx => ?_⟩
  have good := isB_good hC hg 0 hB
  have ok : IdxOK g A RH := hart_idxOK hg good.fixed good.om hA (rl_isRH hRH)
  have hyA : y ∈ A := (hA y).mpr (om_inH good.om hy.1)
  obtain ⟨-, hxZ, h'⟩ := levG_inv hW hx
  rcases h' with h | h
  · exact om_fixed hC hg h
  · refine fixed_of_members hg hxZ fun u hu => ?_
    obtain ⟨b, hb, hbu⟩ := h u hu
    obtain ⟨hbA, -, hbw⟩ := (rl_isRH hRH b w).mp hb
    refine hy.2 g B A RH W hg hB hA hRH hW u ?_
    rcases (hw.2.2 b).mp hbw with k | k
    · exact levG_mono hW ok.trans hyA ((rl_isRH hRH b y).mpr ⟨hbA, hyA, k⟩) hbu
    · rw [← k]
      exact hbu

theorem inJ0_down (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {m m' : V} (hm : InJ0 m)
    (h : EE m' m) : InJ0 m' := by
  refine ⟨om_trans hm.1 h, fun g B A RH W hg hB hA hRH hW x hx => ?_⟩
  have good := isB_good hC hg 0 hB
  have ok : IdxOK g A RH := hart_idxOK hg good.fixed good.om hA (rl_isRH hRH)
  have hmA : m ∈ A := (hA m).mpr (om_inH good.om hm.1)
  have hm'A : m' ∈ A := (hA m').mpr (om_inH good.om (om_trans hm.1 h))
  exact hm.2 g B A RH W hg hB hA hRH hW x
    (levG_mono hW ok.trans hmA ((rl_isRH hRH m' m).mpr ⟨hm'A, hmA, h⟩) hx)

/-- **The level `m` over the finite ordinals is included in the level of the pair of zero and
`m`**, for a hierarchy over the lexicographic index set of `NFUSupply.lean`. -/
theorem lev_low (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {g A₁ RH₁ W₀ H A₂ R₂ W₂ z₀ : V}
    (hg : IsEg g) (hW₀ : IsWG A₁ RH₁ W₀)
    (htr₀ : ∀ a b c : V, Rl RH₁ a b → Rl RH₁ b c → Rl RH₁ a c)
    (hRH₁ : ∀ b a, Rl RH₁ b a ↔ b ∈ A₁ ∧ a ∈ A₁ ∧ EE b a) (hfinA : ∀ m, InOm m → m ∈ A₁)
    (hW₂ : IsWG A₂ R₂ W₂) (hA₂ : ∀ p, p ∈ A₂ ↔ LexA H p)
    (hR₂ : ∀ p p', Rl R₂ p p' ↔ LexR p p' H) (hz₀ : IsZero z₀) (hz₀H : z₀ ∈ H) :
    ∀ m, InOm m → ∀ x, InLev W₀ m x → ∀ p, EOp p z₀ m → InLev W₂ p x := by
  refine om_ind 0 (SDef.all (τ := ![6, 9, 6, 9]) 6 ((inLevD.comp ![2, 1, 0] 0).imp
    (SDef.all 6 ((eOpD.comp ![0, 4, 2] 0).imp (inLevD.comp ![5, 0, 1] 0)))))
    ![W₀, z₀, W₂] (fun z hz => ?_) (fun y hy ih w hw => ?_)
  · show ∀ x, InLev W₀ z x → ∀ p, EOp p z₀ z → InLev W₂ p x
    intro x hx p hp
    obtain ⟨-, hxZ, h'⟩ := levG_inv hW₀ hx
    refine levG_intro hW₂ ((hA₂ p).mpr ⟨z₀, z, hz₀H, om_zero hz, hp⟩) hxZ
      (h'.imp id fun hu u hux => ?_)
    obtain ⟨b, hb, -⟩ := hu u hux
    exact absurd ((hRH₁ b z).mp hb).2.2 (hz.2 b)
  · show ∀ x, InLev W₀ w x → ∀ p, EOp p z₀ w → InLev W₂ p x
    have ih' : ∀ x, InLev W₀ y x → ∀ p, EOp p z₀ y → InLev W₂ p x := ih
    intro x hx p hp
    have hwo : InOm w := om_succ hy hw
    obtain ⟨-, hxZ, h'⟩ := levG_inv hW₀ hx
    obtain ⟨py, hpy, -⟩ := eop_of_fixed hg (om_fixed hC hg (om_zero hz₀)) (om_fixed hC hg hy)
    refine levG_intro hW₂ ((hA₂ p).mpr ⟨z₀, w, hz₀H, hwo, hp⟩) hxZ
      (h'.imp id fun hu u hux => ?_)
    obtain ⟨b, hb, hbu⟩ := hu u hux
    obtain ⟨hbA, -, hbw⟩ := (hRH₁ b w).mp hb
    have huy : InLev W₀ y u := by
      rcases (hw.2.2 b).mp hbw with k | k
      · exact levG_mono hW₀ htr₀ (hfinA y hy) ((hRH₁ b y).mpr ⟨hbA, hfinA y hy, k⟩) hbu
      · rw [← k]
        exact hbu
    exact ⟨py, (hR₂ py p).mpr ⟨z₀, y, z₀, w, hpy, hp, hz₀H, hz₀H, hy, hwo,
      Or.inr ⟨rfl, (hw.2.2 y).mpr (Or.inr rfl)⟩⟩, ih' u huy py hpy⟩

end model

/-! ### The supply for a number in the cut -/

section isupply

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] [Nonempty D] [hH : D↓[ℒₛₑₜ] ⊧* 𝗠𝗛] {i : D → V}

/-- **With the Axiom of Counting, the structure on the domain has a supply for every number in
the cut.** The sets `P_m`, for `m ≤ r`, are the levels over the finite ordinals. `ρ` is
Hartogs' ordinal of `P_r` in the structure. Since `r` is in the cut the members of `P_r` are
fixed, so the members of `ρ` are fixed ordinals among the types, and the rest is as in
`exists_supply`. -/
theorem exists_isupply (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) {r : D} (hr : r ∈ (MH.om : D)) (hJ : InJ0 (i r)) :
    ∃ PP ρ Sq : D, MH.ISupply r PP ρ Sq := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  -- the hierarchy over the finite ordinals
  obtain ⟨B₀, hB₀⟩ := exists_B (V := V) 0
  obtain ⟨A₁, hA₁⟩ := exists_H B₀
  obtain ⟨RH₁, hRH₁⟩ := exists_isRH A₁
  obtain ⟨W₀, hW₀⟩ := exists_WG A₁ RH₁
  have good := isB_good hC hg 0 hB₀
  have ok₀ : IdxOK g A₁ RH₁ := hart_idxOK hg good.fixed good.om hA₁ (rl_isRH hRH₁)
  have hom : ∀ m : D, m ∈ (MH.om : D) → InOm (i m) := fun m hm =>
    (emb_om_iff E _).mp ((E.mem _ _).mp hm)
  have hfinA : ∀ m : V, InOm m → m ∈ A₁ := fun m hm => (hA₁ m).mpr (om_inH good.om hm)
  have hsr : ∀ m : D, m ∈ MH.sc r → m ∈ (MH.om : D) := fun m hm => by
    rcases MH.mem_sc.mp hm with h | h
    · rw [h]
      exact hr
    · exact MH.om_tr r hr m h
  have hlt : ∀ m m' : D, m ∈ m' → m' ∈ (MH.om : D) → Rl RH₁ (i m) (i m') := fun m m' h hm' =>
    (rl_isRH hRH₁ _ _).mpr ⟨hfinA _ (hom m (MH.om_tr m' hm' m h)), hfinA _ (hom m' hm'),
      (E.mem _ _).mp h⟩
  have hrA : i r ∈ A₁ := hfinA _ (hom r hr)
  obtain ⟨Lt₀, hLt₀⟩ := exists_lv (i := i) hg ok₀ hW₀ hdom hrA
  have sub_top : ∀ (m S : D), m ∈ MH.sc r → IsLv i W₀ (i m) S → ∀ z, z ∈ S → z ∈ Lt₀ := by
    intro m S hm hS z hz
    rcases MH.mem_sc.mp hm with h | h
    · subst h
      exact (E.mem z Lt₀).mpr ((hLt₀ _).mpr ((hS _).mp ((E.mem z S).mp hz)))
    · exact lv_mono ok₀ hW₀ E hS hLt₀ hrA (hlt m r h hr) z hz
  -- the function `m ↦ P_m`
  obtain ⟨SS₁, hSS₁⟩ := (SDef.ex (τ := ![6, 9]) 6 (SDef.ex 6 ((eOpD.comp ![2, 1, 0] 0).and
    (SDef.all 6 ((eeD.comp ![0, 1] 0).iff (inLevD.comp ![4, 2, 0] 0)))))).comprehensionU ![W₀]
  have hSS₁' : ∀ q, q ∈ SS₁ ↔ ∃ a w, EOp q a w ∧ ∀ v, (EE v w ↔ InLev W₀ a v) := hSS₁
  obtain ⟨PP, hPP⟩ := dom_sep E hdom (MH.prodS (MH.sc r) (℘ Lt₀)) SS₁
  have hop : ∀ ξ S : D, EOp (i (MH.kp ξ S)) (i ξ) (i S) := fun ξ S =>
    (emb_op_iff E _ ξ S).mp (MH.hin_isOp_iff.mpr rfl)
  have pp_intro : ∀ (m S : D), m ∈ MH.sc r → IsLv i W₀ (i m) S → MH.Pr PP m S :=
    fun m S hm hS => MH.pr_iff.mpr ((hPP _).mpr
      ⟨MH.mem_prodS.mpr ⟨m, hm, S, mem_power_iff.mpr (sub_top m S hm hS), rfl⟩,
        (hSS₁' _).mpr ⟨i m, i S, hop m S, hS⟩⟩)
  have pp_elim : ∀ m S : D, MH.Pr PP m S → m ∈ MH.sc r ∧ IsLv i W₀ (i m) S := by
    intro m S h
    obtain ⟨hX, hS⟩ := (hPP _).mp (MH.pr_iff.mp h)
    obtain ⟨m', hm', S', -, e⟩ := MH.mem_prodS.mp hX
    obtain ⟨e1, -⟩ := MH.kp_inj e
    obtain ⟨a, w, hq, hlv⟩ := (hSS₁' _).mp hS
    obtain ⟨e3, e4⟩ := eop_inj hq (hop m S)
    subst e3
    subst e4
    refine ⟨?_, hlv⟩
    rw [e1]
    exact hm'
  have pp_fn : ∀ m S S' : D, MH.Pr PP m S → MH.Pr PP m S' → S = S' := fun m S S' h h' =>
    emb_ext E fun z => (E.mem z S).trans (((pp_elim m S h).2 _).trans
      ((((pp_elim m S' h').2 _)).symm.trans (E.mem z S').symm))
  have pp_top : MH.Pr PP r Lt₀ := pp_intro r Lt₀ (MH.self_mem_sc r) hLt₀
  -- Hartogs' ordinal of the last set, in the structure
  obtain ⟨ρ, hρ⟩ := MH.next_exists Lt₀
  have hρO : MH.Ord ρ := MH.ord_of_ordS hρ.1
  have hρinj : ∀ ζ : D, ζ ∈ ρ → MH.VInj ζ Lt₀ := fun ζ hζ => hρ.2.2 ζ hζ
  have hart : ∀ ξ : D, MH.Ord ξ → MH.VInj ξ Lt₀ → ξ ∈ ρ := by
    intro ξ hξ hv
    rcases MH.ord_tri hξ hρO with h | h | h
    · exact h
    · rw [h] at hv
      exact (hρ.2.1 hv).elim
    · exact (hρ.2.1 (MH.vinj_dom_mono hv fun z hz => hξ.1 ρ h z hz)).elim
  -- the types that are members of the last set, and the members of `ρ`
  obtain ⟨B, hB⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehensionU ![i Lt₀]
  have hB' : ∀ v, v ∈ B ↔ EE v (i Lt₀) := hB
  have hBfix : ∀ b, b ∈ B → Fixed g b := fun b hb =>
    hJ.2 g B₀ A₁ RH₁ W₀ hg hB₀ hA₁ hRH₁ hW₀ b ((hLt₀ b).mp ((hB' b).mp hb))
  have hρfix : ∀ ζ : D, ζ ∈ ρ → Fixed g (i ζ) := fun ζ hζ =>
    hart_fixed hg hBfix (inH_of_vinj E (MH.ord_mem hρO hζ) (hρinj ζ hζ)
      fun v hv => (hB' v).mpr hv)
  obtain ⟨B₂, hB₂⟩ := ((eeD.comp (τ' := ![6, 6, 6]) ![0, 1] 0).or
    (eeD.comp ![0, 2] 0)).comprehensionU ![i Lt₀, i ρ]
  have hB₂' : ∀ v, v ∈ B₂ ↔ EE v (i Lt₀) ∨ EE v (i ρ) := hB₂
  have hB₂fix : ∀ b, b ∈ B₂ → Fixed g b := fun b hb => by
    rcases (hB₂' b).mp hb with h | h
    · exact hBfix b ((hB' b).mpr h)
    · obtain ⟨ζ, rfl⟩ := E.down _ _ h
      exact hρfix ζ ((E.mem _ _).mpr h)
  obtain ⟨H, hHs⟩ := exists_H B₂
  have hinH : ∀ ξ : D, MH.Ord ξ → (∀ ζ, ζ ∈ ξ → ζ ∈ ρ) → i ξ ∈ H := fun ξ hξ hsub =>
    (hHs _).mpr (inH_of_sub (isOrd_of_ord E hξ) fun u hu => by
      obtain ⟨ζ, rfl⟩ := E.down _ _ hu
      exact (hB₂' _).mpr (Or.inr ((E.mem _ _).mp (hsub ζ ((E.mem _ _).mpr hu)))))
  have hρH : i ρ ∈ H := hinH ρ hρO fun ζ h => h
  have hξH : ∀ ξ : D, ξ ∈ ρ → i ξ ∈ H := fun ξ hξ =>
    hinH ξ (MH.ord_mem hρO hξ) fun ζ hζ => hρO.1 ξ hξ ζ hζ
  have h0H : i (∅ : D) ∈ H := hinH ∅ MH.ord_empty fun ζ hζ => absurd hζ (by simp)
  have lo : LexOK g H := ⟨fun a ha => hart_fixed hg hB₂fix ((hHs a).mp ha),
    fun a ha => ((hHs a).mp ha).1, fun a u ha hu => (hHs u).mpr (hart_down ((hHs a).mp ha) hu),
    ⟨i ρ, hρH⟩⟩
  -- the index set and the levels
  obtain ⟨A₂, hA₂⟩ := (lexAD.comp (τ' := ![6, 7]) ![1, 0] 0).comprehensionU ![H]
  have hA₂' : ∀ p, p ∈ A₂ ↔ LexA H p := hA₂
  obtain ⟨R₂, hR₂⟩ := exists_rel 6 lexRD ![H]
  have hR₂' : ∀ p p', Rl R₂ p p' ↔ LexR p p' H := hR₂
  have ok : IdxOK g A₂ R₂ := lex_idxOK hC hg lo hA₂' hR₂'
  obtain ⟨W, hW⟩ := exists_WG A₂ R₂
  have pair : ∀ a n : V, a ∈ H → InOm n → ∃ p, EOp p a n ∧ p ∈ A₂ := fun a n ha hn => by
    obtain ⟨p, hp, -⟩ := eop_of_fixed hg (lo.fixed a ha) (om_fixed hC hg hn)
    exact ⟨p, hp, (hA₂' p).mpr ⟨a, n, ha, hn, hp⟩⟩
  have lexlt : ∀ {p p' a n a' n' : V}, EOp p a n → EOp p' a' n' → a ∈ H → a' ∈ H → InOm n →
      InOm n' → (EE a a' ∨ (a = a' ∧ EE n n')) → Rl R₂ p p' :=
    fun hp hp' ha ha' hn hn' h => (hR₂' _ _).mpr ⟨_, _, _, _, hp, hp', ha, ha', hn, hn', h⟩
  -- one step and four steps along the finite ordinals
  have step1 : ∀ (a n p : V) (L : D), a ∈ H → InOm n → EOp p a n → IsLv i W p L →
      ∃ (n' p' : V) (L' : D), InOm n' ∧ EOp p' a n' ∧ p' ∈ A₂ ∧ IsLv i W p' L' ∧
        Rl R₂ p p' ∧ ∀ x : D, (∀ z, z ∈ x → z ∈ L) → x ∈ L' := by
    intro a n p L ha hn hp hL
    obtain ⟨m, hm, hmo⟩ := om_succ_exists hn
    obtain ⟨p', hp', hp'A⟩ := pair a m ha hmo
    obtain ⟨L', hL'⟩ := exists_lv hg ok hW hdom hp'A
    have hlt := lexlt hp hp' ha ha hn hmo (Or.inr ⟨rfl, (hm.2.2 n).mpr (Or.inr rfl)⟩)
    exact ⟨m, p', L', hmo, hp', hp'A, hL', hlt, lv_pow hW E hL hL' hp'A hlt⟩
  have step4 : ∀ (a n p : V) (L : D), a ∈ H → InOm n → EOp p a n → IsLv i W p L →
      ∃ (n' p' : V) (L' : D), InOm n' ∧ EOp p' a n' ∧ p' ∈ A₂ ∧ IsLv i W p' L' ∧
        Rl R₂ p p' ∧ MH.SupRel L L' := by
    intro a n p L ha hn hp hL
    obtain ⟨n₁, p₁, L₁, hn₁, hp₁, -, hL₁, r₁, s₁⟩ := step1 a n p L ha hn hp hL
    obtain ⟨n₂, p₂, L₂, hn₂, hp₂, -, hL₂, r₂, s₂⟩ := step1 a n₁ p₁ L₁ ha hn₁ hp₁ hL₁
    obtain ⟨n₃, p₃, L₃, hn₃, hp₃, -, hL₃, r₃, s₃⟩ := step1 a n₂ p₂ L₂ ha hn₂ hp₂ hL₂
    obtain ⟨n₄, p₄, L₄, hn₄, hp₄, hp₄A, hL₄, r₄, s₄⟩ := step1 a n₃ p₃ L₃ ha hn₃ hp₃ hL₃
    exact ⟨n₄, p₄, L₄, hn₄, hp₄, hp₄A, hL₄,
      ok.trans _ _ _ (ok.trans _ _ _ (ok.trans _ _ _ r₁ r₂) r₃) r₄,
      MH.supRel_of_pow4 s₁ s₂ s₃ s₄⟩
  -- the level of the pair of zero and `r` includes the last set
  have hn₀ : InOm (i r) := hom r hr
  have hz₀ : IsZero (i (∅ : D)) := ⟨E.inZ _, fun w hw => by
    obtain ⟨w', rfl⟩ := E.down _ _ hw
    exact absurd ((E.mem w' ∅).mpr hw) (by simp)⟩
  obtain ⟨pb, hpb, hpbA⟩ := pair _ (i r) h0H hn₀
  obtain ⟨Lb, hLb⟩ := exists_lv (i := i) hg ok hW hdom hpbA
  have hlow : ∀ z : D, z ∈ Lt₀ → z ∈ Lb := fun z hz =>
    (E.mem z Lb).mpr ((hLb _).mpr (lev_low hC hg hW₀ ok₀.trans (rl_isRH hRH₁) hfinA hW hA₂' hR₂'
      hz₀ h0H (i r) hn₀ (i z) ((hLt₀ _).mp ((E.mem z Lt₀).mp hz)) pb hpb))
  have inA : ∀ {p a : V}, a ∈ H → EOp p a (i r) → p ∈ A₂ :=
    fun ha hp => (hA₂' _).mpr ⟨_, _, ha, hn₀, hp⟩
  -- the top level
  obtain ⟨pt, hpt, hptA⟩ := pair (i ρ) (i r) hρH hn₀
  obtain ⟨Lt, hLt⟩ := exists_lv (i := i) hg ok hW hdom hptA
  -- the sequence
  obtain ⟨SS, hSS⟩ := (SDef.ex (τ := ![6, 6, 9]) 6 (SDef.ex 6 (SDef.ex 6
    ((eOpD.comp ![3, 2, 1] 0).and ((eOpD.comp ![0, 2, 4] 0).and
      (SDef.all 6 ((eeD.comp ![0, 2] 0).iff
        (inLevD.comp ![6, 1, 0] 0)))))))).comprehensionU ![i r, W]
  have hSS' : ∀ q, q ∈ SS ↔
      ∃ a w p, EOp q a w ∧ (EOp p a (i r) ∧ ∀ v, (EE v w ↔ InLev W p v)) := hSS
  obtain ⟨Sq, hSq⟩ := dom_sep E hdom (MH.prodS ρ (℘ Lt)) SS
  have sq_intro : ∀ (ξ S : D) (p : V), ξ ∈ ρ → (∀ z, z ∈ S → z ∈ Lt) → EOp p (i ξ) (i r) →
      IsLv i W p S → MH.Pr Sq ξ S := fun ξ S p hξ hsub hp hS =>
    MH.pr_iff.mpr ((hSq _).mpr ⟨MH.mem_prodS.mpr ⟨ξ, hξ, S, mem_power_iff.mpr hsub, rfl⟩,
      (hSS' _).mpr ⟨i ξ, i S, p, hop ξ S, hp, hS⟩⟩)
  have sq_elim : ∀ ξ S : D, MH.Pr Sq ξ S → ξ ∈ ρ ∧ ∃ p, EOp p (i ξ) (i r) ∧ IsLv i W p S := by
    intro ξ S h
    obtain ⟨hX, hS⟩ := (hSq _).mp (MH.pr_iff.mp h)
    obtain ⟨ξ', hξ', S', -, e⟩ := MH.mem_prodS.mp hX
    obtain ⟨e1, -⟩ := MH.kp_inj e
    obtain ⟨a, w, p, hq, hp, hlv⟩ := (hSS' _).mp hS
    obtain ⟨e3, e4⟩ := eop_inj hq (hop ξ S)
    subst e3
    subst e4
    refine ⟨?_, p, hp, hlv⟩
    rw [e1]
    exact hξ'
  have low : ∀ α S : D, α ∈ ρ → MH.Pr Sq α S → ∀ z : D, z ∈ Lt₀ → z ∈ S := by
    intro α S hα hS z hz
    obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    have hzb : z ∈ Lb := hlow z hz
    rcases MH.ord_tri MH.ord_empty (MH.ord_mem hρO hα) with h | h | h
    · exact lv_mono ok hW E hLb hlv (inA (hξH α hα) hp)
        (lexlt hpb hp h0H (hξH α hα) hn₀ hn₀ (Or.inl ((E.mem _ _).mp h))) z hzb
    · rw [← h] at hp
      rw [eop_unique hp hpb] at hlv
      exact (E.mem z S).mpr ((hlv _).mpr ((hLb _).mp ((E.mem z Lb).mp hzb)))
    · exact absurd h (by simp)
  refine ⟨PP, ρ, Sq, ⟨hr, ?_, pp_fn, ?_, ?_, ?_, hρO, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm
    obtain ⟨S, hS⟩ := exists_lv (i := i) hg ok₀ hW₀ hdom (hfinA _ (hom m (hsr m hm)))
    exact ⟨S, pp_intro m S hm hS⟩
  · intro m S hS
    obtain ⟨hm, hlv⟩ := pp_elim m S hS
    exact lv_om hW₀ E hlv (hfinA _ (hom m (hsr m hm)))
  · intro m S S' hm hS hS'
    obtain ⟨-, hlv⟩ := pp_elim m S hS
    obtain ⟨hm', hlv'⟩ := pp_elim (MH.sc m) S' hS'
    exact lv_pow hW₀ E hlv hlv' (hfinA _ (hom _ (hsr _ hm')))
      (hlt m (MH.sc m) (MH.self_mem_sc m) (hsr _ hm'))
  · intro m m' S S' hmm' hm' hS hS'
    obtain ⟨-, hlv⟩ := pp_elim m S hS
    obtain ⟨-, hlv'⟩ := pp_elim m' S' hS'
    exact lv_mono ok₀ hW₀ E hlv hlv' (hfinA _ (hom _ (hsr _ hm'))) (hlt m m' hmm' (hsr _ hm'))
  · intro ξ T hT hξ hv
    rw [pp_fn r T Lt₀ hT pp_top] at hv
    exact hart ξ hξ hv
  · intro α hα
    obtain ⟨p, hp, hpA⟩ := pair (i α) (i r) (hξH α hα) hn₀
    obtain ⟨L, hL⟩ := exists_lv (i := i) hg ok hW hdom hpA
    exact ⟨L, sq_intro α L p hα (lv_mono ok hW E hL hLt hptA
      (lexlt hp hpt (hξH α hα) hρH hn₀ hn₀ (Or.inl ((E.mem _ _).mp hα)))) hp hL⟩
  · intro α S T hα hS hT z hz
    rw [pp_fn r T Lt₀ hT pp_top] at hz
    exact low α S hα hS z hz
  · intro α β S S' hαβ hβ hS hS'
    have hα : α ∈ ρ := hρO.1 β hβ α hαβ
    obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    obtain ⟨-, p', hp', hlv'⟩ := sq_elim β S' hS'
    have hp'A := inA (hξH β hβ) hp'
    have hee : EE (i α) (i β) := (E.mem _ _).mp hαβ
    obtain ⟨n₁, p₁, L₁, hn₁, hp₁, -, hL₁, -, s₁⟩ :=
      step4 (i α) (i r) p S (hξH α hα) hn₀ hp hlv
    obtain ⟨n₂, p₂, L₂, hn₂, hp₂, -, hL₂, -, s₂⟩ :=
      step4 (i α) n₁ p₁ L₁ (hξH α hα) hn₁ hp₁ hL₁
    have hlt' : Rl R₂ p₂ p' := lexlt hp₂ hp' (hξH α hα) (hξH β hβ) hn₂ hn₀ (Or.inl hee)
    exact ⟨lv_mono ok hW E hlv hlv' hp'A
        (lexlt hp hp' (hξH α hα) (hξH β hβ) hn₀ hn₀ (Or.inl hee)),
      L₁, s₁, fun C hC => lv_mono ok hW E hL₂ hlv' hp'A hlt' C (s₂ C hC)⟩

/-- **Soundness for a number whose bound is in the cut.** -/
theorem sound_J (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) {κ₀ : D} (h₀ : MH.Full κ₀) (q : (MH.levHost h₀).Nm)
    (hq : InJ0 (i (MH.hval h₀
      (8 * ((5 * q + 6) + (5 * q + 6) + 1) + 28 : (MH.levHost h₀).Nm).val))) :
    ∃ S : D, NSat (fun j : (MH.levHost h₀).Nm => MH.hval h₀ j.val ∈ S) q ∧
      CSat (fun j : (MH.levHost h₀).Nm => MH.hval h₀ j.val ∈ S) q := by
  obtain ⟨PP, ρ, Sq, sup⟩ := exists_isupply hC E hdom (MH.nv_om h₀ _) hq
  exact MH.isupply_clauses h₀ q rfl sup

/-- The cut on the numbers of a host at a full height. -/
def CutJ (i : D → V) {κ₀ : D} (h₀ : MH.Full κ₀) (a : (MH.levHost h₀).Nm) : Prop :=
  InJ0 (i (MH.hval h₀ a.val))

theorem cutJ_hyp (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i) {κ₀ : D}
    (h₀ : MH.Full κ₀) :
    NFUCut.Shortening.Hyp (CutJ i h₀) (fun n => n) (fun n => n + 1) where
  down := fun {a b} hab hb => by
    rcases Host.Nm.eq_or_succ_le a b hab with h | h
    · rw [h]
      exact hb
    · exact inJ0_down hC hb ((E.mem _ _).mp ((MH.nv_mem h₀).mpr h))
  mono := fun h => h
  step := fun _ => rfl
  «exp» := fun {a} ha => by
    show InJ0 (i (MH.hval h₀ (a + 1).val))
    exact inJ0_succ hC ha (emb_succ E _ _ (MH.nv_succ h₀ a))
  base := by
    show InJ0 (i (MH.hval h₀ (0 : (MH.levHost h₀).Nm).val))
    rw [MH.nv_zero]
    exact inJ0_zero hC ⟨E.inZ _, fun w hw => by
      obtain ⟨w', rfl⟩ := E.down _ _ hw
      exact absurd ((E.mem w' ∅).mpr hw) (by simp)⟩

/-- **The cut, closed under addition and multiplication.** -/
def CutK (i : D → V) {κ₀ : D} (h₀ : MH.Full κ₀) (a : (MH.levHost h₀).Nm) : Prop :=
  NFUCut.Shortening.K (CutJ i h₀) (fun n => n) a

/-- **Soundness on the cut.** For every number `q` of the cut there is a truth assignment, a
set of the structure on the domain, that satisfies the instances of N and of the nine clauses
below `q`. -/
theorem sound_K (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) {κ₀ : D} (h₀ : MH.Full κ₀) (q : (MH.levHost h₀).Nm)
    (hq : CutK i h₀ q) :
    ∃ S : D, NSat (fun j : (MH.levHost h₀).Nm => MH.hval h₀ j.val ∈ S) q ∧
      CSat (fun j : (MH.levHost h₀).Nm => MH.hval h₀ j.val ∈ S) q := by
  have hyp := cutJ_hyp hC E h₀
  have k1 : CutK i h₀ 1 := NFUCut.Shortening.K_one
  have kn : ∀ n : ℕ, CutK i h₀ (n : (MH.levHost h₀).Nm) := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero]
      exact NFUCut.Shortening.K_zero
    | succ n ih =>
      rw [Nat.cast_succ]
      exact NFUCut.Shortening.K_add ih k1
  have h5 := kn 5
  have h6 := kn 6
  have h8 := kn 8
  have h28 := kn 28
  have e : (8 * ((5 * q + 6) + (5 * q + 6) + 1) + 28 : (MH.levHost h₀).Nm) =
      ((8 : ℕ) : (MH.levHost h₀).Nm) * ((((5 : ℕ) : (MH.levHost h₀).Nm) * q +
        ((6 : ℕ) : (MH.levHost h₀).Nm)) + (((5 : ℕ) : (MH.levHost h₀).Nm) * q +
        ((6 : ℕ) : (MH.levHost h₀).Nm)) + 1) + ((28 : ℕ) : (MH.levHost h₀).Nm) := by
    push_cast
    rfl
  have hb : CutK i h₀ (8 * ((5 * q + 6) + (5 * q + 6) + 1) + 28) := by
    rw [e]
    have a1 := NFUCut.Shortening.K_add (NFUCut.Shortening.K_mul h5 hq) h6
    exact NFUCut.Shortening.K_add (NFUCut.Shortening.K_mul h8
      (NFUCut.Shortening.K_add (NFUCut.Shortening.K_add a1 a1) k1)) h28
  exact sound_J hC E hdom h₀ q (NFUCut.Shortening.K_sub hyp hb)

end isupply

end HinU

end FFL.FirstOrder.SetTheory
