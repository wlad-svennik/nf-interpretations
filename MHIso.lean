module

public import MHCard

@[expose] public section

set_option autoImplicit false

/-!
# Isomorphisms of constructible well-orderings are constructible

In a model of `𝗠𝗛`. Let `A` and `B` be constructible sets of members of a level, and let `π` be
a relation of the model that is an isomorphism from `A` onto `B` for the order `LtL` of the
constructible sets (`OIso π A B`). Then `π`, cut down to `A × B`, is a constructible set:
`oiso_con`.

The proof is that of the comparability of well-orderings. `IsoR f a b A B Q`: `f` is an
isomorphism from the members of `A` up to `a` onto the members of `B` up to `b` (`Q` gives the
order). Such an `f` agrees with `π`, and `b` is the value of `π` at `a` (`IsoCtx.rigid`). For
every `a` there is such an `f` in one fixed level (`IsoCtx.seg_exists`), by induction on `a`:
the union of the earlier ones is defined by a bounded formula from constructible parameters,
so it is constructible, and it is a subset of a level, so it is in the fixed level by
`bound_exists`. Hence `π` is defined by a bounded formula from constructible parameters.

This is used to show that the collapse of a constructible hull is constructible, without
building the collapse inside the constructible sets.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- `f` is an isomorphism from the members of `A` up to `a` onto the members of `B` up to `b`,
for the order given by the pairs in `Q`. -/
def IsoR {V : Type} [SetStructure V] (f a b A B Q : V) : Prop :=
  (∀ u, u ∈ A → (Pr Q u a ∨ u = a) → ∃ v, v ∈ B ∧ ((Pr Q v b ∨ v = b) ∧ Pr f u v)) ∧
  ((∀ v, v ∈ B → (Pr Q v b ∨ v = b) → ∃ u, u ∈ A ∧ ((Pr Q u a ∨ u = a) ∧ Pr f u v)) ∧
    (∀ u, u ∈ A → ∀ u', u' ∈ A → ∀ v, v ∈ B → ∀ v', v' ∈ B → (Pr Q u a ∨ u = a) →
      (Pr Q u' a ∨ u' = a) → Pr f u v → Pr f u' v' → (Pr Q u u' ↔ Pr Q v v')))

def isoRB : BDef (k := 6) (fun V _ v ↦ IsoR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  ((BDef.ball 3 (((prB.comp ![6, 0, 2]).or (BDef.eq 0 2)).imp
      (BDef.bex 5 (((prB.comp ![7, 0, 4]).or (BDef.eq 0 4)).and (prB.comp ![2, 1, 0]))))).and
    ((BDef.ball 4 (((prB.comp ![6, 0, 3]).or (BDef.eq 0 3)).imp
      (BDef.bex 4 (((prB.comp ![7, 0, 3]).or (BDef.eq 0 3)).and (prB.comp ![2, 0, 1]))))).and
    (BDef.ball 3 (BDef.ball 4 (BDef.ball 6 (BDef.ball 7
      (((prB.comp ![9, 3, 5]).or (BDef.eq 3 5)).imp
        (((prB.comp ![9, 2, 5]).or (BDef.eq 2 5)).imp
          ((prB.comp ![4, 3, 1]).imp ((prB.comp ![4, 2, 0]).imp
            ((prB.comp ![9, 3, 2]).iff (prB.comp ![9, 1, 0])))))))))))).congr
    fun _ _ _ => Iff.rfl

/-- Some member of `K` is an isomorphism from the members of `A` up to `u` onto the members of
`B` up to `v`. -/
def PiR {V : Type} [SetStructure V] (u v A B Q K : V) : Prop := ∃ f, f ∈ K ∧ IsoR f u v A B Q

def piRB : BDef (k := 6) (fun V _ v ↦ PiR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 5 (isoRB.comp ![0, 1, 2, 3, 4, 5])).congr fun _ _ _ => Iff.rfl

section iso

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `π` is an isomorphism from `A` onto `B` for the order of the constructible sets. It is a
relation; only its pairs in `A × B` matter. -/
def OIso (π A B : V) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B ∧ Pr π a b) ∧ ((∀ b, b ∈ B → ∃ a, a ∈ A ∧ Pr π a b) ∧
    (∀ a, a ∈ A → ∀ a', a' ∈ A → ∀ b, b ∈ B → ∀ b', b' ∈ B → Pr π a b → Pr π a' b' →
      (LtL a a' ↔ LtL b b')))

/-- `IsoR` with the order of the constructible sets. -/
def IsoL (f a b A B : V) : Prop :=
  (∀ u, u ∈ A → (LtL u a ∨ u = a) → ∃ v, v ∈ B ∧ ((LtL v b ∨ v = b) ∧ Pr f u v)) ∧
  ((∀ v, v ∈ B → (LtL v b ∨ v = b) → ∃ u, u ∈ A ∧ ((LtL u a ∨ u = a) ∧ Pr f u v)) ∧
    (∀ u, u ∈ A → ∀ u', u' ∈ A → ∀ v, v ∈ B → ∀ v', v' ∈ B → (LtL u a ∨ u = a) →
      (LtL u' a ∨ u' = a) → Pr f u v → Pr f u' v' → (LtL u u' ↔ LtL v v')))

/-- The data: `A` and `B` are sets of members of the level at the limit ordinal `lam`, `Q`
gives the order on that level, and `π` is an isomorphism from `A` onto `B`. -/
structure IsoCtx (A B π lam Q : V) : Prop where
  lim : Lim lam
  al : ∀ a, a ∈ A → a ∈ Lev lam
  bl : ∀ b, b ∈ B → b ∈ Lev lam
  q : ∀ x y, x ∈ Lev lam → y ∈ Lev lam → (Pr Q x y ↔ LtL x y)
  iso : OIso π A B

namespace IsoCtx

variable {A B π lam Q : V} (c : IsoCtx A B π lam Q)

include c

theorem pi_fun {a b b' : V} (ha : a ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h1 : Pr π a b)
    (h2 : Pr π a b') : b = b' := by
  rcases ltL_tri c.lim.1 (c.bl b hb) (c.bl b' hb') with e | e | e
  · exact absurd ((c.iso.2.2 a ha a ha b hb b' hb' h1 h2).mpr e)
      (ltL_irrefl' c.lim.1 (c.al a ha))
  · exact e
  · exact absurd ((c.iso.2.2 a ha a ha b' hb' b hb h2 h1).mpr e)
      (ltL_irrefl' c.lim.1 (c.al a ha))

theorem pi_inj {a a' b : V} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (h1 : Pr π a b)
    (h2 : Pr π a' b) : a = a' := by
  rcases ltL_tri c.lim.1 (c.al a ha) (c.al a' ha') with e | e | e
  · exact absurd ((c.iso.2.2 a ha a' ha' b hb b hb h1 h2).mp e)
      (ltL_irrefl' c.lim.1 (c.bl b hb))
  · exact e
  · exact absurd ((c.iso.2.2 a' ha' a ha b hb b hb h2 h1).mp e)
      (ltL_irrefl' c.lim.1 (c.bl b hb))

theorem isoR_iff {f a b : V} (ha : a ∈ Lev lam) (hb : b ∈ Lev lam) :
    IsoR f a b A B Q ↔ IsoL f a b A B := by
  have qa : ∀ u, u ∈ A → ((Pr Q u a ∨ u = a) ↔ (LtL u a ∨ u = a)) :=
    fun u hu => or_congr (c.q u a (c.al u hu) ha) Iff.rfl
  have qb : ∀ v, v ∈ B → ((Pr Q v b ∨ v = b) ↔ (LtL v b ∨ v = b)) :=
    fun v hv => or_congr (c.q v b (c.bl v hv) hb) Iff.rfl
  unfold IsoR IsoL
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall_congr' fun u => imp_congr_right fun hu => imp_congr (qa u hu)
      (exists_congr fun v => and_congr_right fun hv => and_congr (qb v hv) Iff.rfl)
  · exact forall_congr' fun v => imp_congr_right fun hv => imp_congr (qb v hv)
      (exists_congr fun u => and_congr_right fun hu => and_congr (qa u hu) Iff.rfl)
  · exact forall_congr' fun u => imp_congr_right fun hu => forall_congr' fun u' =>
      imp_congr_right fun hu' => forall_congr' fun v => imp_congr_right fun hv =>
      forall_congr' fun v' => imp_congr_right fun hv' =>
      imp_congr (qa u hu) (imp_congr (qa u' hu') (imp_congr Iff.rfl (imp_congr Iff.rfl
        (iff_congr (c.q u u' (c.al u hu) (c.al u' hu')) (c.q v v' (c.bl v hv) (c.bl v' hv'))))))

/-- **An isomorphism between initial segments agrees with `π`.** -/
theorem rigid {f a b : V} (ha : a ∈ A) (hb : b ∈ B) (h : IsoL f a b A B) :
    (∀ u, u ∈ A → (LtL u a ∨ u = a) → ∀ v, v ∈ B → Pr f u v → Pr π u v) ∧ Pr π a b := by
  obtain ⟨c1, c2, c3⟩ := h
  have hL := c.lim.1
  have ffun : ∀ u, u ∈ A → (LtL u a ∨ u = a) → ∀ v, v ∈ B → ∀ v', v' ∈ B → Pr f u v →
      Pr f u v' → v = v' := by
    intro u hu hle v hv v' hv' h1 h2
    rcases ltL_tri hL (c.bl v hv) (c.bl v' hv') with e | e | e
    · exact absurd ((c3 u hu u hu v hv v' hv' hle hle h1 h2).mpr e)
        (ltL_irrefl' hL (c.al u hu))
    · exact e
    · exact absurd ((c3 u hu u hu v' hv' v hv hle hle h2 h1).mpr e)
        (ltL_irrefl' hL (c.al u hu))
  have part1 : ∀ u, u ∈ A → (LtL u a ∨ u = a) → ∀ v, v ∈ B → Pr f u v → Pr π u v := by
    by_contra hcon
    let Z : V := sepB (k := 5) (((prB.comp ![3, 0, 1]).or (BDef.eq 0 1)).and
      (BDef.bex 2 ((prB.comp ![5, 1, 0]).and (prB.comp ![6, 1, 0]).not))) A ![a, B, Q, f, π]
    have hZ : ∀ u, u ∈ Z ↔ u ∈ A ∧ ((Pr Q u a ∨ u = a) ∧
        ∃ v, v ∈ B ∧ (Pr f u v ∧ ¬Pr π u v)) := fun u => mem_sepB _ _ _ u
    have qa : ∀ u, u ∈ A → ((Pr Q u a ∨ u = a) ↔ (LtL u a ∨ u = a)) :=
      fun u hu => or_congr (c.q u a (c.al u hu) (c.al a ha)) Iff.rfl
    have hne : ∃ u, u ∈ Z := by
      by_contra hno
      exact hcon fun u hu hle v hv hf => by
        by_contra hn
        exact hno ⟨u, (hZ u).mpr ⟨hu, (qa u hu).mpr hle, v, hv, hf, hn⟩⟩
    obtain ⟨u₀, hu₀Z, hmin⟩ := ltL_least hL Z (fun z hz => c.al z ((hZ z).mp hz).1) hne
    obtain ⟨hu₀, hle₀q, v₀, hv₀, hfv₀, hnπ⟩ := (hZ u₀).mp hu₀Z
    have hle₀ : LtL u₀ a ∨ u₀ = a := (qa u₀ hu₀).mp hle₀q
    have hlt_le : ∀ u, u ∈ A → LtL u u₀ → (LtL u a ∨ u = a) := fun u hu hlt => by
      rcases hle₀ with e | e
      · exact Or.inl (ltL_trans hL (c.al u hu) (c.al u₀ hu₀) (c.al a ha) hlt e)
      · exact Or.inl (e ▸ hlt)
    have hmin' : ∀ u, u ∈ A → LtL u u₀ → ∀ v, v ∈ B → Pr f u v → Pr π u v := by
      intro u hu hlt v hv hf
      by_contra hn
      exact hmin u ((hZ u).mpr ⟨hu, (qa u hu).mpr (hlt_le u hu hlt), v, hv, hf, hn⟩) hlt
    obtain ⟨w₀, hw₀, hπw₀⟩ := c.iso.1 u₀ hu₀
    obtain ⟨v₁, hv₁, hv₁b, hfv₁⟩ := c1 u₀ hu₀ hle₀
    have ev : v₁ = v₀ := ffun u₀ hu₀ hle₀ v₁ hv₁ v₀ hv₀ hfv₁ hfv₀
    rw [ev] at hv₁b
    rcases ltL_tri hL (c.bl w₀ hw₀) (c.bl v₀ hv₀) with e | e | e
    · have hw₀b : LtL w₀ b ∨ w₀ = b := by
        rcases hv₁b with e' | e'
        · exact Or.inl (ltL_trans hL (c.bl w₀ hw₀) (c.bl v₀ hv₀) (c.bl b hb) e e')
        · exact Or.inl (e' ▸ e)
      obtain ⟨u₂, hu₂, hu₂a, hfu₂⟩ := c2 w₀ hw₀ hw₀b
      have hlt : LtL u₂ u₀ := (c3 u₂ hu₂ u₀ hu₀ w₀ hw₀ v₀ hv₀ hu₂a hle₀ hfu₂ hfv₀).mpr e
      have hπu₂ := hmin' u₂ hu₂ hlt w₀ hw₀ hfu₂
      have e2 : u₂ = u₀ := c.pi_inj hu₂ hu₀ hw₀ hπu₂ hπw₀
      rw [e2] at hlt
      exact ltL_irrefl' hL (c.al u₀ hu₀) hlt
    · rw [e] at hπw₀
      exact hnπ hπw₀
    · obtain ⟨u₃, hu₃, hπu₃⟩ := c.iso.2.1 v₀ hv₀
      have hlt : LtL u₃ u₀ := (c.iso.2.2 u₃ hu₃ u₀ hu₀ v₀ hv₀ w₀ hw₀ hπu₃ hπw₀).mpr e
      have hu₃a := hlt_le u₃ hu₃ hlt
      obtain ⟨v', hv', -, hfv'⟩ := c1 u₃ hu₃ hu₃a
      have hπv' := hmin' u₃ hu₃ hlt v' hv' hfv'
      have ev' : v' = v₀ := c.pi_fun hu₃ hv' hv₀ hπv' hπu₃
      rw [ev'] at hfv'
      exact ltL_irrefl' hL (c.bl v₀ hv₀)
        ((c3 u₃ hu₃ u₀ hu₀ v₀ hv₀ v₀ hv₀ hu₃a hle₀ hfv' hfv₀).mp hlt)
  refine ⟨part1, ?_⟩
  obtain ⟨v, hv, hvb, hfv⟩ := c1 a ha (Or.inr rfl)
  have hπv := part1 a ha (Or.inr rfl) v hv hfv
  rcases hvb with e | e
  · exfalso
    obtain ⟨u, hu, hua, hfu⟩ := c2 b hb (Or.inr rfl)
    have hlt : LtL a u := (c3 a ha u hu v hv b hb (Or.inr rfl) hua hfv hfu).mpr e
    rcases hua with e' | e'
    · exact ltL_asymm hL (c.al a ha) (c.al u hu) hlt e'
    · rw [e'] at hlt
      exact ltL_irrefl' hL (c.al a ha) hlt
  · rw [e] at hπv
    exact hπv

/-- **Every initial segment of `π` is in one fixed level.** -/
theorem seg_exists {κ₃ : V} (hκ₃ : Ord κ₃)
    (hbound : ∀ δ x : V, Ord δ → x ∈ Lev δ → (∀ z, z ∈ x → z ∈ Lev (scn 4 lam)) → x ∈ Lev κ₃)
    (hA : Con A) (hB : Con B) (hQc : Con Q) :
    ∀ a, a ∈ A → ∀ b, b ∈ B → Pr π a b → PiR a b A B Q (Lev κ₃) := by
  have hL := c.lim.1
  have hbig := lim_big c.lim
  suffices hs : ∀ a, a ∈ A → ∃ b, b ∈ B ∧ PiR a b A B Q (Lev κ₃) by
    intro a ha b hb hπab
    obtain ⟨b', hb', f, hf, hiso⟩ := hs a ha
    have h2 := (c.rigid ha hb' ((c.isoR_iff (c.al a ha) (c.bl b' hb')).mp hiso)).2
    rw [c.pi_fun ha hb hb' hπab h2]
    exact ⟨f, hf, hiso⟩
  by_contra hcon
  let Z : V := sepB (k := 4) ((BDef.bex 1 (piRB.comp ![1, 0, 3, 2, 4, 5])).not) A
    ![B, A, Q, Lev κ₃]
  have hZ : ∀ a, a ∈ Z ↔ a ∈ A ∧ ¬∃ b, b ∈ B ∧ PiR a b A B Q (Lev κ₃) :=
    fun a => mem_sepB _ _ _ a
  have hne : ∃ a, a ∈ Z := by
    by_contra hno
    exact hcon fun a ha => by
      by_contra hn
      exact hno ⟨a, (hZ a).mpr ⟨ha, hn⟩⟩
  obtain ⟨a₀, ha₀Z, hmin⟩ := ltL_least hL Z (fun z hz => c.al z ((hZ z).mp hz).1) hne
  obtain ⟨ha₀, hn₀⟩ := (hZ a₀).mp ha₀Z
  have hbelow : ∀ u, u ∈ A → LtL u a₀ → ∀ v, v ∈ B →
      (PiR u v A B Q (Lev κ₃) ↔ Pr π u v) := by
    intro u hu hlt v hv
    constructor
    · rintro ⟨f, -, hiso⟩
      exact (c.rigid hu hv ((c.isoR_iff (c.al u hu) (c.bl v hv)).mp hiso)).2
    · intro hπuv
      have hex : ∃ b, b ∈ B ∧ PiR u b A B Q (Lev κ₃) := by
        by_contra hn
        exact hmin u ((hZ u).mpr ⟨hu, hn⟩) hlt
      obtain ⟨b', hb', f, hf, hiso⟩ := hex
      have h2 := (c.rigid hu hb' ((c.isoR_iff (c.al u hu) (c.bl b' hb')).mp hiso)).2
      rw [c.pi_fun hu hv hb' hπuv h2]
      exact ⟨f, hf, hiso⟩
  obtain ⟨b₀, hb₀, hπ₀⟩ := c.iso.1 a₀ ha₀
  have hK := con_lev hκ₃
  have ha₀c : Con a₀ := ⟨lam, hL, c.al a₀ ha₀⟩
  obtain ⟨γ, hγ, -, hAγ, hl⟩ := good_common (good_of_con hA) [B, Q, Lev κ₃, a₀] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with e | e | e | e
    · rw [e]; exact good_of_con hB
    · rw [e]; exact good_of_con hQc
    · rw [e]; exact good_of_con hK
    · rw [e]; exact good_of_con ha₀c)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨g, hg, hgz⟩ := sep_good_bdef (closed_true (V := V)) (k := 5)
    (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and ((prB.comp ![5, 1, 7]).and
      (piRB.comp ![1, 0, 3, 4, 5, 6])))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![A, B, Q, Lev κ₃, a₀] (by
      intro i
      match i with
      | 0 => exact ⟨up _ hAγ, good_of_con hA⟩
      | 1 => exact ⟨up _ (hl B (by simp)), good_of_con hB⟩
      | 2 => exact ⟨up _ (hl Q (by simp)), good_of_con hQc⟩
      | 3 => exact ⟨up _ (hl (Lev κ₃) (by simp)), good_of_con hK⟩
      | 4 => exact ⟨up _ (hl a₀ (by simp)), good_of_con ha₀c⟩)
  have hgz' : ∀ p, p ∈ g ↔ p ∈ Lev (scn 4 γ) ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧
      (IsOp p u v ∧ (Pr Q u a₀ ∧ PiR u v A B Q (Lev κ₃))) := hgz
  have hgk : ∀ u v, u ∈ A → v ∈ B → (kp u v ∈ g ↔ LtL u a₀ ∧ Pr π u v) := by
    intro u v hu hv
    rw [hgz']
    constructor
    · rintro ⟨-, u', hu', v', hv', hop, hq, hpi⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [← e1] at hq hpi
      rw [← e2] at hpi
      have hlt := (c.q u a₀ (c.al u hu) (c.al a₀ ha₀)).mp hq
      exact ⟨hlt, (hbelow u hu hlt v hv).mp hpi⟩
    · rintro ⟨hlt, hπuv⟩
      exact ⟨kp_mem_lev hγ (lev_tr hγ.1 _ hAγ u hu) (lev_tr hγ.1 _ (hl B (by simp)) v hv),
        u, hu, v, hv, isOp_kp u v, (c.q u a₀ (c.al u hu) (c.al a₀ ha₀)).mpr hlt,
        (hbelow u hu hlt v hv).mpr hπuv⟩
  have hgc := con_of_good hg
  have hkc : Con (kp a₀ b₀) := con_kp ha₀c ⟨lam, hL, c.bl b₀ hb₀⟩
  obtain ⟨γ', hγ', h1, h2⟩ := con_big2 hgc hkc
  have hf₀L : (insert (kp a₀ b₀) g : V) ∈ Lev (sc γ') := adj_mem_lev hγ'.1 (big_ne hγ') h1 h2
  have hf₀sub : ∀ z, z ∈ (insert (kp a₀ b₀) g : V) → z ∈ Lev (scn 4 lam) := by
    intro z hz
    rcases (by simpa using hz : z = kp a₀ b₀ ∨ z ∈ g) with e | e
    · rw [e]
      exact kp_mem_lev hbig (c.al a₀ ha₀) (c.bl b₀ hb₀)
    · obtain ⟨-, u, hu, v, hv, hop, -⟩ := (hgz' z).mp e
      rw [isOp_iff.mp hop]
      exact kp_mem_lev hbig (c.al u hu) (c.bl v hv)
  have hf₀K : (insert (kp a₀ b₀) g : V) ∈ Lev κ₃ := hbound _ _ (ord_sc hγ'.1) hf₀L hf₀sub
  have hpr : ∀ u v, u ∈ A → v ∈ B → (LtL u a₀ ∨ u = a₀) →
      (Pr (insert (kp a₀ b₀) g : V) u v ↔ Pr π u v) := by
    intro u v hu hv hle
    rw [pr_iff]
    constructor
    · intro h
      rcases (by simpa using h : kp u v = kp a₀ b₀ ∨ kp u v ∈ g) with e | e
      · obtain ⟨e1, e2⟩ := kp_inj e
        rw [e1, e2]
        exact hπ₀
      · exact ((hgk u v hu hv).mp e).2
    · intro h
      rcases hle with e | e
      · have hmem : kp u v ∈ g := (hgk u v hu hv).mpr ⟨e, h⟩
        simp [hmem]
      · have ev : v = b₀ := c.pi_fun ha₀ hv hb₀ (e ▸ h) hπ₀
        rw [e, ev]
        simp
  have hisoL : IsoL (insert (kp a₀ b₀) g : V) a₀ b₀ A B := by
    refine ⟨fun u hu hle => ?_, fun v hv hle => ?_,
      fun u hu u' hu' v hv v' hv' hle hle' h1 h2 => ?_⟩
    · obtain ⟨v, hv, hπuv⟩ := c.iso.1 u hu
      refine ⟨v, hv, ?_, (hpr u v hu hv hle).mpr hπuv⟩
      rcases hle with e | e
      · exact Or.inl ((c.iso.2.2 u hu a₀ ha₀ v hv b₀ hb₀ hπuv hπ₀).mp e)
      · exact Or.inr (c.pi_fun ha₀ hv hb₀ (e ▸ hπuv) hπ₀)
    · obtain ⟨u, hu, hπuv⟩ := c.iso.2.1 v hv
      have hle' : LtL u a₀ ∨ u = a₀ := by
        rcases hle with e | e
        · exact Or.inl ((c.iso.2.2 u hu a₀ ha₀ v hv b₀ hb₀ hπuv hπ₀).mpr e)
        · exact Or.inr (c.pi_inj hu ha₀ hb₀ (e ▸ hπuv) hπ₀)
      exact ⟨u, hu, hle', (hpr u v hu hv hle').mpr hπuv⟩
    · exact c.iso.2.2 u hu u' hu' v hv v' hv' ((hpr u v hu hv hle).mp h1)
        ((hpr u' v' hu' hv' hle').mp h2)
  exact hn₀ ⟨b₀, hb₀, _, hf₀K, (c.isoR_iff (c.al a₀ ha₀) (c.bl b₀ hb₀)).mpr hisoL⟩

end IsoCtx

/-- **An isomorphism between constructible sets of members of a level, for the order of the
constructible sets, is constructible.** -/
theorem oiso_con {A B π lam : V} (hl : Lim lam) (hA : Con A) (hB : Con B)
    (hAl : ∀ a, a ∈ A → a ∈ Lev lam) (hBl : ∀ b, b ∈ B → b ∈ Lev lam) (hπ : OIso π A B) :
    ∃ I : V, Con I ∧ ∀ u v, u ∈ A → v ∈ B → (kp u v ∈ I ↔ Pr π u v) := by
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hl)
  obtain ⟨κ₃, hκ₃, hbound⟩ := bound_exists (big_scn (lim_big hl) 4)
  have c : IsoCtx A B π lam Q := ⟨hl, hAl, hBl, hQ, hπ⟩
  have hseg := c.seg_exists hκ₃ hbound hA hB hQc
  have hK := con_lev hκ₃
  obtain ⟨γ, hγ, -, hAγ, hlst⟩ := good_common (good_of_con hA) [B, Q, Lev κ₃] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with e | e | e
    · rw [e]; exact good_of_con hB
    · rw [e]; exact good_of_con hQc
    · rw [e]; exact good_of_con hK)
  have hγ4 := big_scn hγ 4
  have up := lev_scn_sub hγ.1 4
  obtain ⟨I, hI, hIz⟩ := sep_good_bdef (closed_true (V := V)) (k := 4)
    (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and (piRB.comp ![1, 0, 3, 4, 5, 6]))))
    (good_of_con (con_lev hγ4.1)) (lev_tr hγ4.1) ![A, B, Q, Lev κ₃] (by
      intro i
      match i with
      | 0 => exact ⟨up _ hAγ, good_of_con hA⟩
      | 1 => exact ⟨up _ (hlst B (by simp)), good_of_con hB⟩
      | 2 => exact ⟨up _ (hlst Q (by simp)), good_of_con hQc⟩
      | 3 => exact ⟨up _ (hlst (Lev κ₃) (by simp)), good_of_con hK⟩)
  have hIz' : ∀ p, p ∈ I ↔ p ∈ Lev (scn 4 γ) ∧ ∃ u, u ∈ A ∧ ∃ v, v ∈ B ∧
      (IsOp p u v ∧ PiR u v A B Q (Lev κ₃)) := hIz
  refine ⟨I, con_of_good hI, fun u v hu hv => ?_⟩
  rw [hIz']
  constructor
  · rintro ⟨-, u', hu', v', hv', hop, f, -, hiso⟩
    obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
    rw [← e1, ← e2] at hiso
    exact (c.rigid hu hv ((c.isoR_iff (hAl u hu) (hBl v hv)).mp hiso)).2
  · intro hπuv
    exact ⟨kp_mem_lev hγ (lev_tr hγ.1 _ hAγ u hu) (lev_tr hγ.1 _ (hlst B (by simp)) v hv),
      u, hu, v, hv, isOp_kp u v, hseg u hu v hv hπuv⟩

end iso

end MH

end FFL.FirstOrder.SetTheory
