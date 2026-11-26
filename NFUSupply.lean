module

public import NFUCountMH
public import MHBase
public import MHCountSound

@[expose] public section

set_option autoImplicit false

/-!
# The supply in a model of `𝗡𝗙𝗨𝗜𝗖`, and `Con(𝗡𝗙𝗨𝗜𝗖) → Con(𝗡𝗙𝗖)`

`MHCountSound.lean` derives the consistency of `𝗡𝗙𝗖` from models of `𝗠𝗛` that have a supply
(`MH.Supply`, `MHSupply.lean`) for every radius. Here the supply is built in the model of `𝗠𝗛`
on the types of a model of `𝗡𝗙𝗨𝗜𝗖` (`NFUCountMH.lean`).

* `eop_of_fixed`, `eop_inj`, `eop_unique`: Kuratowski pairs of fixed types, among the types.
* `lex_idxOK`: for a set `H` of fixed ordinals closed under members, the pairs of a member of
  `H` and a finite ordinal, in the lexicographic order, satisfy the conditions `IdxOK` of
  `NFULevels.lean`. So there are levels along `ω · H`: between the levels of two members of `H`
  there are infinitely many levels.
* `dom_sep`: separation in the structure by a set of types. `emb_om_iff`: the members of `ω` of
  the structure are the finite ordinals among the types. `isOrd_of_ord`, `inH_of_vinj`: an
  ordinal of the structure that maps one-to-one into `T` in the structure belongs to Hartogs'
  set of the members of `T`.
* `bT_fixed`: with the Axiom of Counting, the members of the base sets `MH.bT` are fixed types
  (finitely many power sets over the finite ordinals, which are fixed by `om_fixed`).
* `IsLv`, `exists_lv`, `lv_mono`, `lv_pow`, `lv_om`: the levels as elements of the structure.
* **`exists_supply`**: the structure has a supply for every radius.
* **`consistent_nfc_of_consistent_nfuic : Con(𝗡𝗙𝗨𝗜𝗖) → Con(𝗡𝗙𝗖)`**, and
  `consistent_nfc_iff_consistent_nfuic`.

The Axiom of Counting is used in three places: the finite ordinals are fixed types
(`om_fixed`), so the members of the base sets are fixed, so Hartogs' ordinal of the last base
set consists of fixed ordinals and indexes levels that the map `θ` carries onto themselves
(`levG_theta`); these levels are therefore in the domain of the structure.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD Dom)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `p` is the pair of a member of `H` and a finite ordinal. -/
def LexA (H p : V) : Prop := ∃ a n : V, a ∈ H ∧ (InOm n ∧ EOp p a n)

/-- The lexicographic order on the pairs of a member of `H` and a finite ordinal. -/
def LexR (p p' H : V) : Prop :=
  ∃ a n a' n' : V, EOp p a n ∧ (EOp p' a' n' ∧ (a ∈ H ∧ (a' ∈ H ∧ (InOm n ∧ (InOm n' ∧
    (EE a a' ∨ (a = a' ∧ EE n n')))))))

/-- The conditions on `H` under which the pairs form an index set. -/
structure LexOK (g H : V) : Prop where
  fixed : ∀ a : V, a ∈ H → Fixed g a
  ord : ∀ a : V, a ∈ H → IsOrd a
  down : ∀ a u : V, a ∈ H → EE u a → u ∈ H
  nonempty : ∃ a : V, a ∈ H

end defs

section sdefs

def lexAD : SDef ![7, 6] (fun _ _ v ↦ LexA (v 0) (v 1)) :=
  (SDef.ex 6 (SDef.ex 6 ((SDef.mem 1 2).and ((inOmD.comp ![0] 0).and
    (eOpD.comp ![3, 1, 0] 0))))).congr fun _ _ _ => Iff.rfl

def lexRD : SDef ![6, 6, 7] (fun _ _ v ↦ LexR (v 0) (v 1) (v 2)) :=
  (SDef.ex 6 (SDef.ex 6 (SDef.ex 6 (SDef.ex 6 ((eOpD.comp ![4, 3, 2] 0).and
    ((eOpD.comp ![5, 1, 0] 0).and ((SDef.mem 3 6).and ((SDef.mem 1 6).and
      ((inOmD.comp ![2] 0).and ((inOmD.comp ![0] 0).and ((eeD.comp ![3, 1] 0).or
        ((SDef.eq 3 1).and (eeD.comp ![2, 0] 0))))))))))))).congr fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-! ### Pairs of fixed types -/

theorem esing_of_fixed {g a : V} (hg : IsEg g) (ha : Fixed g a) :
    ∃ z, ESing z a ∧ Fixed g z := by
  obtain ⟨S, hS⟩ := exists_sing a
  obtain ⟨z, hzZ, hzf, hz⟩ := exists_type_of_fixed hg (S := S) fun s hs => by
    rw [(hS s).mp hs]
    exact ha
  exact ⟨z, ⟨hzZ, fun c => (hz c).trans (hS c)⟩, hzf⟩

theorem eup_of_fixed {g a b : V} (hg : IsEg g) (ha : Fixed g a) (hb : Fixed g b) :
    ∃ z, EUp z a b ∧ Fixed g z := by
  obtain ⟨S, hS⟩ := exists_up a b
  obtain ⟨z, hzZ, hzf, hz⟩ := exists_type_of_fixed hg (S := S) fun s hs => by
    rcases (hS s).mp hs with e | e
    · rw [e]
      exact ha
    · rw [e]
      exact hb
  exact ⟨z, ⟨hzZ, fun c => (hz c).trans (hS c)⟩, hzf⟩

/-- **Two fixed types have a pair among the types, and it is fixed.** -/
theorem eop_of_fixed {g a b : V} (hg : IsEg g) (ha : Fixed g a) (hb : Fixed g b) :
    ∃ p, EOp p a b ∧ Fixed g p := by
  obtain ⟨z₁, h1, f1⟩ := esing_of_fixed hg ha
  obtain ⟨z₂, h2, f2⟩ := eup_of_fixed hg ha hb
  obtain ⟨p, hp, fp⟩ := eup_of_fixed hg f1 f2
  exact ⟨p, ⟨hp.1, ⟨z₁, (hp.2 z₁).mpr (Or.inl rfl), h1⟩, ⟨z₂, (hp.2 z₂).mpr (Or.inr rfl), h2⟩,
    fun z hz => by
      rcases (hp.2 z).mp hz with e | e
      · rw [e]
        exact Or.inl h1
      · rw [e]
        exact Or.inr h2⟩, fp⟩

omit [Nonempty V] hT in
/-- Pairs among the types determine their components. -/
theorem eop_inj {p a b a' b' : V} (h : EOp p a b) (h' : EOp p a' b') : a = a' ∧ b = b' := by
  obtain ⟨-, ⟨z₁, hz₁p, hz₁⟩, ⟨z₂, hz₂p, hz₂⟩, hall⟩ := h
  obtain ⟨-, ⟨w₁, hw₁p, hw₁⟩, ⟨w₂, hw₂p, hw₂⟩, hall'⟩ := h'
  have ha : a = a' := by
    rcases hall' z₁ hz₁p with k | k
    · exact (k.2 a).mp ((hz₁.2 a).mpr rfl)
    · exact ((hz₁.2 a').mp ((k.2 a').mpr (Or.inl rfl))).symm
  subst ha
  refine ⟨rfl, ?_⟩
  rcases hall' z₂ hz₂p with k | k
  · have hba : b = a := (k.2 b).mp ((hz₂.2 b).mpr (Or.inr rfl))
    rcases hall w₂ hw₂p with k' | k'
    · have hb'a : b' = a := (k'.2 b').mp ((hw₂.2 b').mpr (Or.inr rfl))
      rw [hba, hb'a]
    · rcases (k'.2 b').mp ((hw₂.2 b').mpr (Or.inr rfl)) with e | e
      · rw [hba, e]
      · exact e.symm
  · rcases (k.2 b).mp ((hz₂.2 b).mpr (Or.inr rfl)) with e | e
    · rcases (hz₂.2 b').mp ((k.2 b').mpr (Or.inr rfl)) with e' | e'
      · rw [e, e']
      · exact e'.symm
    · exact e

theorem eop_unique {p p' a b : V} (h : EOp p a b) (h' : EOp p' a b) : p = p' := by
  have key : ∀ {p p' : V}, EOp p a b → EOp p' a b → ∀ v, EE v p → EE v p' := by
    intro p p' h h' v hv
    rcases h.2.2.2 v hv with k | k
    · obtain ⟨z, hz, hzs⟩ := h'.2.1
      rw [esing_unique k hzs]
      exact hz
    · obtain ⟨z, hz, hzs⟩ := h'.2.2.1
      rw [eup_unique k hzs]
      exact hz
  exact ee_ext h.1 h'.1 fun v => ⟨key h h' v, key h' h v⟩

/-! ### The lexicographic index set -/

/-- **The pairs of a member of `H` and a finite ordinal, in the lexicographic order, form an
index set for levels.** -/
theorem lex_idxOK (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {g H A₂ R₂ : V}
    (hg : IsEg g) (lo : LexOK g H) (hA : ∀ p, p ∈ A₂ ↔ LexA H p)
    (hR : ∀ p p', Rl R₂ p p' ↔ LexR p p' H) : IdxOK g A₂ R₂ where
  fixed p hp := by
    obtain ⟨a, n, ha, hn, hpa⟩ := (hA p).mp hp
    obtain ⟨p', hp', f⟩ := eop_of_fixed hg (lo.fixed a ha) (om_fixed hC hg hn)
    rw [eop_unique hpa hp']
    exact f
  wf := by
    rintro X ⟨c₀, hc₀⟩
    obtain ⟨X₁, hX₁⟩ := ((SDef.mem (τ := ![6, 7, 7]) 0 1).and (SDef.ex 6 (SDef.ex 6
      ((SDef.mem 1 4).and ((inOmD.comp ![0] 0).and
        (eOpD.comp ![1, 2, 0] 0)))))).comprehensionU ![H, X]
    have hX₁' : ∀ a, a ∈ X₁ ↔ a ∈ H ∧ ∃ p n, p ∈ X ∧ (InOm n ∧ EOp p a n) := hX₁
    by_cases hne : ∃ a, a ∈ X₁
    · obtain ⟨a₁, ha₁⟩ := hne
      obtain ⟨a₀, ha₀, -, hmin⟩ := ee_wf X₁ ⟨a₁, ha₁, (lo.ord a₁ ((hX₁' a₁).mp ha₁).1).1⟩
      obtain ⟨ha₀H, p₁, n₁, hp₁X, hn₁, hp₁⟩ := (hX₁' a₀).mp ha₀
      obtain ⟨X₂, hX₂⟩ := ((inOmD.comp (τ' := ![6, 7, 6]) ![0] 0).and (SDef.ex 6
        ((SDef.mem 0 2).and (eOpD.comp ![0, 3, 1] 0)))).comprehensionU ![X, a₀]
      have hX₂' : ∀ n, n ∈ X₂ ↔ InOm n ∧ ∃ p, p ∈ X ∧ EOp p a₀ n := hX₂
      obtain ⟨n₀, hn₀, -, hmin₂⟩ := ee_wf X₂
        ⟨n₁, (hX₂' n₁).mpr ⟨hn₁, p₁, hp₁X, hp₁⟩, om_inZ hn₁⟩
      obtain ⟨hn₀o, p₀, hp₀X, hp₀⟩ := (hX₂' n₀).mp hn₀
      refine ⟨p₀, hp₀X, fun b hb hbc => ?_⟩
      obtain ⟨a, n, a', n', hba, hpa', haH, -, hn, -, hor⟩ := (hR b p₀).mp hbc
      obtain ⟨e1, e2⟩ := eop_inj hpa' hp₀
      subst e1
      subst e2
      rcases hor with h | ⟨h1, h2⟩
      · exact hmin a ((hX₁' a).mpr ⟨haH, b, n, hb, hn, hba⟩) h
      · subst h1
        exact hmin₂ n ((hX₂' n).mpr ⟨hn, b, hb, hba⟩) h2
    · refine ⟨c₀, hc₀, fun b hb hbc => hne ?_⟩
      obtain ⟨a, n, a', n', hba, -, haH, -, hn, -, -⟩ := (hR b c₀).mp hbc
      exact ⟨a, (hX₁' a).mpr ⟨haH, b, n, hb, hn, hba⟩⟩
  trans := by
    intro p p' p'' h1 h2
    obtain ⟨a, n, a', n', hp, hp', ha, ha', hn, hn', hor⟩ := (hR p p').mp h1
    obtain ⟨b', m', a'', n'', hq', hp'', -, ha'', -, hn'', hor'⟩ := (hR p' p'').mp h2
    obtain ⟨e1, e2⟩ := eop_inj hq' hp'
    subst e1
    subst e2
    refine (hR p p'').mpr ⟨a, n, a'', n'', hp, hp'', ha, ha'', hn, hn'', ?_⟩
    rcases hor with h | ⟨h, k⟩
    · rcases hor' with h' | ⟨h', -⟩
      · exact Or.inl ((lo.ord a'' ha'').2.1 _ _ h' h)
      · exact Or.inl (h' ▸ h)
    · rcases hor' with h' | ⟨h', k'⟩
      · exact Or.inl (h ▸ h')
      · exact Or.inr ⟨h.trans h', (om_isOrd n'' hn'').2.1 _ _ k' k⟩
  dir := by
    intro p p' hp hp'
    obtain ⟨a, n, ha, hn, hpa⟩ := (hA p).mp hp
    obtain ⟨a', n', ha', hn', hpa'⟩ := (hA p').mp hp'
    have lt : ∀ {p p' a n a' n' : V}, EOp p a n → EOp p' a' n' → a ∈ H → a' ∈ H → InOm n →
        InOm n' → (EE a a' ∨ (a = a' ∧ EE n n')) → Rl R₂ p p' :=
      fun hp hp' ha ha' hn hn' h => (hR _ _).mpr ⟨_, _, _, _, hp, hp', ha, ha', hn, hn', h⟩
    rcases ord_tri hg (lo.ord a ha) (lo.ord a' ha')
        (fun u hu => lo.fixed u (lo.down a u ha hu)) with e | e | e
    · rcases ord_tri hg (om_isOrd n hn) (om_isOrd n' hn')
          (fun u hu => om_fixed hC hg (om_trans hn hu)) with k | k | k
      · subst e
        subst k
        exact ⟨p', hp', Or.inl (eop_unique hpa hpa'), Or.inl rfl⟩
      · exact ⟨p', hp', Or.inr (lt hpa hpa' ha ha' hn hn' (Or.inr ⟨e, k⟩)), Or.inl rfl⟩
      · exact ⟨p, hp, Or.inl rfl, Or.inr (lt hpa' hpa ha' ha hn' hn (Or.inr ⟨e.symm, k⟩))⟩
    · exact ⟨p', hp', Or.inr (lt hpa hpa' ha ha' hn hn' (Or.inl e)), Or.inl rfl⟩
    · exact ⟨p, hp, Or.inl rfl, Or.inr (lt hpa' hpa ha' ha hn' hn (Or.inl e))⟩
  next := by
    intro p hp
    obtain ⟨a, n, ha, hn, hpa⟩ := (hA p).mp hp
    obtain ⟨m, hm, hmo⟩ := om_succ_exists hn
    obtain ⟨p', hp', -⟩ := eop_of_fixed hg (lo.fixed a ha) (om_fixed hC hg hmo)
    exact ⟨p', (hA p').mpr ⟨a, m, ha, hmo, hp'⟩, (hR p p').mpr ⟨a, n, a, m, hpa, hp', ha, ha,
      hn, hmo, Or.inr ⟨rfl, (hm.2.2 n).mpr (Or.inr rfl)⟩⟩⟩
  nonempty := by
    obtain ⟨a, ha⟩ := lo.nonempty
    obtain ⟨z, hz⟩ := exists_zero (V := V)
    obtain ⟨p, hp, -⟩ := eop_of_fixed hg (lo.fixed a ha) (om_fixed hC hg (om_zero hz))
    exact ⟨p, (hA p).mpr ⟨a, z, ha, om_zero hz, hp⟩⟩

end model

/-! ### The structure on the domain: bridges -/

section bridge

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] [Nonempty D] [hH : D↓[ℒₛₑₜ] ⊧* 𝗠𝗛] {i : D → V}

/-- **Separation in the structure by a set of types.** -/
theorem dom_sep (E : Emb i) (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (X : D) (S : V) :
    ∃ w : D, ∀ z : D, z ∈ w ↔ z ∈ X ∧ i z ∈ S := by
  obtain ⟨S', hS'⟩ := ((eeD.comp (τ' := ![6, 6, 7]) ![0, 1] 0).and
    (SDef.mem 0 2)).comprehensionU ![i X, S]
  have hS'' : ∀ v, v ∈ S' ↔ EE v (i X) ∧ v ∈ S := hS'
  obtain ⟨w₀, hwD, -, hw⟩ := dom_sub ((hdom _).mpr ⟨X, rfl⟩) (S := S')
    fun s hs => ((hS'' s).mp hs).1
  obtain ⟨w, rfl⟩ := (hdom w₀).mp hwD
  exact ⟨w, fun z => (E.mem z w).trans ((hw (i z)).trans ((hS'' (i z)).trans
    (and_congr (E.mem z X).symm Iff.rfl)))⟩

omit [Nonempty V] hT in
theorem emb_succ (E : Emb i) (m u : D) (e : u = MH.sc m) : Succ (i m) (i u) := by
  refine ⟨E.inZ m, E.inZ u, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · obtain ⟨w', rfl⟩ := E.down _ _ hw
    have := (E.mem w' u).mpr hw
    rw [e] at this
    rcases MH.mem_sc.mp this with h | h
    · exact Or.inr (congrArg i h)
    · exact Or.inl ((E.mem _ _).mp h)
  · rcases hw with h | h
    · obtain ⟨w', rfl⟩ := E.down _ _ h
      rw [e]
      exact (E.mem _ _).mp (MH.mem_sc.mpr (Or.inr ((E.mem _ _).mpr h)))
    · rw [h, e]
      exact (E.mem _ _).mp (MH.self_mem_sc m)

/-- **The members of `ω` of the structure are the finite ordinals among the types.** -/
theorem emb_om_iff (E : Emb i) (v : V) : EE v (i (MH.om : D)) ↔ InOm v := by
  constructor
  · intro hv
    by_contra hno
    obtain ⟨X, hX⟩ := ((eeD.comp (τ' := ![6, 6]) ![0, 1] 0).and
      (inOmD.comp ![0] 0).not).comprehensionU ![i (MH.om : D)]
    have hX' : ∀ x, x ∈ X ↔ EE x (i (MH.om : D)) ∧ ¬ InOm x := hX
    obtain ⟨x₀, hx₀, -, hmin⟩ := ee_wf X ⟨v, (hX' v).mpr ⟨hv, hno⟩, hv.1⟩
    obtain ⟨hx₀om, hx₀n⟩ := (hX' x₀).mp hx₀
    obtain ⟨u, rfl⟩ := E.down _ _ hx₀om
    have hu : u ∈ (MH.om : D) := (E.mem _ _).mpr hx₀om
    rcases MH.om_cases hu with e | ⟨m, hm, e⟩
    · apply hx₀n
      refine om_zero ⟨E.inZ u, fun w hw => ?_⟩
      obtain ⟨w', rfl⟩ := E.down _ _ hw
      have := (E.mem w' u).mpr hw
      rw [e] at this
      exact absurd this (by simp)
    · have hmu : m ∈ u := by
        rw [e]
        exact MH.self_mem_sc m
      have hmo : InOm (i m) := by
        by_contra h
        exact hmin (i m) ((hX' _).mpr ⟨(E.mem _ _).mp hm, h⟩) ((E.mem _ _).mp hmu)
      exact hx₀n (om_succ hmo (emb_succ E m u e))
  · intro hv
    have hz : IsZero (i (∅ : D)) := ⟨E.inZ _, fun w hw => by
      obtain ⟨w', rfl⟩ := E.down _ _ hw
      exact absurd ((E.mem w' ∅).mpr hw) (by simp)⟩
    exact om_ind 0 (eeD.comp (τ' := ![6, 6]) ![0, 1] 0) ![i (MH.om : D)]
      (fun z hz' => by
        show EE z (i (MH.om : D))
        rw [zero_unique hz' hz]
        exact (E.mem _ _).mp MH.empty_mem_om)
      (fun y _ ih w hw => by
        show EE w (i (MH.om : D))
        have ih' : EE y (i (MH.om : D)) := ih
        obtain ⟨u, rfl⟩ := E.down _ _ ih'
        have hu : u ∈ (MH.om : D) := (E.mem _ _).mpr ih'
        rw [succ_unique hw (emb_succ E u (MH.sc u) rfl)]
        exact (E.mem _ _).mp (MH.sc_mem_om hu)) v hv

omit [Nonempty V] hT in
/-- An ordinal of the structure is an ordinal among the types. -/
theorem isOrd_of_ord (E : Emb i) {ξ : D} (hξ : MH.Ord ξ) : IsOrd (i ξ) := by
  refine ⟨E.inZ ξ, fun u v hu hv => ?_, fun u v hu hv => ?_⟩
  · obtain ⟨u', rfl⟩ := E.down _ _ hu
    obtain ⟨v', rfl⟩ := E.down _ _ hv
    exact (E.mem _ _).mp (hξ.1 u' ((E.mem _ _).mpr hu) v' ((E.mem _ _).mpr hv))
  · obtain ⟨u', rfl⟩ := E.down _ _ hu
    obtain ⟨v', rfl⟩ := E.down _ _ hv
    rcases MH.ord_tri (MH.ord_mem hξ ((E.mem _ _).mpr hu))
        (MH.ord_mem hξ ((E.mem _ _).mpr hv)) with h | h | h
    · exact Or.inr (Or.inl ((E.mem _ _).mp h))
    · exact Or.inl (congrArg i h)
    · exact Or.inr (Or.inr ((E.mem _ _).mp h))

/-- **An ordinal of the structure that maps one-to-one into `T` in the structure belongs to
Hartogs' set of the members of `T`.** -/
theorem inH_of_vinj (E : Emb i) {ξ T : D} {B : V} (hξ : MH.Ord ξ) (h : MH.VInj ξ T)
    (hB : ∀ v, EE v (i T) → v ∈ B) : InH B (i ξ) := by
  obtain ⟨F, hF1, hF2⟩ := h
  obtain ⟨f, hf⟩ := exists_rel 6 (eRlD.comp (τ' := ![6, 6, 6]) ![2, 0, 1] 0) ![i F]
  have hf' : ∀ u b, Rl f u b ↔ ERl (i F) u b := hf
  refine ⟨isOrd_of_ord E hξ, f, fun u hu => ?_, fun u u' b hu hu' h1 h2 => ?_⟩
  · obtain ⟨u', rfl⟩ := E.down _ _ hu
    obtain ⟨v, hv, hr⟩ := hF1 u' ((E.mem _ _).mpr hu)
    exact ⟨i v, hB _ ((E.mem _ _).mp hv), (hf' _ _).mpr ((emb_rl_iff E F u' v).mp hr)⟩
  · obtain ⟨u₁, rfl⟩ := E.down _ _ hu
    obtain ⟨u₂, rfl⟩ := E.down _ _ hu'
    have k1 := (hf' _ _).mp h1
    have k2 := (hf' _ _).mp h2
    obtain ⟨-, b', rfl⟩ := erl_range E k1
    exact congrArg i (hF2 u₁ u₂ b' ((E.mem _ _).mpr hu) ((E.mem _ _).mpr hu')
      ((emb_rl_iff E F u₁ b').mpr k1) ((emb_rl_iff E F u₂ b').mpr k2))

/-! ### The base sets consist of fixed types -/

theorem fixed_of_dmem (E : Emb i) {g : V} (hg : IsEg g) {x : D}
    (h : ∀ z : D, z ∈ x → Fixed g (i z)) : Fixed g (i x) :=
  fixed_of_members hg (E.inZ x) fun u hu => by
    obtain ⟨z, rfl⟩ := E.down x u hu
    exact h z ((E.mem z x).mpr hu)

theorem fixed_rels (E : Emb i) {g : V} (hg : IsEg g) {T x : D}
    (hT : ∀ z : D, z ∈ T → Fixed g (i z))
    (hx : ∀ w, w ∈ x → ∀ p, p ∈ w → p ∈ MH.prodS T T) : Fixed g (i x) := by
  refine fixed_of_dmem E hg fun w hw => fixed_of_dmem E hg fun p hp => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := MH.mem_prodS.mp (hx w hw p hp)
  refine fixed_of_dmem E hg fun s hs => fixed_of_dmem E hg fun t ht => ?_
  rcases (by simpa [MH.kp] using hs : s = {a} ∨ s = {a, b}) with rfl | rfl
  · rw [show t = a by simpa using ht]
    exact hT a ha
  · rcases (by simpa using ht : t = a ∨ t = b) with rfl | rfl
    · exact hT _ ha
    · exact hT _ hb

/-- **With the Axiom of Counting, the members of the base sets are fixed types.** -/
theorem bT_fixed (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i) {g : V}
    (hg : IsEg g) : ∀ (j : ℕ) (x : D), x ∈ (MH.bT j : D) → Fixed g (i x)
  | 0, x, hx => by
    rcases MH.mem_bT_zero.mp hx with h | h
    · exact fixed_rels E hg
        (fun z hz => om_fixed hC hg ((emb_om_iff E _).mp ((E.mem _ _).mp hz))) h
    · exact om_fixed hC hg ((emb_om_iff E _).mp ((E.mem _ _).mp h))
  | j + 1, x, hx => by
    rcases MH.mem_bT_succ.mp hx with h | h
    · exact fixed_rels E hg (bT_fixed hC E hg j) h
    · exact om_fixed hC hg ((emb_om_iff E _).mp ((E.mem _ _).mp h))

/-! ### Levels as elements of the structure -/

/-- `L` is the level of `p`, as an element of the structure. -/
def IsLv (i : D → V) (W p : V) (L : D) : Prop := ∀ v, EE v (i L) ↔ InLev W p v

theorem exists_lv {g A R W p : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (hp : p ∈ A) : ∃ L : D, IsLv i W p L := by
  obtain ⟨S, hS⟩ := exists_slice W p
  obtain ⟨y, hyX, -, hy⟩ := levG_key hg ok hW hp (S := S) fun s hs => (hS s).mp hs
  obtain ⟨L, rfl⟩ := (hdom y).mp (dom_of_levG hg ok hW hyX)
  exact ⟨L, fun v => (hy v).trans (hS v)⟩

theorem lv_mono {g A R W p p' : V} {L L' : D} (ok : IdxOK g A R) (hW : IsWG A R W)
    (E : Emb i) (hL : IsLv i W p L) (hL' : IsLv i W p' L') (hp' : p' ∈ A) (h : Rl R p p') :
    ∀ z : D, z ∈ L → z ∈ L' :=
  fun z hz => (E.mem z L').mpr ((hL' _).mpr
    (levG_mono hW ok.trans hp' h ((hL _).mp ((E.mem z L).mp hz))))

theorem lv_pow {A R W p p' : V} {L L' : D} (hW : IsWG A R W) (E : Emb i)
    (hL : IsLv i W p L) (hL' : IsLv i W p' L') (hp' : p' ∈ A) (h : Rl R p p') :
    ∀ x : D, (∀ z, z ∈ x → z ∈ L) → x ∈ L' :=
  fun x hx => (E.mem x L').mpr ((hL' _).mpr (levG_intro hW hp' (E.inZ x) (Or.inr fun u hu => by
    obtain ⟨z, rfl⟩ := E.down x u hu
    exact ⟨p, h, (hL _).mp ((E.mem z L).mp (hx z ((E.mem z x).mpr hu)))⟩)))

theorem lv_om {A R W p : V} {L : D} (hW : IsWG A R W) (E : Emb i) (hL : IsLv i W p L)
    (hp : p ∈ A) : ∀ n : D, n ∈ (MH.om : D) → n ∈ L :=
  fun n hn => (E.mem n L).mpr ((hL _).mpr (levG_intro hW hp (E.inZ n)
    (Or.inl ((emb_om_iff E _).mp ((E.mem _ _).mp hn)))))

end bridge

/-! ### The supply -/

section supply

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] [Nonempty D] [hH : D↓[ℒₛₑₜ] ⊧* 𝗠𝗛] {i : D → V}

/-- **With the Axiom of Counting, the structure on the domain has a supply of sets for every
radius.** The base sets are `MH.bT`. `ρ` is Hartogs' ordinal of the last base set, in the
structure. Its members are fixed ordinals among the types (`hart_fixed`), so the pairs of a
member of `ρ` or `ρ` itself and a finite ordinal index levels (`lex_idxOK`); the set at
`ξ ∈ ρ` is the level of the pair of `ξ` and a finite ordinal `n₀`, chosen so that the level of
the pair of zero and `n₀` includes the last base set. -/
theorem exists_supply (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) (E : Emb i)
    (hdom : ∀ x : V, Dom x ↔ ∃ w, i w = x) (r : ℕ) :
    ∃ ρ Sq : D, MH.Supply r (MH.bT : ℕ → D) ρ Sq := by
  obtain ⟨g, hg⟩ := exists_eg (V := V)
  -- Hartogs' ordinal of the last base set, in the structure
  obtain ⟨ρ, hρ⟩ := MH.next_exists (MH.bT (r + 2) : D)
  have hρO : MH.Ord ρ := MH.ord_of_ordS hρ.1
  have hρinj : ∀ ζ : D, ζ ∈ ρ → MH.VInj ζ (MH.bT (r + 2) : D) := fun ζ hζ => hρ.2.2 ζ hζ
  have hart : ∀ ξ : D, MH.Ord ξ → MH.VInj ξ (MH.bT (r + 2) : D) → ξ ∈ ρ := by
    intro ξ hξ hv
    rcases MH.ord_tri hξ hρO with h | h | h
    · exact h
    · rw [h] at hv
      exact (hρ.2.1 hv).elim
    · exact (hρ.2.1 (MH.vinj_dom_mono hv fun z hz => hξ.1 ρ h z hz)).elim
  -- the types that are members of the last base set, and the members of `ρ`
  obtain ⟨B, hB⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehensionU
    ![i (MH.bT (r + 2) : D)]
  have hB' : ∀ v, v ∈ B ↔ EE v (i (MH.bT (r + 2) : D)) := hB
  have hBfix : ∀ b, b ∈ B → Fixed g b := fun b hb => by
    obtain ⟨z, rfl⟩ := E.down _ _ ((hB' b).mp hb)
    exact bT_fixed hC E hg (r + 2) z ((E.mem _ _).mpr ((hB' _).mp hb))
  have hρfix : ∀ ζ : D, ζ ∈ ρ → Fixed g (i ζ) := fun ζ hζ =>
    hart_fixed hg hBfix (inH_of_vinj E (MH.ord_mem hρO hζ) (hρinj ζ hζ)
      fun v hv => (hB' v).mpr hv)
  obtain ⟨B₂, hB₂⟩ := ((eeD.comp (τ' := ![6, 6, 6]) ![0, 1] 0).or
    (eeD.comp ![0, 2] 0)).comprehensionU ![i (MH.bT (r + 2) : D), i ρ]
  have hB₂' : ∀ v, v ∈ B₂ ↔ EE v (i (MH.bT (r + 2) : D)) ∨ EE v (i ρ) := hB₂
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
  -- a level over zero that includes the base set `j`
  have lowc : ∀ j : ℕ, ∃ (n p : V) (L : D), InOm n ∧ EOp p (i (∅ : D)) n ∧ p ∈ A₂ ∧
      IsLv i W p L ∧ ∀ z : D, z ∈ (MH.bT j : D) → z ∈ L := by
    intro j
    induction j with
    | zero =>
      obtain ⟨z₀, hz₀⟩ := exists_zero (V := V)
      obtain ⟨p, hp, hpA⟩ := pair _ z₀ h0H (om_zero hz₀)
      obtain ⟨L, hL⟩ := exists_lv hg ok hW hdom hpA
      obtain ⟨n', p', L', hn', hp', hp'A, hL', -, hs⟩ := step4 _ _ p L h0H (om_zero hz₀) hp hL
      refine ⟨n', p', L', hn', hp', hp'A, hL', fun z hz => ?_⟩
      rcases MH.mem_bT_zero.mp hz with h | h
      · exact hs z fun w hw q hq => by
          obtain ⟨a, ha, b, hb, e⟩ := MH.mem_prodS.mp (h w hw q hq)
          exact MH.mem_prodS.mpr ⟨a, lv_om hW E hL hpA a ha, b, lv_om hW E hL hpA b hb, e⟩
      · exact lv_om hW E hL' hp'A z h
    | succ j ih =>
      obtain ⟨n, p, L, hn, hp, hpA, hL, hsub⟩ := ih
      obtain ⟨n', p', L', hn', hp', hp'A, hL', -, hs⟩ := step4 _ n p L h0H hn hp hL
      refine ⟨n', p', L', hn', hp', hp'A, hL', fun z hz => ?_⟩
      rcases MH.mem_bT_succ.mp hz with h | h
      · exact hs z fun w hw q hq => by
          obtain ⟨a, ha, b, hb, e⟩ := MH.mem_prodS.mp (h w hw q hq)
          exact MH.mem_prodS.mpr ⟨a, hsub a ha, b, hsub b hb, e⟩
      · exact lv_om hW E hL' hp'A z h
  obtain ⟨n₀, pb, Lb, hn₀, hpb, hpbA, hLb, hlow⟩ := lowc (r + 2)
  have inA : ∀ {p a : V}, a ∈ H → EOp p a n₀ → p ∈ A₂ :=
    fun ha hp => (hA₂' _).mpr ⟨_, _, ha, hn₀, hp⟩
  -- the top level
  obtain ⟨pt, hpt, hptA⟩ := pair (i ρ) n₀ hρH hn₀
  obtain ⟨Lt, hLt⟩ := exists_lv (i := i) hg ok hW hdom hptA
  -- the sequence
  obtain ⟨SS, hSS⟩ := (SDef.ex (τ := ![6, 6, 9]) 6 (SDef.ex 6 (SDef.ex 6
    ((eOpD.comp ![3, 2, 1] 0).and ((eOpD.comp ![0, 2, 4] 0).and
      (SDef.all 6 ((eeD.comp ![0, 2] 0).iff
        (inLevD.comp ![6, 1, 0] 0)))))))).comprehensionU ![n₀, W]
  have hSS' : ∀ q, q ∈ SS ↔
      ∃ a w p, EOp q a w ∧ (EOp p a n₀ ∧ ∀ v, (EE v w ↔ InLev W p v)) := hSS
  obtain ⟨Sq, hSq⟩ := dom_sep E hdom (MH.prodS ρ (℘ Lt)) SS
  have hop : ∀ ξ S : D, EOp (i (MH.kp ξ S)) (i ξ) (i S) := fun ξ S =>
    (emb_op_iff E _ ξ S).mp (MH.hin_isOp_iff.mpr rfl)
  have sq_intro : ∀ (ξ S : D) (p : V), ξ ∈ ρ → (∀ z, z ∈ S → z ∈ Lt) → EOp p (i ξ) n₀ →
      IsLv i W p S → MH.Pr Sq ξ S := fun ξ S p hξ hsub hp hS =>
    MH.pr_iff.mpr ((hSq _).mpr ⟨MH.mem_prodS.mpr ⟨ξ, hξ, S, mem_power_iff.mpr hsub, rfl⟩,
      (hSS' _).mpr ⟨i ξ, i S, p, hop ξ S, hp, hS⟩⟩)
  have sq_elim : ∀ ξ S : D, MH.Pr Sq ξ S → ξ ∈ ρ ∧ ∃ p, EOp p (i ξ) n₀ ∧ IsLv i W p S := by
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
  have low : ∀ α S : D, α ∈ ρ → MH.Pr Sq α S → ∀ z : D, z ∈ (MH.bT (r + 2) : D) → z ∈ S := by
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
  refine ⟨ρ, Sq, ⟨fun j _ => MH.bT_base j, fun j _ => MH.bT_step j, hρO, hart, ?_, ?_, low, ?_⟩⟩
  · intro α hα
    obtain ⟨p, hp, hpA⟩ := pair (i α) n₀ (hξH α hα) hn₀
    obtain ⟨L, hL⟩ := exists_lv (i := i) hg ok hW hdom hpA
    exact ⟨L, sq_intro α L p hα (lv_mono ok hW E hL hLt hptA
      (lexlt hp hpt (hξH α hα) hρH hn₀ hn₀ (Or.inl ((E.mem _ _).mp hα)))) hp hL⟩
  · intro α S hα hS
    exact ⟨MH.vinj_mono (MH.bT_base (r + 2)).om (low α S hα hS)⟩
  · intro α β S S' hαβ hβ hS hS'
    have hα : α ∈ ρ := hρO.1 β hβ α hαβ
    obtain ⟨-, p, hp, hlv⟩ := sq_elim α S hS
    obtain ⟨-, p', hp', hlv'⟩ := sq_elim β S' hS'
    have hp'A := inA (hξH β hβ) hp'
    have hee : EE (i α) (i β) := (E.mem _ _).mp hαβ
    obtain ⟨n₁, p₁, L₁, hn₁, hp₁, -, hL₁, -, s₁⟩ :=
      step4 (i α) n₀ p S (hξH α hα) hn₀ hp hlv
    obtain ⟨n₂, p₂, L₂, hn₂, hp₂, -, hL₂, -, s₂⟩ :=
      step4 (i α) n₁ p₁ L₁ (hξH α hα) hn₁ hp₁ hL₁
    have hlt : Rl R₂ p₂ p' := lexlt hp₂ hp' (hξH α hα) (hξH β hβ) hn₂ hn₀ (Or.inl hee)
    exact ⟨lv_mono ok hW E hlv hlv' hp'A
        (lexlt hp hp' (hξH α hα) (hξH β hβ) hn₀ hn₀ (Or.inl hee)),
      L₁, s₁, fun C hC => lv_mono ok hW E hL₂ hlv' hp'A hlt C (s₂ C hC)⟩

end supply

end HinU

/-! ### The consistency implication -/

/-- The supply, for a structure on the types given with any structure for the language. -/
theorem supply_of_struc {M : Type} [SetStructure M] [Nonempty M] [hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
    (hC : JensenNFU.Counting (fun a b : M => a ∈ b))
    {W : Type} [SetStructure W] [Nonempty W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛) {i : W → M} (E : HinU.Emb i)
    (hdom : ∀ x : M, Hin.Dom x ↔ ∃ w, i w = x) (r : ℕ) :
    ∃ (V : Type) (_ : SetStructure V) (_ : Nonempty V) (_ : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛) (T : ℕ → V)
      (ρ Sq : V), MH.Supply r T ρ Sq := by
  rcases standardStructure_unique W s
  obtain ⟨ρ, Sq, sup⟩ := HinU.exists_supply (hH := h) hC E hdom r
  exact ⟨W, inferInstance, inferInstance, h, MH.bT, ρ, Sq, sup⟩

/-- **If NFU + Infinity + the Axiom of Counting is consistent, then NF + the Axiom of Counting
is consistent.** A model of `𝗡𝗙𝗨𝗜𝗖` carries a model of `𝗠𝗛` on its types (`NFUCountMH.lean`),
which has a supply of sets for every radius (`HinU.exists_supply`); so the consistency follows
by `MH.consistent_nfc_of_supplies`. -/
theorem consistent_nfc_of_consistent_nfuic (h : Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖) :
    Entailment.Consistent 𝗡𝗙𝗖 := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTC
  exfalso
  apply hU
  obtain ⟨hUI, hC⟩ := nfuic_models hTC
  have := hUI
  have hi : Function.Injective (fun a : macTranslationC.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hdom : ∀ x : M, Hin.Dom x ↔ ∃ w : macTranslationC.Model M, (w : M) = x := fun x =>
    ⟨fun hx => ⟨⟨x, (macDomainU_val_iff x).mpr hx⟩, rfl⟩,
      fun ⟨w, hw⟩ => hw ▸ (macDomainU_val_iff _).mp w.dom⟩
  have hMH : (macTranslationC.Model M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp macModelC_models φ (Or.inl hφ)
  have E := HinU.emb_of_dom _ hi hdom macModelC_mem_iff
  exact MH.consistent_nfc_of_supplies fun q => supply_of_struc hC hMH E hdom _

/-- **NF + the Axiom of Counting and NFU + Infinity + the Axiom of Counting are
equiconsistent.** One direction is `consistent_nfc_of_consistent_nfuic`; the other is the
interpretation `nfcInterpretsNFUIC`. -/
theorem consistent_nfc_iff_consistent_nfuic :
    Entailment.Consistent 𝗡𝗙𝗖 ↔ Entailment.Consistent 𝗡𝗙𝗨𝗜𝗖 :=
  ⟨consistent_of_interprets nfcInterpretsNFUIC, consistent_nfc_of_consistent_nfuic⟩

end FFL.FirstOrder.SetTheory
