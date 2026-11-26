module

public import NFUOrd
public import AlephTheory

@[expose] public section

set_option autoImplicit false

/-!
# The alephs in the level models, in a model of `𝗡𝗙𝗨𝗜` with the Axiom of Counting

`IsB k B`: `B` is the `k`-th iterate of Hartogs' set, starting from the set of the finite
ordinals. With the Axiom of Counting these are sets of fixed ordinals (`isB_good`), so
`NFULevels.lean` gives a model `D` of `𝗭` of types of rank below `B` for `IsB (n + 1) B`.
This file proves that `D` satisfies "`ℵₙ` exists" (`aleph_in_levels`).

* `levG_key`: every set of members of a level is the extension of a type in the domain.
  `idx_mem_lev`: every index is in its own level.
* `Emb i`: `i` embeds a structure `D` onto a set of types closed under members, with
  singletons and unordered pairs. Kuratowski pairs and relations in `D` correspond to the same
  notions written with membership between types (`emb_op_iff`, `emb_rl_iff`).
* `next_in_levels`: if `x` and `y` are the elements of `D` whose members are a set `B` and its
  Hartogs set, then `y` is the least ordinal of `D` that does not map one-to-one into `x`.
* `omega_in_levels`: the element whose members are the finite ordinals is `ω` in `D`.

This is Proposition 17.8 of the draft *Choice and Consistency Strength in NF and NFU* (v15).
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `B` is the `k`-th iterate of Hartogs' set over the finite ordinals. -/
def IsB : ℕ → V → Prop
  | 0, B => ∀ x : V, x ∈ B ↔ InOm x
  | k + 1, B => ∃ B' : V, IsB k B' ∧ ∀ α : V, α ∈ B ↔ InH B' α

/-- `RH` is membership between types, restricted to `H`. -/
def IsRH (H RH : V) : Prop :=
  ∀ p : V, p ∈ RH ↔ ∃ b a : V, IsOp p b a ∧ b ∈ H ∧ a ∈ H ∧ EE b a

/-- The properties of the sets `B`. -/
structure GoodB (g B : V) : Prop where
  fixed : ∀ b : V, b ∈ B → Fixed g b
  om : ∀ k : V, InOm k → k ∈ B
  ord : ∀ α : V, α ∈ B → IsOrd α
  down : ∀ α u : V, α ∈ B → EE u α → u ∈ B

/-- The type `z` has the one member `a`. -/
def ESing (z a : V) : Prop := InZ z ∧ ∀ c : V, EE c z ↔ c = a

/-- The type `z` has the members `a` and `b`. -/
def EUp (z a b : V) : Prop := InZ z ∧ ∀ c : V, EE c z ↔ c = a ∨ c = b

/-- The type `p` is the Kuratowski pair of `a` and `b`, with respect to `E`. -/
def EOp (p a b : V) : Prop :=
  InZ p ∧ (∃ z : V, EE z p ∧ ESing z a) ∧ (∃ z : V, EE z p ∧ EUp z a b) ∧
    ∀ z : V, EE z p → ESing z a ∨ EUp z a b

/-- The type `f` has the pair of `a` and `b` as a member. -/
def ERl (f a b : V) : Prop := ∃ p : V, EE p f ∧ EOp p a b

end defs

section sdefs

def isBD : (k : ℕ) → SDef ![7] (fun _ _ v ↦ IsB k (v 0))
  | 0 => (SDef.all 6 ((SDef.mem 0 1).iff (inOmD.comp ![0] 0))).congr fun _ _ _ => Iff.rfl
  | k + 1 => (SDef.ex 7 (((isBD k).comp ![0] 0).and
      (SDef.all 6 ((SDef.mem 0 2).iff (inHD.comp ![1, 0] 0))))).congr fun _ _ _ => Iff.rfl

def isRHD : SDef ![7, 9] (fun _ _ v ↦ IsRH (v 0) (v 1)) :=
  (SDef.all 8 ((SDef.mem 0 2).iff (SDef.ex 6 (SDef.ex 6 ((isOpD.comp ![2, 1, 0] 6).and
    ((SDef.mem 1 3).and ((SDef.mem 0 3).and (eeD.comp ![1, 0] 0)))))))).congr
    fun _ _ _ => Iff.rfl

def eSingD : SDef ![6, 6] (fun _ _ v ↦ ESing (v 0) (v 1)) :=
  ((inZD.comp ![0] 0).and (SDef.all 6 ((eeD.comp ![0, 1] 0).iff (SDef.eq 0 2)))).congr
    fun _ _ _ => Iff.rfl

def eUpD : SDef ![6, 6, 6] (fun _ _ v ↦ EUp (v 0) (v 1) (v 2)) :=
  ((inZD.comp ![0] 0).and (SDef.all 6 ((eeD.comp ![0, 1] 0).iff
    ((SDef.eq 0 2).or (SDef.eq 0 3))))).congr fun _ _ _ => Iff.rfl

def eOpD : SDef ![6, 6, 6] (fun _ _ v ↦ EOp (v 0) (v 1) (v 2)) :=
  ((inZD.comp ![0] 0).and ((SDef.ex 6 ((eeD.comp ![0, 1] 0).and (eSingD.comp ![0, 2] 0))).and
    ((SDef.ex 6 ((eeD.comp ![0, 1] 0).and (eUpD.comp ![0, 2, 3] 0))).and
      (SDef.all 6 ((eeD.comp ![0, 1] 0).imp
        ((eSingD.comp ![0, 2] 0).or (eUpD.comp ![0, 2, 3] 0))))))).congr fun _ _ _ => Iff.rfl

def eRlD : SDef ![6, 6, 6] (fun _ _ v ↦ ERl (v 0) (v 1) (v 2)) :=
  (SDef.ex 6 ((eeD.comp ![0, 1] 0).and (eOpD.comp ![0, 2, 3] 0))).congr fun _ _ _ => Iff.rfl

end sdefs

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-! ### Levels: two more facts -/

/-- **Every set of members of a level is the extension of a type in the domain.** -/
theorem levG_key {g A R W a S : V} (hg : IsEg g) (ok : IdxOK g A R) (hW : IsWG A R W)
    (ha : a ∈ A) (hS : ∀ s, s ∈ S → InLev W a s) :
    ∃ y, InXG A W y ∧ InZ y ∧ ∀ v, EE v y ↔ v ∈ S := by
  obtain ⟨L, hL⟩ := exists_slice W a
  obtain ⟨y, hyZ, hy⟩ := stable_full hg (levG_stable hg ok hW ha hL) S
    fun s hs => (hL s).mpr (hS s hs)
  obtain ⟨c, hc, hac⟩ := ok.next a ha
  exact ⟨y, ⟨c, hc, levG_intro hW hc hyZ (Or.inr fun u hu => ⟨a, hac, hS u ((hy u).mp hu)⟩)⟩,
    hyZ, hy⟩

/-- **Every index is in its own level**, when the indices are types closed under members and
the relation is membership. -/
theorem idx_mem_lev {g A R W : V} (ok : IdxOK g A R) (hW : IsWG A R W)
    (hZ : ∀ a, a ∈ A → InZ a) (hdown : ∀ a u, a ∈ A → EE u a → u ∈ A ∧ Rl R u a) :
    ∀ a, a ∈ A → InLev W a a := by
  obtain ⟨Bad, hBad⟩ := ((SDef.mem (τ := ![6, 7, 9]) 0 1).and
    (inLevD.comp ![2, 0, 0] 0).not).comprehensionU ![A, W]
  have hBad' : ∀ a, a ∈ Bad ↔ a ∈ A ∧ ¬ InLev W a a := hBad
  by_contra hcon
  have hne : ∃ a, a ∈ Bad := by
    by_contra h
    exact hcon fun a ha => by
      by_contra hq
      exact h ⟨a, (hBad' a).mpr ⟨ha, hq⟩⟩
  obtain ⟨c, hcBad, hmin⟩ := ok.wf Bad hne
  obtain ⟨hc, hnc⟩ := (hBad' c).mp hcBad
  refine hnc (levG_intro hW hc (hZ c hc) (Or.inr fun u hu => ?_))
  obtain ⟨huA, huc⟩ := hdown c u hc hu
  refine ⟨u, huc, ?_⟩
  by_contra hq
  exact hmin u ((hBad' u).mpr ⟨huA, hq⟩) huc

/-! ### The iterates of Hartogs' set -/

theorem exists_B : ∀ k : ℕ, ∃ B : V, IsB k B
  | 0 => inOmD.comprehensionU (![] : Fin 0 → V)
  | k + 1 => by
    obtain ⟨B', hB'⟩ := exists_B k
    obtain ⟨B, hB⟩ := exists_H B'
    exact ⟨B, B', hB', hB⟩

theorem exists_isRH (H : V) : ∃ RH : V, IsRH H RH :=
  (SDef.ex (τ := ![8, 7]) 6 (SDef.ex 6 ((isOpD.comp ![2, 1, 0] 6).and
    ((SDef.mem 1 3).and ((SDef.mem 0 3).and (eeD.comp ![1, 0] 0)))))).comprehensionU ![H]

theorem rl_isRH {H RH : V} (h : IsRH H RH) (b a : V) : Rl RH b a ↔ b ∈ H ∧ a ∈ H ∧ EE b a :=
  rl_of_spec h b a

/-- An ordinal whose members are in `B` is in Hartogs' set of `B`. -/
theorem inH_of_sub {B α : V} (hα : IsOrd α) (hsub : ∀ u, EE u α → u ∈ B) : InH B α := by
  obtain ⟨f, hf⟩ := exists_rel 6 (SDef.eq (τ := ![6, 6]) 0 1) (![] : Fin 0 → V)
  have hf' : ∀ u b, Rl f u b ↔ u = b := hf
  exact ⟨hα, f, fun u hu => ⟨u, hsub u hu, (hf' u u).mpr rfl⟩,
    fun u u' b _ _ h h' => ((hf' u b).mp h).trans ((hf' u' b).mp h').symm⟩

omit [Nonempty V] hT in
/-- Hartogs' set depends only on the members of the set. -/
theorem inH_congr {B B' α : V} (h : ∀ x, x ∈ B ↔ x ∈ B') : InH B α → InH B' α :=
  fun ⟨hα, f, hf1, hf2⟩ => ⟨hα, f, fun u hu => let ⟨b, hb, hfb⟩ := hf1 u hu; ⟨b, (h b).mp hb, hfb⟩,
    hf2⟩

omit [Nonempty V] hT in
theorem isB_ext : ∀ (k : ℕ) {B B' : V}, IsB k B → IsB k B' → ∀ x, x ∈ B ↔ x ∈ B'
  | 0, _, _, h, h' => fun x => (h x).trans (h' x).symm
  | k + 1, _, _, ⟨B₁, h₁, hB⟩, ⟨B₂, h₂, hB'⟩ => fun x =>
    have e : InH B₁ x ↔ InH B₂ x :=
      ⟨inH_congr (isB_ext k h₁ h₂), inH_congr fun y => (isB_ext k h₁ h₂ y).symm⟩
    (hB x).trans (e.trans (hB' x).symm)

/-- **With the Axiom of Counting, the iterates are sets of fixed ordinals**, closed under
members and containing the finite ordinals. -/
theorem isB_good (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {g : V} (hg : IsEg g) :
    ∀ (k : ℕ) {B : V}, IsB k B → GoodB g B
  | 0, _, h => ⟨fun b hb => om_fixed hC hg ((h b).mp hb), fun k hk => (h k).mpr hk,
      fun α hα => om_isOrd α ((h α).mp hα),
      fun α u hα hu => (h u).mpr (om_trans ((h α).mp hα) hu)⟩
  | k + 1, _, ⟨_, hB', hB⟩ =>
    have ih := isB_good hC hg k hB'
    ⟨fun b hb => hart_fixed hg ih.fixed ((hB b).mp hb),
      fun n hn => (hB n).mpr (om_inH ih.om hn),
      fun α hα => ((hB α).mp hα).1,
      fun α u hα hu => (hB u).mpr (hart_down ((hB α).mp hα) hu)⟩

/-- The iterates increase. -/
theorem isB_le (hC : JensenNFU.Counting (fun a b : V => a ∈ b)) {g : V} (hg : IsEg g)
    {k : ℕ} {B : V} (hB : IsB k B) :
    ∀ (j : ℕ) {B' : V}, IsB (k + j) B' → ∀ α, α ∈ B → α ∈ B'
  | 0, _, hB' => fun α hα => (isB_ext k hB hB' α).mp hα
  | j + 1, _, ⟨B'', hB'', hB'⟩ => fun α hα =>
    have good := isB_good hC hg (k + j) hB''
    have hα'' : α ∈ B'' := isB_le hC hg hB j hB'' α hα
    (hB' α).mpr (inH_of_sub (good.ord α hα'') fun u hu => good.down α u hα'' hu)

/-- The type whose members are the members of a good set is an ordinal. -/
theorem ord_of_good {g B η : V} (hg : IsEg g) (good : GoodB g B) (hηZ : InZ η)
    (hη : ∀ v, EE v η ↔ v ∈ B) : IsOrd η :=
  ⟨hηZ, fun u v hu hv => (hη v).mpr (good.down u v ((hη u).mp hu) hv),
    fun u v hu hv => ord_tri hg (good.ord u ((hη u).mp hu)) (good.ord v ((hη v).mp hv))
      fun w hw => good.fixed w (good.down u w ((hη u).mp hu) hw)⟩

/-- A finite ordinal is zero or a successor. -/
theorem om_cases : ∀ a : V, InOm a → IsZero a ∨ ∃ p, InOm p ∧ Succ p a :=
  om_ind 0 ((isZeroD.comp (τ' := ![6]) ![0] 0).or
    (SDef.ex 6 ((inOmD.comp ![0] 0).and (succD.comp ![0, 1] 0))))
    (![] : Fin 0 → V) (fun _ hz => Or.inl hz) (fun y hy _ _ hw => Or.inr ⟨y, hy, hw⟩)

theorem esing_unique {z z' a : V} (h : ESing z a) (h' : ESing z' a) : z = z' :=
  ee_ext h.1 h'.1 fun c => (h.2 c).trans (h'.2 c).symm

theorem eup_unique {z z' a b : V} (h : EUp z a b) (h' : EUp z' a b) : z = z' :=
  ee_ext h.1 h'.1 fun c => (h.2 c).trans (h'.2 c).symm

end model

/-! ### Structures embedded in the types -/

/-- `i` embeds the structure `D` onto a set of types closed under members, with membership
`EE`; and `D` has singletons and unordered pairs. -/
structure Emb {V D : Type} [SetStructure V] [SetStructure D] (i : D → V) : Prop where
  inj : Function.Injective i
  mem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b)
  inZ : ∀ w : D, InZ (i w)
  down : ∀ (w : D) (v : V), EE v (i w) → ∃ w' : D, i w' = v
  sing : ∀ a : D, ∃ z : D, IsSing z a
  up : ∀ a b : D, ∃ z : D, IsUp z a b

section emb

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] {i : D → V}

omit [Nonempty V] hT in
theorem emb_sing_iff (E : Emb i) (z a : D) : IsSing z a ↔ ESing (i z) (i a) := by
  constructor
  · intro h
    refine ⟨E.inZ z, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
    · obtain ⟨c', rfl⟩ := E.down z c hc
      exact congrArg i ((h c').mp ((E.mem c' z).mpr hc))
    · rw [hc]
      exact (E.mem a z).mp ((h a).mpr rfl)
  · intro h c
    exact ⟨fun hc => E.inj ((h.2 (i c)).mp ((E.mem c z).mp hc)),
      fun hc => (E.mem c z).mpr ((h.2 (i c)).mpr (congrArg i hc))⟩

omit [Nonempty V] hT in
theorem emb_up_iff (E : Emb i) (z a b : D) : IsUp z a b ↔ EUp (i z) (i a) (i b) := by
  constructor
  · intro h
    refine ⟨E.inZ z, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
    · obtain ⟨c', rfl⟩ := E.down z c hc
      rcases (h c').mp ((E.mem c' z).mpr hc) with h1 | h1
      · exact Or.inl (congrArg i h1)
      · exact Or.inr (congrArg i h1)
    · rcases hc with hc | hc
      · rw [hc]
        exact (E.mem a z).mp ((h a).mpr (Or.inl rfl))
      · rw [hc]
        exact (E.mem b z).mp ((h b).mpr (Or.inr rfl))
  · intro h c
    refine ⟨fun hc => ?_, fun hc => (E.mem c z).mpr ((h.2 (i c)).mpr ?_)⟩
    · rcases (h.2 (i c)).mp ((E.mem c z).mp hc) with h1 | h1
      · exact Or.inl (E.inj h1)
      · exact Or.inr (E.inj h1)
    · rcases hc with hc | hc
      · exact Or.inl (congrArg i hc)
      · exact Or.inr (congrArg i hc)

/-- **Kuratowski pairs in `D` are Kuratowski pairs among the types.** -/
theorem emb_op_iff (E : Emb i) (p a b : D) : IsOp p a b ↔ EOp (i p) (i a) (i b) := by
  constructor
  · intro h
    obtain ⟨z₁, hz₁⟩ := E.sing a
    obtain ⟨z₂, hz₂⟩ := E.up a b
    refine ⟨E.inZ p, ⟨i z₁, (E.mem z₁ p).mp ((h z₁).mpr (Or.inl hz₁)), (emb_sing_iff E z₁ a).mp hz₁⟩,
      ⟨i z₂, (E.mem z₂ p).mp ((h z₂).mpr (Or.inr hz₂)), (emb_up_iff E z₂ a b).mp hz₂⟩,
      fun z hz => ?_⟩
    obtain ⟨z', rfl⟩ := E.down p z hz
    rcases (h z').mp ((E.mem z' p).mpr hz) with h1 | h1
    · exact Or.inl ((emb_sing_iff E z' a).mp h1)
    · exact Or.inr ((emb_up_iff E z' a b).mp h1)
  · rintro ⟨-, ⟨z₁, hz₁p, hz₁⟩, ⟨z₂, hz₂p, hz₂⟩, hall⟩ z
    constructor
    · intro hz
      rcases hall (i z) ((E.mem z p).mp hz) with h1 | h1
      · exact Or.inl ((emb_sing_iff E z a).mpr h1)
      · exact Or.inr ((emb_up_iff E z a b).mpr h1)
    · rintro (h1 | h1)
      · have e : i z = z₁ := esing_unique ((emb_sing_iff E z a).mp h1) hz₁
        rw [← e] at hz₁p
        exact (E.mem z p).mpr hz₁p
      · have e : i z = z₂ := eup_unique ((emb_up_iff E z a b).mp h1) hz₂
        rw [← e] at hz₂p
        exact (E.mem z p).mpr hz₂p

/-- **Relations in `D` are relations among the types.** -/
theorem emb_rl_iff (E : Emb i) (f a b : D) : Rl f a b ↔ ERl (i f) (i a) (i b) := by
  constructor
  · rintro ⟨p, hp, hop⟩
    exact ⟨i p, (E.mem p f).mp hp, (emb_op_iff E p a b).mp hop⟩
  · rintro ⟨p₀, hp₀, hop⟩
    obtain ⟨p, rfl⟩ := E.down f p₀ hp₀
    exact ⟨p, (E.mem p f).mpr hp₀, (emb_op_iff E p a b).mpr hop⟩

omit [Nonempty V] hT in
/-- The components of a pair that is a member of an element of `D` are elements of `D`. -/
theorem erl_range (E : Emb i) {f : D} {a b : V} (h : ERl (i f) a b) :
    (∃ a' : D, i a' = a) ∧ ∃ b' : D, i b' = b := by
  obtain ⟨p₀, hp₀, -, -, ⟨z₀, hz₀p, hz₀⟩, -⟩ := h
  obtain ⟨p, rfl⟩ := E.down f p₀ hp₀
  obtain ⟨z, rfl⟩ := E.down p z₀ hz₀p
  exact ⟨E.down z a ((hz₀.2 a).mpr (Or.inl rfl)), E.down z b ((hz₀.2 b).mpr (Or.inr rfl))⟩

omit [Nonempty V] hT in
/-- Kuratowski pairs in `D` determine their components. -/
theorem emb_op_inj (E : Emb i) {p a b a' b' : D} (h : IsOp p a b) (h' : IsOp p a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨sa, hsa⟩ := E.sing a
  obtain ⟨u, hu⟩ := E.up a b
  obtain ⟨u', hu'⟩ := E.up a' b'
  have ha : a = a' := by
    rcases (h' sa).mp ((h sa).mpr (Or.inl hsa)) with h1 | h1
    · exact sing_inj hsa h1
    · exact ((hsa a').mp ((h1 a').mpr (Or.inl rfl))).symm
  subst ha
  refine ⟨rfl, ?_⟩
  have hb : b = a ∨ b = b' := by
    rcases (h' u).mp ((h u).mpr (Or.inr hu)) with h1 | h1
    · exact Or.inl ((h1 b).mp ((hu b).mpr (Or.inr rfl)))
    · exact (h1 b).mp ((hu b).mpr (Or.inr rfl))
  have hb' : b' = a ∨ b' = b := by
    rcases (h u').mp ((h' u').mpr (Or.inr hu')) with h1 | h1
    · exact Or.inl ((h1 b').mp ((hu' b').mpr (Or.inr rfl)))
    · exact (h1 b').mp ((hu' b').mpr (Or.inr rfl))
  rcases hb with hb | hb
  · rcases hb' with hb' | hb'
    · rw [hb, hb']
    · exact hb'.symm
  · exact hb

/-- `D` is extensional. -/
theorem emb_ext (E : Emb i) {x y : D} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  refine E.inj (ee_ext (E.inZ x) (E.inZ y) fun v => ⟨fun hv => ?_, fun hv => ?_⟩)
  · obtain ⟨z, rfl⟩ := E.down x v hv
    exact (E.mem z y).mp ((h z).mp ((E.mem z x).mpr hv))
  · obtain ⟨z, rfl⟩ := E.down y v hv
    exact (E.mem z x).mp ((h z).mpr ((E.mem z y).mpr hv))

/-- `D` has Kuratowski pairs. -/
theorem emb_exists_op (E : Emb i) (a b : D) : ∃ p : D, IsOp p a b := by
  obtain ⟨z₁, hz₁⟩ := E.sing a
  obtain ⟨z₂, hz₂⟩ := E.up a b
  obtain ⟨p, hp⟩ := E.up z₁ z₂
  refine ⟨p, fun z => (hp z).trans ⟨?_, ?_⟩⟩
  · rintro (rfl | rfl)
    · exact Or.inl hz₁
    · exact Or.inr hz₂
  · rintro (h | h)
    · exact Or.inl (emb_ext E fun c => (h c).trans (hz₁ c).symm)
    · exact Or.inr (emb_ext E fun c => (h c).trans (hz₂ c).symm)

omit [Nonempty V] hT in
/-- An ordinal among the types is an ordinal of `D`. -/
theorem ordS_of_isOrd (E : Emb i) {e : D} (h : IsOrd (i e)) : OrdS e :=
  ⟨fun u v hu hv => (E.mem v e).mpr (h.2.1 (i u) (i v) ((E.mem u e).mp hu) ((E.mem v u).mp hv)),
    fun u v hu hv => by
      rcases h.2.2 (i u) (i v) ((E.mem u e).mp hu) ((E.mem v e).mp hv) with h1 | h1 | h1
      · exact Or.inl (E.inj h1)
      · exact Or.inr (Or.inl ((E.mem u v).mpr h1))
      · exact Or.inr (Or.inr ((E.mem v u).mpr h1))⟩

end emb

/-! ### A level model with its embedding -/

/-- A structure `D` of types that contains the types in the levels over an index set `A` of
ordinals closed under members, with membership as the relation. -/
structure LevModel {V D : Type} [SetStructure V] [SetStructure D] (g A RH W : V) (i : D → V) :
    Prop where
  eg : IsEg g
  ok : IdxOK g A RH
  rh : IsRH A RH
  w : IsWG A RH W
  emb : Emb i
  dom : ∀ x : V, InXG A W x → ∃ w : D, i w = x
  ord : ∀ a : V, a ∈ A → IsOrd a
  adown : ∀ a u : V, a ∈ A → EE u a → u ∈ A

section levmodel

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]
variable {D : Type} [SetStructure D] {i : D → V} {g A RH W : V}

omit [Nonempty V] hT in
theorem eop_range (E : Emb i) {p : D} {a b : V} (h : EOp (i p) a b) :
    (∃ a' : D, i a' = a) ∧ ∃ b' : D, i b' = b := by
  obtain ⟨-, -, ⟨z₀, hz₀p, hz₀⟩, -⟩ := h
  obtain ⟨z, rfl⟩ := E.down p z₀ hz₀p
  exact ⟨E.down z a ((hz₀.2 a).mpr (Or.inl rfl)), E.down z b ((hz₀.2 b).mpr (Or.inr rfl))⟩

theorem lm_self (M : LevModel g A RH W i) {a : V} (ha : a ∈ A) : InLev W a a :=
  idx_mem_lev M.ok M.w (fun a ha => (M.ord a ha).1)
    (fun a u ha hu => ⟨M.adown a u ha hu, (rl_isRH M.rh u a).mpr ⟨M.adown a u ha hu, ha, hu⟩⟩) a ha

theorem lm_idx (M : LevModel g A RH W i) {a : V} (ha : a ∈ A) : ∃ e : D, i e = a :=
  M.dom a ⟨a, ha, lm_self M ha⟩

/-- **The level model from its data.** -/
theorem levModel_of {B : V} (hg : IsEg g) (good : GoodB g B) (goodA : GoodB g A)
    (hA : ∀ α, α ∈ A ↔ InH B α) (hRH : IsRH A RH) (hW : IsWG A RH W) (hi : Function.Injective i)
    (hdom : ∀ x : V, InXG A W x ↔ ∃ w : D, i w = x)
    (hmem : ∀ a b : D, a ∈ b ↔ EE (i a) (i b)) : LevModel g A RH W i := by
  have ok : IdxOK g A RH := hart_idxOK hg good.fixed good.om hA (rl_isRH hRH)
  have hlev : ∀ w : D, ∃ a, a ∈ A ∧ InLev W a (i w) := fun w => (hdom _).mpr ⟨w, rfl⟩
  refine ⟨hg, ok, hRH, hW, ⟨hi, hmem, fun w => ?_, fun w v hv => ?_, fun a => ?_, fun a b => ?_⟩,
    fun x => (hdom x).mp, goodA.ord, goodA.down⟩
  · obtain ⟨a, -, h⟩ := hlev w
    exact (levG_inv hW h).2.1
  · obtain ⟨a, ha, h⟩ := hlev w
    exact (hdom v).mp ⟨a, ha, levG_trans hW ok.trans h hv⟩
  · obtain ⟨c, hc, hl⟩ := hlev a
    obtain ⟨S, hS⟩ := exists_sing (i a)
    obtain ⟨y, hyX, -, hy⟩ := levG_key hg ok hW hc (S := S) fun s hs => by
      rw [(hS s).mp hs]; exact hl
    obtain ⟨z, rfl⟩ := (hdom y).mp hyX
    exact ⟨z, fun c' => ⟨fun h => hi ((hS _).mp ((hy _).mp ((hmem c' z).mp h))),
      fun h => (hmem c' z).mpr ((hy _).mpr ((hS _).mpr (congrArg i h)))⟩⟩
  · obtain ⟨c₁, hc₁, hl₁⟩ := hlev a
    obtain ⟨c₂, hc₂, hl₂⟩ := hlev b
    obtain ⟨c, hc, h1, h2⟩ := ok.dir c₁ c₂ hc₁ hc₂
    have hla : InLev W c (i a) := by
      rcases h1 with rfl | h1
      · exact hl₁
      · exact levG_mono hW ok.trans hc h1 hl₁
    have hlb : InLev W c (i b) := by
      rcases h2 with rfl | h2
      · exact hl₂
      · exact levG_mono hW ok.trans hc h2 hl₂
    obtain ⟨S, hS⟩ := exists_up (i a) (i b)
    obtain ⟨y, hyX, -, hy⟩ := levG_key hg ok hW hc (S := S) fun s hs => by
      rcases (hS s).mp hs with h | h
      · rw [h]; exact hla
      · rw [h]; exact hlb
    obtain ⟨z, rfl⟩ := (hdom y).mp hyX
    refine ⟨z, fun c' => ⟨fun h => ?_, fun h => (hmem c' z).mpr ((hy _).mpr ((hS _).mpr ?_))⟩⟩
    · rcases (hS _).mp ((hy _).mp ((hmem c' z).mp h)) with h' | h'
      · exact Or.inl (hi h')
      · exact Or.inr (hi h')
    · rcases h with h | h
      · exact Or.inl (congrArg i h)
      · exact Or.inr (congrArg i h)

/-- **The successor cardinal in a level model.** If the members of `x` are the members of a
good set `B` and the members of `y` are the members of Hartogs' set of `B`, then `y` is the
least ordinal of `D` that does not map one-to-one into `x`. -/
theorem next_in_levels (M : LevModel g A RH W i) {B Bp : V} (good : GoodB g B)
    (hBp : ∀ α, α ∈ Bp ↔ InH B α) {x y : D} (hx : ∀ v, EE v (i x) ↔ v ∈ B)
    (hy : ∀ v, EE v (i y) ↔ v ∈ Bp) (hyA : i y ∈ A) : NextS x y := by
  have hBpA : ∀ α, α ∈ Bp → α ∈ A := fun α hα => M.adown (i y) α hyA ((hy α).mpr hα)
  have hBBp : ∀ b, b ∈ B → b ∈ Bp := fun b hb =>
    (hBp b).mpr (inH_of_sub (good.ord b hb) fun u hu => good.down b u hb hu)
  refine ⟨ordS_of_isOrd M.emb (M.ord _ hyA), ?_, fun z hz => ?_⟩
  · -- no element of `D` maps `y` one-to-one into `x`
    rintro ⟨f, hf1, hf2⟩
    obtain ⟨F, hF⟩ := exists_rel 6 (eRlD.comp (τ' := ![6, 6, 6]) ![2, 0, 1] 0) ![i f]
    have hF' : ∀ a b, Rl F a b ↔ ERl (i f) a b := hF
    refine hart_no_inj M.eg good.fixed hBp ⟨F, fun u hu => ?_, fun u u' b hu hu' h h' => ?_⟩
    · obtain ⟨u', rfl⟩ := lm_idx M (hBpA u hu)
      obtain ⟨v, hvx, hfuv⟩ := hf1 u' ((M.emb.mem u' y).mpr ((hy _).mpr hu))
      exact ⟨i v, (hx _).mp ((M.emb.mem v x).mp hvx),
        (hF' _ _).mpr ((emb_rl_iff M.emb f u' v).mp hfuv)⟩
    · obtain ⟨u₁, rfl⟩ := lm_idx M (hBpA u hu)
      obtain ⟨u₂, rfl⟩ := lm_idx M (hBpA u' hu')
      obtain ⟨-, b', rfl⟩ := erl_range M.emb ((hF' _ _).mp h)
      have h1 := (emb_rl_iff M.emb f u₁ b').mpr ((hF' _ _).mp h)
      have h2 := (emb_rl_iff M.emb f u₂ b').mpr ((hF' _ _).mp h')
      exact congrArg i (hf2 u₁ u₂ b' ((M.emb.mem u₁ y).mpr ((hy _).mpr hu))
        ((M.emb.mem u₂ y).mpr ((hy _).mpr hu')) h1 h2)
  · -- every member of `y` maps one-to-one into `x` by an element of `D`
    have hzy : EE (i z) (i y) := (M.emb.mem z y).mp hz
    obtain ⟨-, f₀, hf1, hf2⟩ := (hBp _).mp ((hy _).mp hzy)
    obtain ⟨P, hP⟩ := (SDef.ex (τ := ![6, 6, 7, 9]) 6 (SDef.ex 6 ((eeD.comp ![1, 3] 0).and
      ((SDef.mem 0 4).and ((rlD.comp ![5, 1, 0] 6).and
        (eOpD.comp ![2, 1, 0] 0)))))).comprehensionU ![i z, B, f₀]
    have hP' : ∀ p, p ∈ P ↔ ∃ u b, EE u (i z) ∧ b ∈ B ∧ Rl f₀ u b ∧ EOp p u b := hP
    obtain ⟨e', he', hee'⟩ := M.ok.next (i y) hyA
    have hPl : ∀ p, p ∈ P → InLev W e' p := by
      intro p hp
      obtain ⟨u, b, hu, hb, -, hpZ, -, -, hall⟩ := (hP' p).mp hp
      have huBp : u ∈ Bp := (hy u).mp ((M.ord _ hyA).2.1 (i z) u hzy hu)
      have hbBp : b ∈ Bp := hBBp b hb
      have hue : Rl RH u (i y) := (rl_isRH M.rh _ _).mpr ⟨hBpA u huBp, hyA, (hy u).mpr huBp⟩
      have hbe : Rl RH b (i y) := (rl_isRH M.rh _ _).mpr ⟨hBpA b hbBp, hyA, (hy b).mpr hbBp⟩
      have hul := lm_self M (hBpA u huBp)
      have hbl := lm_self M (hBpA b hbBp)
      refine levG_intro M.w he' hpZ (Or.inr fun q hq => ⟨i y, hee', ?_⟩)
      rcases hall q hq with ⟨hqZ, hq'⟩ | ⟨hqZ, hq'⟩
      · refine levG_intro M.w hyA hqZ (Or.inr fun c hc => ?_)
        rw [(hq' c).mp hc]
        exact ⟨u, hue, hul⟩
      · refine levG_intro M.w hyA hqZ (Or.inr fun c hc => ?_)
        rcases (hq' c).mp hc with h | h
        · rw [h]; exact ⟨u, hue, hul⟩
        · rw [h]; exact ⟨b, hbe, hbl⟩
    obtain ⟨yh, hyhX, -, hyh⟩ := levG_key M.eg M.ok M.w he' hPl
    obtain ⟨fh, rfl⟩ := M.dom yh hyhX
    refine ⟨fh, fun u hu => ?_, fun u u' v hu hu' h h' => ?_⟩
    · obtain ⟨b, hbB, hfu⟩ := hf1 (i u) ((M.emb.mem u z).mp hu)
      obtain ⟨b', rfl⟩ := lm_idx M (hBpA b (hBBp b hbB))
      obtain ⟨p, hp⟩ := emb_exists_op M.emb u b'
      exact ⟨b', (M.emb.mem b' x).mpr ((hx _).mpr hbB), p,
        (M.emb.mem p fh).mpr ((hyh _).mpr ((hP' _).mpr ⟨i u, i b', (M.emb.mem u z).mp hu, hbB, hfu,
          (emb_op_iff M.emb p u b').mp hp⟩)), hp⟩
    · have key : ∀ w : D, Rl fh w v → Rl f₀ (i w) (i v) := by
        rintro w ⟨p, hp, hop⟩
        obtain ⟨u₀, b₀, -, -, hf₀, hop₀⟩ := (hP' _).mp ((hyh _).mp ((M.emb.mem p fh).mp hp))
        obtain ⟨⟨u₀', hu₀'⟩, b₀', hb₀'⟩ := eop_range M.emb hop₀
        rw [← hu₀', ← hb₀'] at hop₀ hf₀
        obtain ⟨e1, e2⟩ := emb_op_inj M.emb ((emb_op_iff M.emb p u₀' b₀').mpr hop₀) hop
        rw [e1, e2] at hf₀
        exact hf₀
      exact M.emb.inj (hf2 (i u) (i u') (i v) ((M.emb.mem u z).mp hu) ((M.emb.mem u' z).mp hu')
        (key u h) (key u' h'))

/-- **The element whose members are the finite ordinals is `ω`.** -/
theorem omega_in_levels (M : LevModel g A RH W i) {B₀ : V} (hB₀ : ∀ x, x ∈ B₀ ↔ InOm x) {e : D}
    (he : ∀ v, EE v (i e) ↔ v ∈ B₀) (heo : IsOrd (i e)) : OmegaS e := by
  have hin : ∀ v, InOm v → EE v (i e) := fun v hv => (he v).mpr ((hB₀ v).mpr hv)
  have hom : ∀ u : D, u ∈ e → InOm (i u) := fun u hu =>
    (hB₀ _).mp ((he _).mp ((M.emb.mem u e).mp hu))
  refine ⟨ordS_of_isOrd M.emb heo, ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨o, ho⟩ := exists_zero (V := V)
    obtain ⟨o', ho'⟩ := M.emb.down e o (hin o (om_zero ho))
    refine ⟨o', (M.emb.mem o' e).mpr (by rw [ho']; exact hin o (om_zero ho)), fun z hz => ?_⟩
    have := (M.emb.mem z o').mp hz
    rw [ho'] at this
    exact ho.2 (i z) this
  · obtain ⟨w, hsw, hwo⟩ := om_succ_exists (hom u hu)
    obtain ⟨s, hs⟩ := M.emb.down e w (hin w hwo)
    refine ⟨s, (M.emb.mem s e).mpr (by rw [hs]; exact hin w hwo), fun z => ?_⟩
    have h1 : z ∈ s ↔ EE (i z) w := by rw [← hs]; exact M.emb.mem z s
    exact h1.trans ((hsw.2.2 (i z)).trans (or_congr (M.emb.mem z u).symm
      ⟨fun h => M.emb.inj h, fun h => congrArg i h⟩))
  · rcases om_cases (i u) (hom u hu) with hz | ⟨p₀, hp₀, hsp⟩
    · exact Or.inl fun z hz' => hz.2 (i z) ((M.emb.mem z u).mp hz')
    · obtain ⟨p, hp⟩ := M.emb.down e p₀ (hin p₀ hp₀)
      refine Or.inr ⟨p, (M.emb.mem p e).mpr (by rw [hp]; exact hin p₀ hp₀), fun z => ?_⟩
      have h1 : z ∈ p ↔ EE (i z) p₀ := by rw [← hp]; exact M.emb.mem z p
      have h2 : z = p ↔ i z = p₀ := by
        rw [← hp]; exact ⟨fun h => congrArg i h, fun h => M.emb.inj h⟩
      exact (M.emb.mem z u).trans ((hsp.2.2 (i z)).trans (or_congr h1.symm h2.symm))

/-- **"`ℵₙ` exists" in the level model over the `(n + 1)`-st iterate of Hartogs' set.** -/
theorem aleph_in_levels (hC : JensenNFU.Counting (fun a b : V => a ∈ b))
    (M : LevModel g A RH W i) {n : ℕ} (hA : IsB (n + 1) A) : ∃ y : D, IsAleph n y := by
  obtain ⟨Bn, hBn, hAH⟩ := hA
  have elem : ∀ k j : ℕ, k + j = n → ∀ B : V, IsB k B →
      ∃ e : D, (∀ v, EE v (i e) ↔ v ∈ B) ∧ i e ∈ A := by
    intro k j hkj B hB
    have good := isB_good hC M.eg k hB
    obtain ⟨η, hηZ, -, hη⟩ := exists_type_of_fixed M.eg good.fixed
    have hηo : IsOrd η := ord_of_good M.eg good hηZ hη
    have hBn' : IsB (k + j) Bn := by rw [hkj]; exact hBn
    have hηA : η ∈ A := (hAH η).mpr (inH_of_sub hηo fun u hu =>
      isB_le hC M.eg hB j hBn' u ((hη u).mp hu))
    obtain ⟨e, rfl⟩ := lm_idx M hηA
    exact ⟨e, hη, hηA⟩
  have claim : ∀ k j : ℕ, k + j = n → ∀ B : V, IsB k B →
      ∃ e : D, (∀ v, EE v (i e) ↔ v ∈ B) ∧ i e ∈ A ∧ IsAleph k e := by
    intro k
    induction k with
    | zero =>
      intro j hj B hB
      obtain ⟨e, he, heA⟩ := elem 0 j hj B hB
      exact ⟨e, he, heA, omega_in_levels M hB he (M.ord _ heA)⟩
    | succ k ih =>
      intro j hj B hB
      obtain ⟨e, he, heA⟩ := elem (k + 1) j hj B hB
      obtain ⟨B', hB', hBH⟩ := hB
      obtain ⟨e', he', -, hal⟩ := ih (j + 1) (by omega) B' hB'
      exact ⟨e, he, heA, e', hal,
        next_in_levels M (isB_good hC M.eg k hB') hBH he' he heA⟩
  obtain ⟨e, -, -, h⟩ := claim n 0 (by omega) Bn hBn
  exact ⟨e, h⟩

end levmodel

end HinU

end FFL.FirstOrder.SetTheory
