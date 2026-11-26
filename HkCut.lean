module

public import HkTree

@[expose] public section

/-!
# The assignment for a sentence and a family of instances cut off at a number

Inside a model `V` of `𝗠𝗛`. Fix a sentence `σ₀` and a formula `χ` of three variables. The
instance of `χ` at a number `j` is `χ (dn (j + 1), dn j, dn 0)`.

* `SatF J p q`: below the bound `q`, the assignment `p` makes `σ₀` true and the instances of
  `χ` at the members of `J` below `q`. `SatR`: the same by a bounded formula (`satB`, `sat_iff`).
* `Kset`: the numbers `n` such that for every bound some assignment makes `σ₀` and the
  instances at the numbers below `n` true. It is a set, since the condition is bounded.
  `Jset`: the numbers `j` with `j + 1` in `Kset`.
* `sat_ne`: if `0` is in `Kset`, then for every bound some assignment makes `σ₀` and the
  instances at the members of `Jset` true. (If `Kset` is not everything, it has a largest
  member.)
* **`can_holds`**: so the leftmost assignment `S` of `HkTree.lean` makes `σ₀` true and all the
  instances of `χ` at the members of `Jset`, without a bound.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Bounded definitions -/

section rdefs

variable {V : Type} [SetStructure V]

/-- `ε` is the number of the environment `(dn (j + 1), dn j, dn 0)`. -/
def EnvJ (P o j ε : V) : Prop :=
  ∃ z, z ∈ o ∧ ((∀ w, w ∈ z → False) ∧ ∃ j', j' ∈ o ∧ (SuccR j' j ∧
    ∃ d0, d0 ∈ o ∧ (PG P z z d0 ∧ ∃ dj, dj ∈ o ∧ (PG P z j dj ∧ ∃ dj', dj' ∈ o ∧
      (PG P z j' dj' ∧ ∃ ε1, ε1 ∈ o ∧ (PG P d0 z ε1 ∧ ∃ ε2, ε2 ∈ o ∧
        (PG P dj ε1 ε2 ∧ PG P dj' ε2 ε)))))))

end rdefs

def envJB : BDef (k := 4) (fun V _ v ↦ EnvJ (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 1 ((BDef.ball 0 BDef.fls).and (BDef.bex 2 ((succB.comp ![0, 4]).and
    (BDef.bex 3 ((pgB.comp ![3, 2, 2, 0]).and (BDef.bex 4 ((pgB.comp ![4, 3, 6, 0]).and
      (BDef.bex 5 ((pgB.comp ![5, 4, 3, 0]).and (BDef.bex 6 ((pgB.comp ![6, 3, 5, 0]).and
        (BDef.bex 7 ((pgB.comp ![7, 3, 1, 0]).and
          (pgB.comp ![7, 2, 0, 10]))))))))))))))).congr fun _ _ _ => Iff.rfl

section sat

variable (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)

/-- **Below the bound `q`, the assignment `p` makes `σ₀` true and the instances of `χ` at the
members of `J` below `q`**, by a bounded formula. The arguments are `q`, `p`, `P`, `o`, `J`. -/
def SatR : Rel5 := fun V _ q p P o J ↦
  (∀ ε, ε ∈ o → ((∀ z, z ∈ ε → False) → HQ P o p q σ₀ 0 ε)) ∧
  ∀ j, j ∈ J → (j ∈ q → ∀ ε, ε ∈ o → (EnvJ P o j ε → HQ P o p q χ (cnt σ₀) ε))

def satB : BDef (k := 5) (fun V _ v ↦ SatR σ₀ χ V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((BDef.ball 3 ((BDef.ball 0 BDef.fls).imp ((hqB σ₀ 0).comp ![3, 4, 2, 1, 0]))).and
    (BDef.ball 4 ((BDef.mem 0 1).imp (BDef.ball 4 ((envJB.comp ![4, 5, 1, 0]).imp
      ((hqB χ (cnt σ₀)).comp ![4, 5, 3, 2, 0])))))).congr fun _ _ _ => Iff.rfl

/-- The condition that defines `Kset`. The arguments are `n`, `o`, `PO`, `P`. -/
def KDef {V : Type} [SetStructure V] (n o PO P : V) : Prop :=
  ∀ q, q ∈ o → ∃ p, p ∈ PO ∧ SatR σ₀ χ V q p P o n

def kdefB : BDef (k := 4) (fun V _ v ↦ KDef σ₀ χ (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.ball 1 (BDef.bex 3 ((satB σ₀ χ).comp ![1, 0, 5, 3, 2]))).congr fun _ _ _ => Iff.rfl

/-- The condition that defines `Jset`. -/
def JDef {V : Type} [SetStructure V] (j K : V) : Prop := ∃ j', j' ∈ K ∧ SuccR j' j

def jdefB : BDef (k := 2) (fun V _ v ↦ JDef (v 0) (v 1)) :=
  (BDef.bex 1 (succB.comp ![0, 1])).congr fun _ _ _ => Iff.rfl

end sat

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]
variable (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)

/-- The environment of the instance at `j`. -/
noncomputable def envJ (j : V) : Fin 3 → V := ![dn (sc j), dn j, dn ∅]

theorem envJ_mem_om {j : V} (hj : j ∈ (om : V)) : ∀ i, envJ j i ∈ (om : V) := by
  intro i
  fin_cases i
  · exact dn_mem_om (sc_mem_om hj)
  · exact dn_mem_om hj
  · exact dn_mem_om empty_mem_om

/-- **Below the bound `q`, the assignment `p` makes `σ₀` true and the instances of `χ` at the
members of `J` below `q`.** -/
def SatF (J p q : V) : Prop :=
  HoldsQ p q σ₀ 0 ![] ∧ ∀ j, j ∈ J → j ∈ q → HoldsQ p q χ (cnt σ₀) (envJ j)

section bridge

variable {P : V} (hP : CanP P)

include hP

theorem envJ_iff {j ε : V} (hj : j ∈ (om : V)) : EnvJ P (om : V) j ε ↔ ε = tup (envJ j) := by
  have h0 : (∅ : V) ∈ (om : V) := empty_mem_om
  have hsj := sc_mem_om hj
  constructor
  · rintro ⟨z, -, hz, j', -, hj', d0, -, hd0, dj, -, hdj, dj', -, hdj', ε1, -, hε1, ε2, -, hε2, hε⟩
    have ez : z = ∅ := mem_ext fun w => ⟨fun h => (hz w h).elim, fun h => absurd h (by simp)⟩
    subst ez
    obtain rfl := succR_iff_sc.mp hj'
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hd0
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hdj
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hdj'
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hε1
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hε2
    exact ((canP_pg hP).mp hε).2.2
  · rintro rfl
    have hd0 : pr (∅ : V) ∅ ∈ (om : V) := pr_mem_om h0 h0
    have hdj : pr (∅ : V) j ∈ (om : V) := pr_mem_om h0 hj
    have hdj' : pr (∅ : V) (sc j) ∈ (om : V) := pr_mem_om h0 hsj
    have hε1 : pr (pr (∅ : V) ∅) ∅ ∈ (om : V) := pr_mem_om hd0 h0
    have hε2 : pr (pr (∅ : V) j) (pr (pr (∅ : V) ∅) ∅) ∈ (om : V) := pr_mem_om hdj hε1
    exact ⟨∅, h0, fun w hw => absurd hw (by simp), sc j, hsj, succR_iff_sc.mpr rfl,
      _, hd0, (canP_pg hP).mpr ⟨h0, h0, rfl⟩, _, hdj, (canP_pg hP).mpr ⟨h0, hj, rfl⟩,
      _, hdj', (canP_pg hP).mpr ⟨h0, hsj, rfl⟩, _, hε1, (canP_pg hP).mpr ⟨hd0, h0, rfl⟩,
      _, hε2, (canP_pg hP).mpr ⟨hdj, hε1, rfl⟩, (canP_pg hP).mpr ⟨hdj', hε2, rfl⟩⟩

/-- **The bounded formula is `SatF`.** -/
theorem sat_iff {q p J : V} (hq : ∀ α, α ∈ q → α ∈ (om : V)) (hJ : ∀ j, j ∈ J → j ∈ (om : V)) :
    SatR σ₀ χ V q p P (om : V) J ↔ SatF σ₀ χ J p q := by
  have e0 : tup (![] : Fin 0 → V) = ∅ := rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun j hj hjq => ?_⟩
    · have := h1 ∅ empty_mem_om (fun z hz => absurd hz (by simp))
      rw [← e0] at this
      exact (hq_iff hP hq σ₀ 0 ![] (fun i => i.elim0)).mp this
    · have := h2 j hj hjq _ (tup_mem_om _ (envJ_mem_om (hJ j hj)))
        ((envJ_iff hP (hJ j hj)).mpr rfl)
      exact (hq_iff hP hq χ _ _ (envJ_mem_om (hJ j hj))).mp this
  · rintro ⟨h1, h2⟩
    refine ⟨fun ε _ hε => ?_, fun j hj hjq ε _ hεj => ?_⟩
    · have eε : ε = tup (![] : Fin 0 → V) :=
        mem_ext fun w => ⟨fun h => (hε w h).elim, fun h => absurd h (by simp [e0])⟩
      rw [eε]
      exact (hq_iff hP hq σ₀ 0 ![] (fun i => i.elim0)).mpr h1
    · obtain rfl := (envJ_iff hP (hJ j hj)).mp hεj
      exact (hq_iff hP hq χ _ _ (envJ_mem_om (hJ j hj))).mpr (h2 j hj hjq)

end bridge

theorem satF_mono {J p p' q q' : V} (hq : ∀ α, α ∈ q → α ∈ q')
    (hp : ∀ α, α ∈ q → (α ∈ p ↔ α ∈ p')) (h : SatF σ₀ χ J p' q') : SatF σ₀ χ J p q :=
  ⟨holdsQ_mono hq hp σ₀ 0 _ h.1, fun j hj hjq => holdsQ_mono hq hp χ _ _ (h.2 j hj (hq j hjq))⟩

theorem satF_sub {J J' p q : V} (hJ : ∀ j, j ∈ J → j ∈ q → j ∈ J') (h : SatF σ₀ χ J' p q) :
    SatF σ₀ χ J p q :=
  ⟨h.1, fun j hj hjq => h.2 j (hJ j hj hjq) hjq⟩

/-- **The numbers `n` such that for every bound some assignment makes `σ₀` and the instances of
`χ` at the numbers below `n` true.** -/
noncomputable def Kset (P : V) : V := sepB (kdefB σ₀ χ) (om : V) ![(om : V), ℘ om, P]

/-- The numbers `j` with `j + 1` in `Kset`. -/
noncomputable def Jset (P : V) : V := sepB jdefB (om : V) ![Kset σ₀ χ P]

variable {P : V} (hP : CanP P)

include hP

theorem mem_kset {n : V} : n ∈ Kset σ₀ χ P ↔ n ∈ (om : V) ∧
    ∀ q, q ∈ (om : V) → ∃ p, p ∈ (℘ om : V) ∧ SatF σ₀ χ n p q := by
  have h : n ∈ Kset σ₀ χ P ↔ n ∈ (om : V) ∧ KDef σ₀ χ n (om : V) (℘ om) P :=
    mem_sepB (kdefB σ₀ χ) _ _ n
  rw [h]
  refine and_congr_right fun hn => forall_congr' fun q => imp_congr_right fun hq =>
    exists_congr fun p => and_congr_right fun _ => ?_
  exact sat_iff σ₀ χ hP (fun α hα => (ord_om (V := V)).1 q hq α hα)
    (fun j hj => (ord_om (V := V)).1 n hn j hj)

omit hP in
theorem mem_jset {j : V} : j ∈ Jset σ₀ χ P ↔ j ∈ (om : V) ∧ sc j ∈ Kset σ₀ χ P := by
  have h : j ∈ Jset σ₀ χ P ↔ j ∈ (om : V) ∧ JDef j (Kset σ₀ χ P) := mem_sepB jdefB _ _ j
  rw [h]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, succR_iff_sc.mpr rfl⟩⟩
  rintro ⟨j', hj', hs⟩
  exact succR_iff_sc.mp hs ▸ hj'

theorem kset_down {n m : V} (hn : n ∈ Kset σ₀ χ P) (hm : m ∈ n) : m ∈ Kset σ₀ χ P := by
  obtain ⟨hno, h⟩ := (mem_kset σ₀ χ hP).mp hn
  refine (mem_kset σ₀ χ hP).mpr ⟨(ord_om (V := V)).1 n hno m hm, fun q hq => ?_⟩
  obtain ⟨p, hp, hs⟩ := h q hq
  exact ⟨p, hp, satF_sub σ₀ χ (fun j hj _ => (ord_mem ord_om hno).1 m hm j hj) hs⟩

/-- **For every bound some assignment makes `σ₀` and the instances at the members of `Jset`
true**, if `0` is in `Kset`. -/
theorem sat_ne (h0 : (∅ : V) ∈ Kset σ₀ χ P) (q : V) (hq : q ∈ (om : V)) :
    ∃ p, p ∈ (℘ om : V) ∧ SatF σ₀ χ (Jset σ₀ χ P) p q := by
  by_cases hqK : q ∈ Kset σ₀ χ P
  · obtain ⟨p, hp, hs⟩ := ((mem_kset σ₀ χ hP).mp hqK).2 q hq
    exact ⟨p, hp, satF_sub σ₀ χ (fun j _ hjq => hjq) hs⟩
  · let Z : V := sepB (k := 1) (BDef.mem 0 1).not (om : V) ![Kset σ₀ χ P]
    have hZ : ∀ z, z ∈ Z ↔ z ∈ (om : V) ∧ ¬z ∈ Kset σ₀ χ P := fun z => mem_sepB _ _ _ z
    obtain ⟨n₀, hn₀Z, hmin⟩ := ord_least Z (fun z hz => ord_mem ord_om ((hZ z).mp hz).1)
      ⟨q, (hZ q).mpr ⟨hq, hqK⟩⟩
    obtain ⟨hn₀, hn₀K⟩ := (hZ n₀).mp hn₀Z
    rcases om_cases hn₀ with rfl | ⟨n₁, hn₁, rfl⟩
    · exact absurd h0 hn₀K
    · have hn₁K : n₁ ∈ Kset σ₀ χ P := by
        by_contra hcon
        rcases hmin n₁ ((hZ n₁).mpr ⟨hn₁, hcon⟩) with h | h
        · have h1 : n₁ ∈ sc n₁ := self_mem_sc n₁
          rw [h] at h1
          exact mem_irrefl n₁ h1
        · exact mem_asymm h (self_mem_sc n₁)
      obtain ⟨p, hp, hs⟩ := ((mem_kset σ₀ χ hP).mp hn₁K).2 q hq
      refine ⟨p, hp, satF_sub σ₀ χ (fun j hj _ => ?_) hs⟩
      obtain ⟨hjo, hjK⟩ := (mem_jset σ₀ χ).mp hj
      have hOj := ord_mem ord_om hjo
      have hOn := ord_mem ord_om hn₁
      rcases ord_tri hOj hOn with h | h | h
      · exact h
      · exact absurd (h ▸ hjK) hn₀K
      · refine absurd (kset_down σ₀ χ hP hjK ?_) hn₀K
        rcases ord_sc_le hOn hOj h with h' | h'
        · exact h' ▸ self_mem_sc j
        · exact mem_sc.mpr (Or.inr h')

omit hP in
theorem jset_sub {j : V} (hj : j ∈ Jset σ₀ χ P) : j ∈ (om : V) := ((mem_jset σ₀ χ).mp hj).1

theorem satR_mono (q q' p p' : V) (hq : q ∈ (om : V)) (hq' : q' ∈ (om : V))
    (hs : ∀ α, α ∈ q → α ∈ q') (hp : ∀ α, α ∈ q → (α ∈ p ↔ α ∈ p'))
    (h : SatR σ₀ χ V q' p' P (om : V) (Jset σ₀ χ P)) :
    SatR σ₀ χ V q p P (om : V) (Jset σ₀ χ P) :=
  (sat_iff σ₀ χ hP (fun α hα => (ord_om (V := V)).1 q hq α hα) (fun _ => jset_sub σ₀ χ)).mpr
    (satF_mono σ₀ χ hs hp ((sat_iff σ₀ χ hP (fun α hα => (ord_om (V := V)).1 q' hq' α hα)
      (fun _ => jset_sub σ₀ χ)).mp h))

/-- **The leftmost assignment for `σ₀` and the instances at the members of `Jset`.** -/
def IsS (S P : V) : Prop :=
  Can (SatR σ₀ χ) (om : V) (℘ om) S P (om : V) (Jset σ₀ χ P)

omit hP in
theorem exists_isS : ∃ S : V, IsS σ₀ χ S P := exists_can (satB σ₀ χ)

omit hP in
theorem isS_unique {S S' : V} (h : IsS σ₀ χ S P) (h' : IsS σ₀ χ S' P) : S = S' :=
  can_unique (satB σ₀ χ) h h'

theorem isS_satF (h0 : (∅ : V) ∈ Kset σ₀ χ P) {S : V} (hS : IsS σ₀ χ S P) (q : V)
    (hq : q ∈ (om : V)) : SatF σ₀ χ (Jset σ₀ χ P) S q := by
  have h := can_sat (satB σ₀ χ) (satR_mono σ₀ χ hP) (fun q hq => by
    obtain ⟨p, hp, hs⟩ := sat_ne σ₀ χ hP h0 q hq
    exact ⟨p, hp, (sat_iff σ₀ χ hP (fun α hα => (ord_om (V := V)).1 q hq α hα)
      (fun _ => jset_sub σ₀ χ)).mpr hs⟩) hS q hq
  exact (sat_iff σ₀ χ hP (fun α hα => (ord_om (V := V)).1 q hq α hα)
    (fun _ => jset_sub σ₀ χ)).mp h

/-- **The leftmost assignment makes `σ₀` true, and the instances of `χ` at all the members of
`Jset`.** -/
theorem can_holds (h0 : (∅ : V) ∈ Kset σ₀ χ P) {S : V} (hS : IsS σ₀ χ S P) :
    Holds S σ₀ 0 ![] ∧ ∀ j, j ∈ Jset σ₀ χ P → Holds S χ (cnt σ₀) (envJ j) := by
  refine ⟨holds_of_holdsQ σ₀ 0 ![] (fun i => i.elim0) ∅ empty_mem_om
    (fun q hq _ => (isS_satF σ₀ χ hP h0 hS q hq).1), fun j hj => ?_⟩
  have hjo := jset_sub σ₀ χ hj
  exact holds_of_holdsQ χ _ (envJ j) (envJ_mem_om hjo) (sc j) (sc_mem_om hjo)
    (fun q hq hs => (isS_satF σ₀ χ hP h0 hS q hq).2 j hj (hs j (self_mem_sc j)))

omit hP in
theorem isS_sub {S : V} (hS : IsS σ₀ χ S P) {α : V} (hα : α ∈ S) : α ∈ (om : V) := hS.1 α hα

omit hP in
/-- If all the numerals are in `Kset`, they are in `Jset`. -/
theorem jset_nm (hK : ∀ n : ℕ, (nm n : V) ∈ Kset σ₀ χ P) (n : ℕ) : (nm n : V) ∈ Jset σ₀ χ P :=
  (mem_jset σ₀ χ).mpr ⟨nm_mem_om n, hK (n + 1)⟩

end model

end MH

end FFL.FirstOrder.SetTheory
