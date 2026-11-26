module

public import HkHolds

@[expose] public section

/-!
# Compactness inside a model of `𝗠𝗛`: the leftmost assignment

Inside a model `V` of `𝗠𝗛`. Let `R q p` be a condition with a bounded definition on a number
`q` and a set `p` of numbers (with three parameters), such that

* `R` is preserved when the bound `q` is lowered and `p` is changed above the bound (`hmono`);
* for every `q` some `p` satisfies `R q p` (`hne`).

Then there is exactly one set `S` of numbers such that a number `i` is in `S` exactly when,
for every bound, some `p` that agrees with `S` below `i` and contains `i` satisfies `R`
(`Can`, `exists_can`, `can_unique`), and **`R q S` for every `q`** (`can_sat`).

The proof is König's lemma for the tree of the assignments, by induction on the numbers of
the model: all the conditions are bounded, with `ω` and its power set as parameters.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-- A relation of five arguments, in every structure. -/
abbrev Rel5 := ∀ (V : Type) [SetStructure V], V → V → V → V → V → Prop

section defs

variable {V : Type} [SetStructure V] (R : Rel5)

/-- For every bound, some assignment that agrees with `s` below `i` and contains `i` satisfies
the condition. -/
def GoodT (o PO i s a b c : V) : Prop :=
  ∀ q, q ∈ o → (i ∈ q → ∃ p, p ∈ PO ∧
    ((∀ α, α ∈ i → (α ∈ p ↔ α ∈ s)) ∧ (i ∈ p ∧ R V q p a b c)))

/-- For every bound from `k` on, some assignment that agrees with `s` below `k` satisfies the
condition. -/
def GoodA (o PO k s a b c : V) : Prop :=
  ∀ q, q ∈ o → ((k = q ∨ k ∈ q) → ∃ p, p ∈ PO ∧
    ((∀ α, α ∈ k → (α ∈ p ↔ α ∈ s)) ∧ R V q p a b c))

/-- `s` is the leftmost assignment below `k`. -/
def Corr (o PO k s a b c : V) : Prop :=
  ∀ i, i ∈ k → (i ∈ s ↔ GoodT R o PO i s a b c)

/-- `S` is the leftmost assignment. -/
def Can (o PO S a b c : V) : Prop :=
  (∀ i, i ∈ S → i ∈ o) ∧ ∀ i, i ∈ o → (i ∈ S ↔ GoodT R o PO i S a b c)

/-- The condition that defines the leftmost assignment. -/
def CanDef (i o PO a b c : V) : Prop :=
  ∃ s, s ∈ PO ∧ (Corr R o PO i s a b c ∧ GoodT R o PO i s a b c)

/-- The statement of `corr_goodA`. -/
def CGA (k o PO a b c : V) : Prop :=
  ∀ s, s ∈ PO → (Corr R o PO k s a b c → GoodA R o PO k s a b c)

/-- The statement of `corr_unique`. -/
def CUQ (k o PO a b c : V) : Prop :=
  ∀ s, s ∈ PO → ∀ s', s' ∈ PO → (Corr R o PO k s a b c → (Corr R o PO k s' a b c →
    ∀ i, i ∈ k → (i ∈ s ↔ i ∈ s')))

/-- The statement of `corr_exists`. -/
def CEX (k o PO a b c : V) : Prop := ∃ s, s ∈ PO ∧ Corr R o PO k s a b c

end defs

section bdefs

variable {R : Rel5} (dR : BDef (k := 5) (fun V _ v ↦ R V (v 0) (v 1) (v 2) (v 3) (v 4)))

def goodTB : BDef (k := 7) (fun V _ v ↦ GoodT R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.ball 0 ((BDef.mem 3 0).imp (BDef.bex 2
    ((BDef.ball 4 ((BDef.mem 0 1).iff (BDef.mem 0 6))).and
      ((BDef.mem 4 0).and (dR.comp ![1, 0, 6, 7, 8])))))).congr fun _ _ _ => Iff.rfl

def goodAB : BDef (k := 7) (fun V _ v ↦ GoodA R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.ball 0 (((BDef.eq 3 0).or (BDef.mem 3 0)).imp (BDef.bex 2
    ((BDef.ball 4 ((BDef.mem 0 1).iff (BDef.mem 0 6))).and
      (dR.comp ![1, 0, 6, 7, 8]))))).congr fun _ _ _ => Iff.rfl

def corrB : BDef (k := 7) (fun V _ v ↦ Corr R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.ball 2 ((BDef.mem 0 4).iff ((goodTB dR).comp ![1, 2, 0, 4, 5, 6, 7]))).congr
    fun _ _ _ => Iff.rfl

def canB : BDef (k := 6) (fun V _ v ↦ Can R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  ((BDef.ball 2 (BDef.mem 0 1)).and (BDef.ball 0 ((BDef.mem 0 3).iff
    ((goodTB dR).comp ![1, 2, 0, 3, 4, 5, 6])))).congr fun _ _ _ => Iff.rfl

def canDefB : BDef (k := 6) (fun V _ v ↦ CanDef R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 2 (((corrB dR).comp ![2, 3, 1, 0, 4, 5, 6]).and
    ((goodTB dR).comp ![2, 3, 1, 0, 4, 5, 6]))).congr fun _ _ _ => Iff.rfl

def cgaB : BDef (k := 6) (fun V _ v ↦ CGA R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.ball 2 (((corrB dR).comp ![2, 3, 1, 0, 4, 5, 6]).imp
    ((goodAB dR).comp ![2, 3, 1, 0, 4, 5, 6]))).congr fun _ _ _ => Iff.rfl

def cuqB : BDef (k := 6) (fun V _ v ↦ CUQ R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.ball 2 (BDef.ball 3 (((corrB dR).comp ![3, 4, 2, 1, 5, 6, 7]).imp
    (((corrB dR).comp ![3, 4, 2, 0, 5, 6, 7]).imp
      (BDef.ball 2 ((BDef.mem 0 2).iff (BDef.mem 0 1))))))).congr fun _ _ _ => Iff.rfl

def cexB : BDef (k := 6) (fun V _ v ↦ CEX R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.bex 2 ((corrB dR).comp ![2, 3, 1, 0, 4, 5, 6])).congr fun _ _ _ => Iff.rfl

end bdefs

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]
variable {R : Rel5} (dR : BDef (k := 5) (fun V _ v ↦ R V (v 0) (v 1) (v 2) (v 3) (v 4)))
variable {a b c : V}

theorem goodT_congr {i s s' : V} (h : ∀ α, α ∈ i → (α ∈ s ↔ α ∈ s'))
    (hg : GoodT R (om : V) (℘ om) i s a b c) : GoodT R (om : V) (℘ om) i s' a b c := by
  intro q hq hiq
  obtain ⟨p, hp, hag, hip, hR⟩ := hg q hq hiq
  exact ⟨p, hp, fun α hα => (hag α hα).trans (h α hα), hip, hR⟩

theorem corr_down {k k' s : V} (hsub : ∀ i, i ∈ k' → i ∈ k)
    (h : Corr R (om : V) (℘ om) k s a b c) : Corr R (om : V) (℘ om) k' s a b c :=
  fun i hi => h i (hsub i hi)

theorem om_mem_tr {n i α : V} (hn : n ∈ (om : V)) (hi : i ∈ n) (hα : α ∈ i) : α ∈ n :=
  (ord_mem ord_om hn).1 i hi α hα

variable (hmono : ∀ q q' p p' : V, q ∈ (om : V) → q' ∈ (om : V) → (∀ α, α ∈ q → α ∈ q') →
  (∀ α, α ∈ q → (α ∈ p ↔ α ∈ p')) → R V q' p' a b c → R V q p a b c)
variable (hne : ∀ q, q ∈ (om : V) → ∃ p, p ∈ (℘ om : V) ∧ R V q p a b c)

include dR hmono hne in
/-- **An assignment that is leftmost below `k` extends, for every bound, to one that satisfies
the condition.** -/
theorem corr_goodA : ∀ k, k ∈ (om : V) → ∀ s, s ∈ (℘ om : V) →
    Corr R (om : V) (℘ om) k s a b c → GoodA R (om : V) (℘ om) k s a b c := by
  have key := om_ind (cgaB dR) ![(om : V), ℘ om, a, b, c] (by
    intro s _ _ q hq _
    obtain ⟨p, hp, hR⟩ := hne q hq
    exact ⟨p, hp, fun α hα => absurd hα (by simp), hR⟩) (by
    intro n hn ih s hs hcor
    have hcn : Corr R (om : V) (℘ om) n s a b c :=
      corr_down (fun i hi => mem_sc.mpr (Or.inr hi)) hcor
    have hga : GoodA R (om : V) (℘ om) n s a b c := ih s hs hcn
    have hnq : ∀ q, q ∈ (om : V) → (sc n = q ∨ sc n ∈ q) → n ∈ q := by
      intro q hq h
      rcases h with h | h
      · exact h ▸ self_mem_sc n
      · exact (ord_mem ord_om hq).1 _ h n (self_mem_sc n)
    by_cases hns : n ∈ s
    · have hgt : GoodT R (om : V) (℘ om) n s a b c := (hcor n (self_mem_sc n)).mp hns
      intro q hq hsq
      obtain ⟨p, hp, hag, hnp, hR⟩ := hgt q hq (hnq q hq hsq)
      refine ⟨p, hp, fun α hα => ?_, hR⟩
      rcases mem_sc.mp hα with rfl | hα
      · exact ⟨fun _ => hns, fun _ => hnp⟩
      · exact hag α hα
    · have hngt : ¬GoodT R (om : V) (℘ om) n s a b c :=
        fun h => hns ((hcor n (self_mem_sc n)).mpr h)
      simp only [GoodT, not_forall] at hngt
      obtain ⟨q₁, hq₁, hnq₁, hno⟩ := hngt
      intro q hq hsq
      have hnq' := hnq q hq hsq
      obtain ⟨m, hm, h1, h2⟩ := om_max hq hq₁
      obtain ⟨p₂, hp₂, hag, hR⟩ := hga m hm (Or.inr (h1 n hnq'))
      have hnp₂ : ¬n ∈ p₂ := fun hin =>
        hno ⟨p₂, hp₂, hag, hin, hmono q₁ m p₂ p₂ hq₁ hm h2 (fun _ _ => Iff.rfl) hR⟩
      refine ⟨p₂, hp₂, fun α hα => ?_, hmono q m p₂ p₂ hq hm h1 (fun _ _ => Iff.rfl) hR⟩
      rcases mem_sc.mp hα with rfl | hα
      · exact ⟨fun h => absurd h hnp₂, fun h => absurd h hns⟩
      · exact hag α hα)
  exact fun k hk => key k hk

include dR in
/-- **Two assignments that are leftmost below `k` agree below `k`.** -/
theorem corr_unique : ∀ k, k ∈ (om : V) → ∀ s, s ∈ (℘ om : V) → ∀ s', s' ∈ (℘ om : V) →
    Corr R (om : V) (℘ om) k s a b c → Corr R (om : V) (℘ om) k s' a b c →
    ∀ i, i ∈ k → (i ∈ s ↔ i ∈ s') := by
  have key := om_ind (cuqB dR) ![(om : V), ℘ om, a, b, c] (by
    intro s _ s' _ _ _ i hi
    exact absurd hi (by simp)) (by
    intro n hn ih s hs s' hs' hcor hcor' i hi
    have hag := ih s hs s' hs' (corr_down (fun i hi => mem_sc.mpr (Or.inr hi)) hcor)
      (corr_down (fun i hi => mem_sc.mpr (Or.inr hi)) hcor')
    rcases mem_sc.mp hi with rfl | hi'
    · exact (hcor i (self_mem_sc i)).trans
        (Iff.trans ⟨goodT_congr hag, goodT_congr fun α hα => (hag α hα).symm⟩
          (hcor' i (self_mem_sc i)).symm)
    · exact hag i hi')
  exact fun k hk => key k hk

include dR in
/-- **For every `k` there is an assignment that is leftmost below `k`.** -/
theorem corr_exists : ∀ k, k ∈ (om : V) →
    ∃ s, s ∈ (℘ om : V) ∧ Corr R (om : V) (℘ om) k s a b c := by
  have key := om_ind (cexB dR) ![(om : V), ℘ om, a, b, c] (by
    exact ⟨∅, mem_power_iff.mpr fun z hz => absurd hz (by simp), fun i hi => absurd hi (by simp)⟩)
    (by
    rintro n hn ⟨s, hs, hcor⟩
    by_cases hg : GoodT R (om : V) (℘ om) n s a b c
    · let s' : V := sepB (k := 2) (((BDef.mem 0 1).and (BDef.mem 0 2)).or (BDef.eq 0 1))
        (om : V) ![n, s]
      have hs' : ∀ i, i ∈ s' ↔ i ∈ (om : V) ∧ ((i ∈ n ∧ i ∈ s) ∨ i = n) :=
        fun i => mem_sepB _ _ _ i
      have hag : ∀ α, α ∈ n → (α ∈ s ↔ α ∈ s') := fun α hα =>
        ⟨fun h => (hs' α).mpr ⟨(ord_om (V := V)).1 n hn α hα, Or.inl ⟨hα, h⟩⟩, fun h => by
          rcases ((hs' α).mp h).2 with h | h
          · exact h.2
          · exact absurd (h ▸ hα) (mem_irrefl n)⟩
      refine ⟨s', mem_power_iff.mpr fun z hz => ((hs' z).mp hz).1, fun i hi => ?_⟩
      rcases mem_sc.mp hi with rfl | hi'
      · exact ⟨fun _ => goodT_congr hag hg, fun _ => (hs' i).mpr ⟨hn, Or.inr rfl⟩⟩
      · exact (hag i hi').symm.trans ((hcor i hi').trans
          ⟨goodT_congr fun α hα => hag α (om_mem_tr hn hi' hα),
            goodT_congr fun α hα => (hag α (om_mem_tr hn hi' hα)).symm⟩)
    · let s' : V := sepB (k := 2) ((BDef.mem 0 1).and (BDef.mem 0 2)) (om : V) ![n, s]
      have hs' : ∀ i, i ∈ s' ↔ i ∈ (om : V) ∧ (i ∈ n ∧ i ∈ s) := fun i => mem_sepB _ _ _ i
      have hag : ∀ α, α ∈ n → (α ∈ s ↔ α ∈ s') := fun α hα =>
        ⟨fun h => (hs' α).mpr ⟨(ord_om (V := V)).1 n hn α hα, hα, h⟩,
          fun h => ((hs' α).mp h).2.2⟩
      refine ⟨s', mem_power_iff.mpr fun z hz => ((hs' z).mp hz).1, fun i hi => ?_⟩
      rcases mem_sc.mp hi with rfl | hi'
      · exact ⟨fun h => absurd ((hs' i).mp h).2.1 (mem_irrefl i),
          fun h => absurd (goodT_congr (fun α hα => (hag α hα).symm) h) hg⟩
      · exact (hag i hi').symm.trans ((hcor i hi').trans
          ⟨goodT_congr fun α hα => hag α (om_mem_tr hn hi' hα),
            goodT_congr fun α hα => (hag α (om_mem_tr hn hi' hα)).symm⟩))
  exact fun k hk => key k hk

include dR in
/-- **The leftmost assignment exists.** -/
theorem exists_can : ∃ S : V, Can R (om : V) (℘ om) S a b c := by
  let S : V := sepB (canDefB dR) (om : V) ![(om : V), ℘ om, a, b, c]
  have hS : ∀ i, i ∈ S ↔ i ∈ (om : V) ∧ CanDef R i (om : V) (℘ om) a b c :=
    fun i => mem_sepB (canDefB dR) _ _ i
  have hSP : S ∈ (℘ om : V) := mem_power_iff.mpr fun z hz => ((hS z).mp hz).1
  have hmain : ∀ i, i ∈ (om : V) → ∀ s, s ∈ (℘ om : V) → Corr R (om : V) (℘ om) i s a b c →
      (∀ j, j ∈ i → (j ∈ S ↔ j ∈ s)) := by
    intro i hi s hs hcor j hj
    have hjo : j ∈ (om : V) := (ord_om (V := V)).1 i hi j hj
    have hcj : Corr R (om : V) (℘ om) j s a b c :=
      corr_down (fun α hα => om_mem_tr hi hj hα) hcor
    constructor
    · intro h
      obtain ⟨-, s', hs', hc', hg'⟩ := (hS j).mp h
      exact (hcor j hj).mpr (goodT_congr (corr_unique dR j hjo s' hs' s hs hc' hcj) hg')
    · intro h
      exact (hS j).mpr ⟨hjo, s, hs, hcj, (hcor j hj).mp h⟩
  refine ⟨S, fun i hi => ((hS i).mp hi).1, fun i hi => ?_⟩
  obtain ⟨s, hs, hcor⟩ := corr_exists dR i hi
  have hag := hmain i hi s hs hcor
  constructor
  · intro h
    obtain ⟨-, s', hs', hc', hg'⟩ := (hS i).mp h
    exact goodT_congr (fun α hα => ((hmain i hi s' hs' hc') α hα).symm) hg'
  · intro h
    exact (hS i).mpr ⟨hi, s, hs, hcor, goodT_congr hag h⟩

theorem can_corr {S : V} (hS : Can R (om : V) (℘ om) S a b c) (k : V) (hk : k ∈ (om : V)) :
    Corr R (om : V) (℘ om) k S a b c :=
  fun i hi => hS.2 i ((ord_om (V := V)).1 k hk i hi)

theorem can_mem_pow {S : V} (hS : Can R (om : V) (℘ om) S a b c) : S ∈ (℘ om : V) :=
  mem_power_iff.mpr hS.1

include dR in
/-- **The leftmost assignment is unique.** -/
theorem can_unique {S S' : V} (hS : Can R (om : V) (℘ om) S a b c)
    (hS' : Can R (om : V) (℘ om) S' a b c) : S = S' := by
  refine mem_ext fun i => ?_
  have key : ∀ i, i ∈ (om : V) → (i ∈ S ↔ i ∈ S') := fun i hi =>
    corr_unique dR (sc i) (sc_mem_om hi) S (can_mem_pow hS) S' (can_mem_pow hS')
      (can_corr hS _ (sc_mem_om hi)) (can_corr hS' _ (sc_mem_om hi)) i (self_mem_sc i)
  exact ⟨fun h => (key i (hS.1 i h)).mp h, fun h => (key i (hS'.1 i h)).mpr h⟩

include dR hmono hne in
/-- **The leftmost assignment satisfies the condition for every bound.** -/
theorem can_sat {S : V} (hS : Can R (om : V) (℘ om) S a b c) (q : V) (hq : q ∈ (om : V)) :
    R V q S a b c := by
  obtain ⟨p, -, hag, hR⟩ := corr_goodA dR hmono hne q hq S (can_mem_pow hS) (can_corr hS q hq)
    q hq (Or.inl rfl)
  exact hmono q q S p hq hq (fun _ h => h) (fun α hα => (hag α hα).symm) hR

end model

end MH

end FFL.FirstOrder.SetTheory
