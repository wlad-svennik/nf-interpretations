module

public import HkModel

@[expose] public section

/-!
# Truth in a set structure, by a bounded formula on valuations

Inside a model `V` of `𝗠𝗛`. A valuation of `n` variables in a set `A` is coded by the finite
function `fnc e` on the numeral `n`: the variable `i` has the coordinate `n - 1 - i`, so that a
new variable `0` is a new pair at the coordinate `n` and no coordinate moves.

* `RS o A FS φ s`: the formula `φ` is true in the structure `(A, ∈)` under the valuation coded
  by `s`, by a bounded formula (`rsB`); `FS` is a set that contains the codes.
* **`rs_iff`**: `RS` at `fnc e` is truth in the structure of the members of `A`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Bounded definitions -/

section rdefs

variable {V : Type} [SetStructure V]

/-- `s' = s ∪ {⟨k, b⟩}`. -/
def Ext (s' s k b : V) : Prop :=
  (∀ p, p ∈ s' → (p ∈ s ∨ IsOp p k b)) ∧ ((∀ p, p ∈ s → p ∈ s') ∧ Pr s' k b)

/-- `s' = s ∪ {⟨n, b⟩}` for the numeral `n`. -/
def ExtN (o s' s : V) (n : ℕ) (b : V) : Prop := ∃ z, z ∈ o ∧ (IsNum n z ∧ Ext s' s z b)

/-- `s` has the value `a` at the coordinate `k`. -/
def AtC (o s : V) (k : ℕ) (a : V) : Prop := ∃ z, z ∈ o ∧ (IsNum k z ∧ Pr s z a)

/-- The atomic condition of a relation symbol. -/
def RAt : {k : ℕ} → (ℒₛₑₜ).Rel k → V → V → Prop
  | _, Language.Set.Rel.eq, a, b => a = b
  | _, Language.Set.Rel.mem, a, b => a ∈ b

/-- **Truth in `(A, ∈)` under the valuation coded by `s`.** -/
def RS (o A FS : V) : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → V → Prop
  | n, .rel r v, s => ∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC o s (n - 1 - aL r v) a ∧
      (AtC o s (n - 1 - aR r v) b ∧ RAt r a b))
  | n, .nrel r v, s => ∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC o s (n - 1 - aL r v) a ∧
      (AtC o s (n - 1 - aR r v) b ∧ ¬RAt r a b))
  | _, ⊤, _ => True
  | _, ⊥, _ => False
  | _, φ ⋏ ψ, s => RS o A FS φ s ∧ RS o A FS ψ s
  | _, φ ⋎ ψ, s => RS o A FS φ s ∨ RS o A FS ψ s
  | n, ∀¹ φ, s => ∀ b, b ∈ A → ∀ s', s' ∈ FS → (ExtN o s' s n b → RS o A FS φ s')
  | n, ∃¹ φ, s => ∃ b, b ∈ A ∧ ∃ s', s' ∈ FS ∧ (ExtN o s' s n b ∧ RS o A FS φ s')

end rdefs

def extB : BDef (k := 4) (fun V _ v ↦ Ext (v 0) (v 1) (v 2) (v 3)) :=
  ((BDef.ball 0 ((BDef.mem 0 2).or (isOpB.comp ![0, 3, 4]))).and
    ((BDef.ball 1 (BDef.mem 0 1)).and (prB.comp ![0, 2, 3]))).congr fun _ _ _ => Iff.rfl

def extNB (n : ℕ) : BDef (k := 4) (fun V _ v ↦ ExtN (v 0) (v 1) (v 2) n (v 3)) :=
  (BDef.bex 0 (((isNumB n).comp ![0]).and (extB.comp ![2, 3, 0, 4]))).congr
    fun _ _ _ => Iff.rfl

def atCB (k : ℕ) : BDef (k := 3) (fun V _ v ↦ AtC (v 0) (v 1) k (v 2)) :=
  (BDef.bex 0 (((isNumB k).comp ![0]).and (prB.comp ![2, 0, 3]))).congr fun _ _ _ => Iff.rfl

def ratB : {k : ℕ} → (r : (ℒₛₑₜ).Rel k) → BDef (k := 2) (fun V _ v ↦ RAt r (v 0) (v 1))
  | _, Language.Set.Rel.eq => (BDef.eq 0 1).congr fun _ _ _ => Iff.rfl
  | _, Language.Set.Rel.mem => (BDef.mem 0 1).congr fun _ _ _ => Iff.rfl

def rsB : {n : ℕ} → (φ : Semiformula ℒₛₑₜ Empty n) →
    BDef (k := 4) (fun V _ v ↦ RS (v 0) (v 1) (v 2) φ (v 3))
  | n, .rel r v => (BDef.bex 1 (BDef.bex 2 (((atCB (n - 1 - aL r v)).comp ![2, 5, 1]).and
      (((atCB (n - 1 - aR r v)).comp ![2, 5, 0]).and ((ratB r).comp ![1, 0]))))).congr
      fun _ _ _ => Iff.rfl
  | n, .nrel r v => (BDef.bex 1 (BDef.bex 2 (((atCB (n - 1 - aL r v)).comp ![2, 5, 1]).and
      (((atCB (n - 1 - aR r v)).comp ![2, 5, 0]).and ((ratB r).comp ![1, 0]).not)))).congr
      fun _ _ _ => Iff.rfl
  | _, ⊤ => BDef.tru.congr fun _ _ _ => Iff.rfl
  | _, ⊥ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, φ ⋏ ψ => ((rsB φ).and (rsB ψ)).congr fun _ _ _ => Iff.rfl
  | _, φ ⋎ ψ => ((rsB φ).or (rsB ψ)).congr fun _ _ _ => Iff.rfl
  | n, ∀¹ φ => (BDef.ball 1 (BDef.ball 3 (((extNB n).comp ![2, 0, 5, 1]).imp
      ((rsB φ).comp ![2, 3, 4, 0])))).congr fun _ _ _ => Iff.rfl
  | n, ∃¹ φ => (BDef.bex 1 (BDef.bex 3 (((extNB n).comp ![2, 0, 5, 1]).and
      ((rsB φ).comp ![2, 3, 4, 0])))).congr fun _ _ _ => Iff.rfl

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **The code of a valuation.** -/
noncomputable def fnc : {n : ℕ} → (Fin n → V) → V
  | 0, _ => ∅
  | n + 1, e => insert (kp (nm n) (e 0)) (fnc fun i ↦ e i.succ)

theorem fnc_cons {n : ℕ} (b : V) (e : Fin n → V) :
    fnc (b :> e) = insert (kp (nm n) b) (fnc e) := rfl

theorem mem_fnc : ∀ {n : ℕ} (e : Fin n → V) (p : V),
    p ∈ fnc e ↔ ∃ i : Fin n, p = kp (nm (n - 1 - i)) (e i)
  | 0, _, p => by
    show p ∈ (∅ : V) ↔ _
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨i, -⟩; exact i.elim0
  | n + 1, e, p => by
    show p ∈ (insert (kp (nm n) (e 0)) (fnc fun i ↦ e i.succ) : V) ↔ _
    rw [mem_insert, mem_fnc (fun i ↦ e i.succ) p]
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨0, by simp⟩
      · refine ⟨i.succ, ?_⟩
        have : n + 1 - 1 - ((i.succ : Fin (n + 1)) : ℕ) = n - 1 - (i : ℕ) := by
          simp only [Fin.val_succ]; omega
        rw [this]
    · rintro ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact Or.inl (by simp)
      | succ j =>
        refine Or.inr ⟨j, ?_⟩
        have : n + 1 - 1 - ((j.succ : Fin (n + 1)) : ℕ) = n - 1 - (j : ℕ) := by
          simp only [Fin.val_succ]; omega
        rw [this]

theorem atC_fnc {n : ℕ} (e : Fin n → V) (i : Fin n) (a : V) :
    AtC (om : V) (fnc e) (n - 1 - i) a ↔ a = e i := by
  constructor
  · rintro ⟨z, -, hz, hpr⟩
    obtain rfl := (isNum_iff _ z).mp hz
    obtain ⟨j, hj⟩ := (mem_fnc e _).mp (pr_iff.mp hpr)
    obtain ⟨e1, e2⟩ := kp_inj hj
    have e3 := nm_inj e1
    have : i = j := Fin.ext (by have := i.2; have := j.2; omega)
    rw [e2, this]
  · rintro rfl
    exact ⟨_, nm_mem_om _, isNum_nm _, pr_iff.mpr ((mem_fnc e _).mpr ⟨i, rfl⟩)⟩

theorem fnc_mem_pow {n : ℕ} {A : V} (e : Fin n → V) (he : ∀ i, e i ∈ A) :
    fnc e ∈ (℘ (prodS (om : V) A) : V) :=
  mem_power_iff.mpr fun p hp => by
    obtain ⟨i, rfl⟩ := (mem_fnc e p).mp hp
    exact mem_prodS.mpr ⟨_, nm_mem_om _, _, he i, rfl⟩

theorem extN_fnc {n : ℕ} (e : Fin n → V) (b s' : V) :
    ExtN (om : V) s' (fnc e) n b ↔ s' = fnc (b :> e) := by
  rw [fnc_cons]
  constructor
  · rintro ⟨z, -, hz, h1, h2, h3⟩
    obtain rfl := (isNum_iff _ z).mp hz
    refine mem_ext fun p => ?_
    rw [mem_insert]
    constructor
    · intro hp
      rcases h1 p hp with h | h
      · exact Or.inr h
      · exact Or.inl (isOp_iff.mp h)
    · rintro (rfl | h)
      · exact pr_iff.mp h3
      · exact h2 p h
  · rintro rfl
    refine ⟨_, nm_mem_om n, isNum_nm n, fun p hp => ?_, fun p hp => ?_, ?_⟩
    · rcases mem_insert.mp hp with rfl | h
      · exact Or.inr (isOp_kp _ _)
      · exact Or.inl h
    · exact mem_insert.mpr (Or.inr hp)
    · exact pr_iff.mpr (mem_insert.mpr (Or.inl rfl))

/-- **`RS` at the code of a valuation is truth in the structure of the members of `A`.** -/
theorem rs_iff {A : V} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (e : Fin n → extSet A),
    RS (om : V) A (℘ (prodS (om : V) A)) φ (fnc fun i ↦ (e i : V)) ↔
      Eval (M := extSet A) e Empty.elim φ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; exact Iff.rfl
  | hfalsum => intro e; exact Iff.rfl
  | hrel r v =>
    intro e
    cases r with
    | eq =>
      show (∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC _ _ _ a ∧ (AtC _ _ _ b ∧ a = b))) ↔
        (v 0).val (M := extSet A) e _ = (v 1).val (M := extSet A) e _
      rw [tix_val, tix_val]
      constructor
      · rintro ⟨a, -, b, -, ha, hb, hab⟩
        rw [(atC_fnc _ _ a).mp ha, (atC_fnc _ _ b).mp hb] at hab
        exact Subtype.ext hab
      · intro h
        exact ⟨_, (e _).2, _, (e _).2, (atC_fnc _ _ _).mpr rfl, (atC_fnc _ _ _).mpr rfl,
          congrArg Subtype.val h⟩
    | mem =>
      show (∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC _ _ _ a ∧ (AtC _ _ _ b ∧ a ∈ b))) ↔
        (v 0).val (M := extSet A) e _ ∈ (v 1).val (M := extSet A) e _
      rw [tix_val, tix_val]
      constructor
      · rintro ⟨a, -, b, -, ha, hb, hab⟩
        rw [(atC_fnc _ _ a).mp ha, (atC_fnc _ _ b).mp hb] at hab
        exact hab
      · intro h
        exact ⟨_, (e _).2, _, (e _).2, (atC_fnc _ _ _).mpr rfl, (atC_fnc _ _ _).mpr rfl, h⟩
  | hnrel r v =>
    intro e
    cases r with
    | eq =>
      show (∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC _ _ _ a ∧ (AtC _ _ _ b ∧ ¬a = b))) ↔
        ¬(v 0).val (M := extSet A) e _ = (v 1).val (M := extSet A) e _
      rw [tix_val, tix_val]
      constructor
      · rintro ⟨a, -, b, -, ha, hb, hab⟩ h
        rw [(atC_fnc _ _ a).mp ha, (atC_fnc _ _ b).mp hb] at hab
        exact hab (congrArg Subtype.val h)
      · intro h
        exact ⟨_, (e _).2, _, (e _).2, (atC_fnc _ _ _).mpr rfl, (atC_fnc _ _ _).mpr rfl,
          fun h' => h (Subtype.ext h')⟩
    | mem =>
      show (∃ a, a ∈ A ∧ ∃ b, b ∈ A ∧ (AtC _ _ _ a ∧ (AtC _ _ _ b ∧ ¬a ∈ b))) ↔
        ¬(v 0).val (M := extSet A) e _ ∈ (v 1).val (M := extSet A) e _
      rw [tix_val, tix_val]
      constructor
      · rintro ⟨a, -, b, -, ha, hb, hab⟩ h
        rw [(atC_fnc _ _ a).mp ha, (atC_fnc _ _ b).mp hb] at hab
        exact hab h
      · intro h
        exact ⟨_, (e _).2, _, (e _).2, (atC_fnc _ _ _).mpr rfl, (atC_fnc _ _ _).mpr rfl, h⟩
  | hand φ ψ ih1 ih2 => intro e; exact and_congr (ih1 e) (ih2 e)
  | hor φ ψ ih1 ih2 => intro e; exact or_congr (ih1 e) (ih2 e)
  | hall φ ih =>
    intro e
    have hc : ∀ x : extSet A, (fun i ↦ (((x :> e) i : extSet A) : V)) =
        ((x : V) :> fun i ↦ (e i : V)) := by
      intro x; funext i; cases i using Fin.cases <;> rfl
    constructor
    · intro h x
      have := h x.1 x.2 _ (fnc_mem_pow _ (fun i => by
        cases i using Fin.cases with
        | zero => exact x.2
        | succ j => exact (e j).2)) ((extN_fnc _ _ _).mpr rfl)
      rw [← hc x] at this
      exact (ih _).mp this
    · intro h b hb s' _ hext
      obtain rfl := (extN_fnc _ _ _).mp hext
      have := (ih _).mpr (h ⟨b, hb⟩)
      rw [hc ⟨b, hb⟩] at this
      exact this
  | hexs φ ih =>
    intro e
    have hc : ∀ x : extSet A, (fun i ↦ (((x :> e) i : extSet A) : V)) =
        ((x : V) :> fun i ↦ (e i : V)) := by
      intro x; funext i; cases i using Fin.cases <;> rfl
    constructor
    · rintro ⟨b, hb, s', -, hext, h⟩
      obtain rfl := (extN_fnc _ _ _).mp hext
      rw [← hc ⟨b, hb⟩] at h
      exact ⟨⟨b, hb⟩, (ih _).mp h⟩
    · rintro ⟨x, h⟩
      have := (ih _).mpr h
      rw [hc x] at this
      exact ⟨x.1, x.2, _, fnc_mem_pow _ (fun i => by
        cases i using Fin.cases with
        | zero => exact x.2
        | succ j => exact (e j).2), (extN_fnc _ _ _).mpr rfl, this⟩

end model

end MH

end FFL.FirstOrder.SetTheory
