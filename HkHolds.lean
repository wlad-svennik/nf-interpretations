module

public import HkPair

@[expose] public section

/-!
# Truth of a formula under an assignment of truth values to atomic sentences of numbers

Inside a model `V` of `𝗠𝗛`. The terms of the Henkin construction are the finite ordinals. An
atomic sentence is a number `atm r a b` (`r = 0` for membership, `r = 1` for equality), and a
set `S` of such numbers is an assignment of truth values. A formula in negation normal form is
read under `S` as follows (`Holds`): a universal quantifier ranges over all numbers, and an
existential quantifier is witnessed by the number `sk c (tup e)`, where `c` is the number of
the quantifier in the formula and `e` the values of the variables in its scope.

`HoldsQ p q` is the same below the bound `q`: universal quantifiers range over the numbers
below `q`, and a literal on an atomic sentence that is not below `q` counts as true.

* `holdsQ_mono`: `HoldsQ` is preserved by lowering the bound.
* `holdsQ_of_holds`, `holds_of_holdsQ`: `Holds S` is `HoldsQ S q` for all large `q`.
* `HQ P o p q φ c ε`: `HoldsQ` by a bounded formula (`hqB`), in terms of the set `P` of the
  triples of the pairing function and of the number `ε` of the environment; `hq_iff`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Syntax -/

section syn

/-- The number of the existential quantifiers of a formula. -/
def cnt : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, ⊤ => 0
  | _, ⊥ => 0
  | _, φ ⋏ ψ => cnt φ + cnt ψ
  | _, φ ⋎ ψ => cnt φ + cnt ψ
  | _, ∀¹ φ => cnt φ
  | _, ∃¹ φ => cnt φ + 1

/-- The variable that a term is. -/
def tix {n : ℕ} : Semiterm ℒₛₑₜ Empty n → Fin n
  | #x => x
  | &x => Empty.elim x
  | .func f _ => Empty.elim f

/-- The number of a relation symbol. -/
def rcode : {k : ℕ} → (ℒₛₑₜ).Rel k → ℕ
  | _, Language.Set.Rel.eq => 1
  | _, Language.Set.Rel.mem => 0

/-- The variable on the left of an atomic formula. -/
def aL {n : ℕ} : {k : ℕ} → (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ Empty n) → Fin n
  | _, Language.Set.Rel.eq, v => tix (v 0)
  | _, Language.Set.Rel.mem, v => tix (v 0)

/-- The variable on the right of an atomic formula. -/
def aR {n : ℕ} : {k : ℕ} → (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ Empty n) → Fin n
  | _, Language.Set.Rel.eq, v => tix (v 1)
  | _, Language.Set.Rel.mem, v => tix (v 1)

end syn

/-! ### The bounded formula -/

section rdefs

variable {V : Type} [SetStructure V]

/-- `x` is the entry number `i` of the environment `ε`. -/
def LookR (P o : V) : ℕ → V → V → Prop
  | 0, ε, x => ∃ ε', ε' ∈ o ∧ PG P x ε' ε
  | i + 1, ε, x => ∃ y, y ∈ o ∧ ∃ ε', ε' ∈ o ∧ (PG P y ε' ε ∧ LookR P o i ε' x)

/-- `α` is the atomic sentence of the relation number `r` and of `a`, `b`. -/
def AtomR (P o : V) (r : ℕ) (a b α : V) : Prop :=
  ∃ w, w ∈ o ∧ (PG P a b w ∧ ∃ z, z ∈ o ∧ (IsNum r z ∧ PG P z w α))

/-- `w` is the witness of the quantifier number `c` in the environment `ε`. -/
def SkR (P o : V) (c : ℕ) (ε w : V) : Prop :=
  ∃ z, z ∈ o ∧ (IsNum (c + 1) z ∧ PG P z ε w)

/-- **Truth below a bound, by a bounded formula.** -/
def HQ (P o p q : V) : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ → V → Prop
  | _, .rel r v, _, ε => ∀ a, a ∈ o → ∀ b, b ∈ o → (LookR P o (aL r v) ε a →
      (LookR P o (aR r v) ε b → ∀ α, α ∈ q → (AtomR P o (rcode r) a b α → α ∈ p)))
  | _, .nrel r v, _, ε => ∀ a, a ∈ o → ∀ b, b ∈ o → (LookR P o (aL r v) ε a →
      (LookR P o (aR r v) ε b → ∀ α, α ∈ q → (AtomR P o (rcode r) a b α → ¬α ∈ p)))
  | _, ⊤, _, _ => True
  | _, ⊥, _, _ => False
  | _, φ ⋏ ψ, c, ε => HQ P o p q φ c ε ∧ HQ P o p q ψ (c + cnt φ) ε
  | _, φ ⋎ ψ, c, ε => HQ P o p q φ c ε ∨ HQ P o p q ψ (c + cnt φ) ε
  | _, ∀¹ φ, c, ε => ∀ t, t ∈ q → ∀ ε', ε' ∈ o → (PG P t ε ε' → HQ P o p q φ c ε')
  | _, ∃¹ φ, c, ε => ∀ w, w ∈ o → (SkR P o c ε w →
      ∀ ε', ε' ∈ o → (PG P w ε ε' → HQ P o p q φ (c + 1) ε'))

end rdefs

def lookB : (i : ℕ) → BDef (k := 4) (fun V _ v ↦ LookR (v 0) (v 1) i (v 2) (v 3))
  | 0 => (BDef.bex 1 (pgB.comp ![1, 4, 0, 3])).congr fun _ _ _ => Iff.rfl
  | i + 1 => (BDef.bex 1 (BDef.bex 2 ((pgB.comp ![2, 1, 0, 4]).and
      ((lookB i).comp ![2, 3, 0, 5])))).congr fun _ _ _ => Iff.rfl

def atomB (r : ℕ) : BDef (k := 5) (fun V _ v ↦ AtomR (v 0) (v 1) r (v 2) (v 3) (v 4)) :=
  (BDef.bex 1 ((pgB.comp ![1, 3, 4, 0]).and (BDef.bex 2 (((isNumB r).comp ![0]).and
    (pgB.comp ![2, 0, 1, 6]))))).congr fun _ _ _ => Iff.rfl

def skB (c : ℕ) : BDef (k := 4) (fun V _ v ↦ SkR (v 0) (v 1) c (v 2) (v 3)) :=
  (BDef.bex 1 (((isNumB (c + 1)).comp ![0]).and (pgB.comp ![1, 0, 3, 4]))).congr
    fun _ _ _ => Iff.rfl

def hqB : {n : ℕ} → (φ : Semiformula ℒₛₑₜ Empty n) → (c : ℕ) →
    BDef (k := 5) (fun V _ v ↦ HQ (v 0) (v 1) (v 2) (v 3) φ c (v 4))
  | _, .rel r v, _ => (BDef.ball 1 (BDef.ball 2 (((lookB (aL r v)).comp ![2, 3, 6, 1]).imp
      (((lookB (aR r v)).comp ![2, 3, 6, 0]).imp (BDef.ball 5
        (((atomB (rcode r)).comp ![3, 4, 2, 1, 0]).imp (BDef.mem 0 5))))))).congr
      fun _ _ _ => Iff.rfl
  | _, .nrel r v, _ => (BDef.ball 1 (BDef.ball 2 (((lookB (aL r v)).comp ![2, 3, 6, 1]).imp
      (((lookB (aR r v)).comp ![2, 3, 6, 0]).imp (BDef.ball 5
        (((atomB (rcode r)).comp ![3, 4, 2, 1, 0]).imp (BDef.mem 0 5).not)))))).congr
      fun _ _ _ => Iff.rfl
  | _, ⊤, _ => BDef.tru.congr fun _ _ _ => Iff.rfl
  | _, ⊥, _ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, φ ⋏ ψ, c => ((hqB φ c).and (hqB ψ (c + cnt φ))).congr fun _ _ _ => Iff.rfl
  | _, φ ⋎ ψ, c => ((hqB φ c).or (hqB ψ (c + cnt φ))).congr fun _ _ _ => Iff.rfl
  | _, ∀¹ φ, c => (BDef.ball 3 (BDef.ball 2 ((pgB.comp ![2, 1, 6, 0]).imp
      ((hqB φ c).comp ![2, 3, 4, 5, 0])))).congr fun _ _ _ => Iff.rfl
  | _, ∃¹ φ, c => (BDef.ball 1 (((skB c).comp ![1, 2, 5, 0]).imp (BDef.ball 2
      ((pgB.comp ![2, 1, 6, 0]).imp ((hqB φ (c + 1)).comp ![2, 3, 4, 5, 0]))))).congr
      fun _ _ _ => Iff.rfl

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The number of an environment. -/
noncomputable def tup : {n : ℕ} → (Fin n → V) → V
  | 0, _ => ∅
  | _ + 1, e => pr (e 0) (tup fun i ↦ e i.succ)

/-- The witness of the quantifier number `c` in the environment number `ε`. -/
noncomputable def sk (c : ℕ) (ε : V) : V := pr (nm (c + 1)) ε

/-- The atomic sentence of the relation number `r` and of `a`, `b`. -/
noncomputable def atm (r : ℕ) (a b : V) : V := pr (nm r) (pr a b)

/-- The term for the number `j`. -/
noncomputable def dn (j : V) : V := pr ∅ j

/-- The atomic sentence of an atomic formula in an environment. -/
noncomputable def atomOf {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ Empty n)
    (e : Fin n → V) : V := atm (rcode r) (e (aL r v)) (e (aR r v))

/-- **Truth below the bound `q`** under the assignment `p`. -/
def HoldsQ (p q : V) : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ → (Fin n → V) → Prop
  | _, .rel r v, _, e => atomOf r v e ∈ q → atomOf r v e ∈ p
  | _, .nrel r v, _, e => atomOf r v e ∈ q → ¬atomOf r v e ∈ p
  | _, ⊤, _, _ => True
  | _, ⊥, _, _ => False
  | _, φ ⋏ ψ, c, e => HoldsQ p q φ c e ∧ HoldsQ p q ψ (c + cnt φ) e
  | _, φ ⋎ ψ, c, e => HoldsQ p q φ c e ∨ HoldsQ p q ψ (c + cnt φ) e
  | _, ∀¹ φ, c, e => ∀ t, t ∈ q → HoldsQ p q φ c (t :> e)
  | _, ∃¹ φ, c, e => HoldsQ p q φ (c + 1) (sk c (tup e) :> e)

/-- **Truth** under the assignment `S`. -/
def Holds (S : V) : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ → (Fin n → V) → Prop
  | _, .rel r v, _, e => atomOf r v e ∈ S
  | _, .nrel r v, _, e => ¬atomOf r v e ∈ S
  | _, ⊤, _, _ => True
  | _, ⊥, _, _ => False
  | _, φ ⋏ ψ, c, e => Holds S φ c e ∧ Holds S ψ (c + cnt φ) e
  | _, φ ⋎ ψ, c, e => Holds S φ c e ∨ Holds S ψ (c + cnt φ) e
  | _, ∀¹ φ, c, e => ∀ t, t ∈ (om : V) → Holds S φ c (t :> e)
  | _, ∃¹ φ, c, e => Holds S φ (c + 1) (sk c (tup e) :> e)

theorem tup_cons {n : ℕ} (t : V) (e : Fin n → V) : tup (t :> e) = pr t (tup e) := rfl

theorem tup_mem_om : ∀ {n : ℕ} (e : Fin n → V), (∀ i, e i ∈ (om : V)) → tup e ∈ (om : V)
  | 0, _, _ => empty_mem_om
  | _ + 1, e, he => pr_mem_om (he 0) (tup_mem_om _ fun i => he i.succ)

theorem sk_mem_om (c : ℕ) {ε : V} (hε : ε ∈ (om : V)) : sk c ε ∈ (om : V) :=
  pr_mem_om (nm_mem_om _) hε

theorem atm_mem_om (r : ℕ) {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    atm r a b ∈ (om : V) := pr_mem_om (nm_mem_om _) (pr_mem_om ha hb)

theorem dn_mem_om {j : V} (hj : j ∈ (om : V)) : dn j ∈ (om : V) := pr_mem_om empty_mem_om hj

theorem atomOf_mem_om {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ Empty n)
    {e : Fin n → V} (he : ∀ i, e i ∈ (om : V)) : atomOf r v e ∈ (om : V) :=
  atm_mem_om _ (he _) (he _)

theorem cons_mem_om {n : ℕ} {t : V} {e : Fin n → V} (ht : t ∈ (om : V))
    (he : ∀ i, e i ∈ (om : V)) : ∀ i, (t :> e) i ∈ (om : V) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ht
  | succ j => exact he j

/-- **Lowering the bound.** -/
theorem holdsQ_mono {p p' q q' : V} (hq : ∀ α, α ∈ q → α ∈ q')
    (hp : ∀ α, α ∈ q → (α ∈ p ↔ α ∈ p')) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V),
      HoldsQ p' q' φ c e → HoldsQ p q φ c e := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e h; exact h
  | hfalsum => intro c e h; exact h
  | hrel r v => intro c e h hα; exact (hp _ hα).mpr (h (hq _ hα))
  | hnrel r v => intro c e h hα h'; exact h (hq _ hα) ((hp _ hα).mp h')
  | hand φ ψ ih1 ih2 => intro c e h; exact ⟨ih1 c e h.1, ih2 _ e h.2⟩
  | hor φ ψ ih1 ih2 => intro c e h; exact h.imp (ih1 c e) (ih2 _ e)
  | hall φ ih => intro c e h t ht; exact ih c _ (h t (hq t ht))
  | hexs φ ih => intro c e h; exact ih _ _ h

theorem holdsQ_of_holds {S q : V} (hq : ∀ α, α ∈ q → α ∈ (om : V)) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V),
      Holds S φ c e → HoldsQ S q φ c e := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e h; exact h
  | hfalsum => intro c e h; exact h
  | hrel r v => intro c e h _; exact h
  | hnrel r v => intro c e h _; exact h
  | hand φ ψ ih1 ih2 => intro c e h; exact ⟨ih1 c e h.1, ih2 _ e h.2⟩
  | hor φ ψ ih1 ih2 => intro c e h; exact h.imp (ih1 c e) (ih2 _ e)
  | hall φ ih => intro c e h t ht; exact ih c _ (h t (hq t ht))
  | hexs φ ih => intro c e h; exact ih _ _ h

/-- Two numbers are included in a number. -/
theorem om_max {a b : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    ∃ m, m ∈ (om : V) ∧ (∀ z, z ∈ a → z ∈ m) ∧ ∀ z, z ∈ b → z ∈ m := by
  have hOa := ord_mem ord_om ha
  have hOb := ord_mem ord_om hb
  rcases ord_tri hOa hOb with h | h | h
  · exact ⟨b, hb, fun z hz => hOb.1 a h z hz, fun z hz => hz⟩
  · exact ⟨b, hb, fun z hz => h ▸ hz, fun z hz => hz⟩
  · exact ⟨a, ha, fun z hz => hz, fun z hz => hOa.1 b h z hz⟩

/-- **Truth is truth below all large bounds.** -/
theorem holds_of_holdsQ {S : V} :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V), (∀ i, e i ∈ (om : V)) →
      ∀ q₀, q₀ ∈ (om : V) →
        (∀ q, q ∈ (om : V) → (∀ z, z ∈ q₀ → z ∈ q) → HoldsQ S q φ c e) → Holds S φ c e := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e _ q₀ hq₀ h; exact h q₀ hq₀ fun _ hz => hz
  | hfalsum => intro c e _ q₀ hq₀ h; exact h q₀ hq₀ fun _ hz => hz
  | hrel r v =>
    intro c e he q₀ hq₀ h
    have hα := atomOf_mem_om r v he
    obtain ⟨m, hm, h1, h2⟩ := om_max hq₀ (sc_mem_om hα)
    exact h m hm h1 (h2 _ (self_mem_sc _))
  | hnrel r v =>
    intro c e he q₀ hq₀ h
    have hα := atomOf_mem_om r v he
    obtain ⟨m, hm, h1, h2⟩ := om_max hq₀ (sc_mem_om hα)
    exact h m hm h1 (h2 _ (self_mem_sc _))
  | hand φ ψ ih1 ih2 =>
    intro c e he q₀ hq₀ h
    exact ⟨ih1 c e he q₀ hq₀ fun q hq hs => (h q hq hs).1,
      ih2 _ e he q₀ hq₀ fun q hq hs => (h q hq hs).2⟩
  | hor φ ψ ih1 ih2 =>
    intro c e he q₀ hq₀ h
    by_cases h1 : ∀ q, q ∈ (om : V) → (∀ z, z ∈ q₀ → z ∈ q) → HoldsQ S q φ c e
    · exact Or.inl (ih1 c e he q₀ hq₀ h1)
    · refine Or.inr ?_
      simp only [not_forall] at h1
      obtain ⟨q₁, hq₁, hs₁, hn⟩ := h1
      refine ih2 _ e he q₁ hq₁ fun q hq hs => ?_
      rcases h q hq (fun z hz => hs z (hs₁ z hz)) with h' | h'
      · exact absurd (holdsQ_mono hs (fun _ _ => Iff.rfl) φ c e h') hn
      · exact h'
  | hall φ ih =>
    intro c e he q₀ hq₀ h t ht
    obtain ⟨m, hm, h1, h2⟩ := om_max hq₀ (sc_mem_om ht)
    refine ih c _ (cons_mem_om ht he) m hm fun q hq hs => ?_
    exact h q hq (fun z hz => hs z (h1 z hz)) t (hs t (h2 t (self_mem_sc t)))
  | hexs φ ih =>
    intro c e he q₀ hq₀ h
    exact ih _ _ (cons_mem_om (sk_mem_om c (tup_mem_om e he)) he) q₀ hq₀ h

/-! ### The bounded formula and truth below a bound -/

section bridge

variable {P : V} (hP : CanP P)

include hP

theorem look_iff : ∀ {n : ℕ} (e : Fin n → V), (∀ i, e i ∈ (om : V)) → ∀ (i : Fin n) (x : V),
    LookR P (om : V) i (tup e) x ↔ x = e i
  | 0, _, _, i, _ => i.elim0
  | n + 1, e, he, i, x => by
    have htl : tup (fun i ↦ e i.succ) ∈ (om : V) := tup_mem_om _ fun i => he i.succ
    cases i using Fin.cases with
    | zero =>
      show (∃ ε', ε' ∈ (om : V) ∧ PG P x ε' (pr (e 0) (tup fun i ↦ e i.succ))) ↔ x = e 0
      constructor
      · rintro ⟨ε', -, h⟩
        obtain ⟨hx, hε', h⟩ := (canP_pg hP).mp h
        exact ((pr_inj (he 0) htl hx hε' h).1).symm
      · rintro rfl
        exact ⟨_, htl, (canP_pg hP).mpr ⟨he 0, htl, rfl⟩⟩
    | succ j =>
      show (∃ y, y ∈ (om : V) ∧ ∃ ε', ε' ∈ (om : V) ∧
        (PG P y ε' (pr (e 0) (tup fun i ↦ e i.succ)) ∧ LookR P (om : V) j ε' x)) ↔ x = e j.succ
      constructor
      · rintro ⟨y, -, ε', -, h, hl⟩
        obtain ⟨hy, hε', h⟩ := (canP_pg hP).mp h
        obtain ⟨-, e2⟩ := pr_inj (he 0) htl hy hε' h
        rw [← e2] at hl
        exact (look_iff (fun i ↦ e i.succ) (fun i => he i.succ) j x).mp hl
      · rintro rfl
        exact ⟨_, he 0, _, htl, (canP_pg hP).mpr ⟨he 0, htl, rfl⟩,
          (look_iff (fun i ↦ e i.succ) (fun i => he i.succ) j _).mpr rfl⟩

theorem atomR_iff (r : ℕ) {a b α : V} (ha : a ∈ (om : V)) (hb : b ∈ (om : V)) :
    AtomR P (om : V) r a b α ↔ α = atm r a b := by
  constructor
  · rintro ⟨w, -, hw, z, -, hz, hα⟩
    obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hw
    obtain rfl := (isNum_iff r z).mp hz
    exact ((canP_pg hP).mp hα).2.2
  · rintro rfl
    exact ⟨_, pr_mem_om ha hb, (canP_pg hP).mpr ⟨ha, hb, rfl⟩, _, nm_mem_om r, isNum_nm r,
      (canP_pg hP).mpr ⟨nm_mem_om r, pr_mem_om ha hb, rfl⟩⟩

theorem skR_iff (c : ℕ) {ε w : V} (hε : ε ∈ (om : V)) :
    SkR P (om : V) c ε w ↔ w = sk c ε := by
  constructor
  · rintro ⟨z, -, hz, hw⟩
    obtain rfl := (isNum_iff _ z).mp hz
    exact ((canP_pg hP).mp hw).2.2
  · rintro rfl
    exact ⟨_, nm_mem_om _, isNum_nm _, (canP_pg hP).mpr ⟨nm_mem_om _, hε, rfl⟩⟩

/-- **The bounded formula is truth below the bound.** -/
theorem hq_iff {p q : V} (hq : ∀ α, α ∈ q → α ∈ (om : V)) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V), (∀ i, e i ∈ (om : V)) →
      (HQ P (om : V) p q φ c (tup e) ↔ HoldsQ p q φ c e) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e _; exact Iff.rfl
  | hfalsum => intro c e _; exact Iff.rfl
  | hrel r v =>
    intro c e he
    constructor
    · intro h hα
      exact h _ (he _) _ (he _) ((look_iff hP e he _ _).mpr rfl) ((look_iff hP e he _ _).mpr rfl)
        _ hα ((atomR_iff hP _ (he _) (he _)).mpr rfl)
    · intro h a _ b _ ha hb α hα hat
      obtain rfl := (look_iff hP e he _ _).mp ha
      obtain rfl := (look_iff hP e he _ _).mp hb
      obtain rfl := (atomR_iff hP _ (he _) (he _)).mp hat
      exact h hα
  | hnrel r v =>
    intro c e he
    constructor
    · intro h hα
      exact h _ (he _) _ (he _) ((look_iff hP e he _ _).mpr rfl) ((look_iff hP e he _ _).mpr rfl)
        _ hα ((atomR_iff hP _ (he _) (he _)).mpr rfl)
    · intro h a _ b _ ha hb α hα hat
      obtain rfl := (look_iff hP e he _ _).mp ha
      obtain rfl := (look_iff hP e he _ _).mp hb
      obtain rfl := (atomR_iff hP _ (he _) (he _)).mp hat
      exact h hα
  | hand φ ψ ih1 ih2 => intro c e he; exact and_congr (ih1 c e he) (ih2 _ e he)
  | hor φ ψ ih1 ih2 => intro c e he; exact or_congr (ih1 c e he) (ih2 _ e he)
  | hall φ ih =>
    intro c e he
    have hε := tup_mem_om e he
    constructor
    · intro h t ht
      have ht' := hq t ht
      exact (ih c _ (cons_mem_om ht' he)).mp
        (h t ht _ (pr_mem_om ht' hε) ((canP_pg hP).mpr ⟨ht', hε, rfl⟩))
    · intro h t ht ε' _ hpg
      have ht' := hq t ht
      obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hpg
      exact (ih c _ (cons_mem_om ht' he)).mpr (h t ht)
  | hexs φ ih =>
    intro c e he
    have hε := tup_mem_om e he
    have hw := sk_mem_om c hε
    constructor
    · intro h
      exact (ih _ _ (cons_mem_om hw he)).mp
        (h _ hw ((skR_iff hP c hε).mpr rfl) _ (pr_mem_om hw hε) ((canP_pg hP).mpr ⟨hw, hε, rfl⟩))
    · intro h w _ hsk ε' _ hpg
      obtain rfl := (skR_iff hP c hε).mp hsk
      obtain ⟨-, -, rfl⟩ := (canP_pg hP).mp hpg
      exact (ih _ _ (cons_mem_om hw he)).mpr h

end bridge

end model

end MH

end FFL.FirstOrder.SetTheory
