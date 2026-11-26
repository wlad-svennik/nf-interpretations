module

public import CutFml
public import MDefs

@[expose] public section

set_option autoImplicit false

/-!
# The formulas of the two-sorted language, as formulas of `ℒₛₑₜ`

A formula of `L₂` (`BFml`) is translated into a formula of `ℒₛₑₜ`, given formulas of `ℒₛₑₜ` for
its atoms (`Ops`): "is in the domain", "is a number", "is in the cut", the graphs of addition
and multiplication, membership, and the numerals. Number quantifiers are relativised to the
numbers and set quantifiers to the domain; a term is replaced by a formula for its graph
(`grT`).

* `bholdsR mem cut`: the meaning of a formula of `L₂` in a structure of numbers and sets, for
  any membership relation and any cut (`CutSys.bholds` is the case of a `CutSys`).
* `Spec`: what the formulas for the atoms have to mean, for numbers and sets coded by elements
  of a structure `M` for `ℒₛₑₜ`.
* **`eval_trM`**: then the translation of a formula holds in `M` exactly when the formula
  holds.
-/

open NFUCut

section bholdsR

variable {N W : Type} [CommSemiring N] [PartialOrder N]

/-- Truth of a formula of `L₂`, for a membership relation and a cut. -/
def bholdsR (mem : N → W → Prop) (cut : N → Prop) : BFml → (ℕ → N) → (ℕ → W) → Prop
  | .eq s t, e, _ => evalG s e = evalG t e
  | .le s t, e, _ => evalG s e ≤ evalG t e
  | .mem t X, e, s => mem (evalG t e) (s X)
  | .inKt t, e, _ => cut (evalG t e)
  | .neg φ, e, s => ¬ bholdsR mem cut φ e s
  | .and φ ψ, e, s => bholdsR mem cut φ e s ∧ bholdsR mem cut ψ e s
  | .all x φ, e, s => ∀ a : N, bholdsR mem cut φ (Function.update e x a) s
  | .allS X φ, e, s => ∀ A : W, bholdsR mem cut φ e (Function.update s X A)

theorem bholdsR_imp {mem : N → W → Prop} {cut : N → Prop} {φ ψ : BFml} {e : ℕ → N}
    {s : ℕ → W} :
    bholdsR mem cut (φ.imp ψ) e s ↔ (bholdsR mem cut φ e s → bholdsR mem cut ψ e s) := by
  simp only [BFml.imp, bholdsR]
  tauto

end bholdsR

theorem CutSys.bholds_iff_bholdsR {N W : Type} [CommSemiring N] [PartialOrder N]
    [IsOrderedRing N] [CanonicallyOrderedAdd N] (C : CutSys N W) (φ : BFml) :
    ∀ (e : ℕ → N) (s : ℕ → W), C.bholds φ e s ↔ bholdsR C.mem C.cut φ e s := by
  induction φ with
  | eq s t => exact fun _ _ => Iff.rfl
  | le s t => exact fun _ _ => Iff.rfl
  | mem t X => exact fun _ _ => Iff.rfl
  | inKt t => exact fun _ _ => Iff.rfl
  | neg φ ih => exact fun e s => not_congr (ih e s)
  | and φ ψ ih1 ih2 => exact fun e s => and_congr (ih1 e s) (ih2 e s)
  | all x φ ih => exact fun e s => forall_congr' fun a => ih _ s
  | allS X φ ih => exact fun e s => forall_congr' fun A => ih e _

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-- **The formulas of `ℒₛₑₜ` for the atoms of `L₂`.** -/
structure Ops where
  /-- "is in the domain" -/
  dom : Semisentence ℒₛₑₜ 1
  /-- "is a number", for the members of the domain -/
  num : Semisentence ℒₛₑₜ 1
  /-- "is in the cut", for the numbers -/
  cut : Semisentence ℒₛₑₜ 1
  /-- the graph of addition -/
  add : Semisentence ℒₛₑₜ 3
  /-- the graph of multiplication -/
  mul : Semisentence ℒₛₑₜ 3
  /-- membership -/
  mem : Semisentence ℒₛₑₜ 2
  /-- "is the numeral `k`" -/
  numl : ℕ → Semisentence ℒₛₑₜ 1

/-! ### The translation -/

section syn

/-- A formula with its variables replaced by terms. -/
def app {k n : ℕ} (o : Semisentence ℒₛₑₜ k) (v : Fin k → Semiterm ℒₛₑₜ Empty n) :
    Semiformula ℒₛₑₜ Empty n := Rew.subst v ▹ o

/-- A term under one more quantifier. -/
def sh {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) : Semiterm ℒₛₑₜ Empty (n + 1) := Rew.bShift t

/-- Equality of two terms. -/
def eqF {n : ℕ} (t u : Semiterm ℒₛₑₜ Empty n) : Semiformula ℒₛₑₜ Empty n :=
  Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![t, u]

/-- "`out` is the value of the number term", where `c` gives the terms for the variables. -/
def grT (O : Ops) : BTm → (n : ℕ) → (ℕ → Semiterm ℒₛₑₜ Empty n) → Semiterm ℒₛₑₜ Empty n →
    Semiformula ℒₛₑₜ Empty n
  | .var i, _, c, out => eqF out (c i)
  | .zero, _, _, out => app O.dom ![out] ⋏ app (O.numl 0) ![out]
  | .one, _, _, out => app O.dom ![out] ⋏ app (O.numl 1) ![out]
  | .«lit» k, _, _, out => app O.dom ![out] ⋏ app (O.numl k) ![out]
  | .add s t, n, c, out => app O.dom ![out] ⋏
      (∃¹ (∃¹ (grT O s (n + 2) (fun i => sh (sh (c i))) #1 ⋏
        (grT O t (n + 2) (fun i => sh (sh (c i))) #0 ⋏ app O.add ![#1, #0, sh (sh out)]))))
  | .mul s t, n, c, out => app O.dom ![out] ⋏
      (∃¹ (∃¹ (grT O s (n + 2) (fun i => sh (sh (c i))) #1 ⋏
        (grT O t (n + 2) (fun i => sh (sh (c i))) #0 ⋏ app O.mul ![#1, #0, sh (sh out)]))))

/-- **The translation of a formula of `L₂`**, where `cN` and `cS` give the terms for the
number variables and for the set variables. -/
def trM (O : Ops) : BFml → (n : ℕ) → (ℕ → Semiterm ℒₛₑₜ Empty n) →
    (ℕ → Semiterm ℒₛₑₜ Empty n) → Semiformula ℒₛₑₜ Empty n
  | .eq s t, n, cN, _ => ∃¹ (grT O s (n + 1) (fun i => sh (cN i)) #0 ⋏
      grT O t (n + 1) (fun i => sh (cN i)) #0)
  | .le s t, n, cN, _ => ∃¹ (∃¹ (grT O s (n + 2) (fun i => sh (sh (cN i))) #1 ⋏
      (grT O t (n + 2) (fun i => sh (sh (cN i))) #0 ⋏ (app O.mem ![#1, #0] ⋎ eqF #1 #0))))
  | .mem t X, n, cN, cS => ∃¹ (grT O t (n + 1) (fun i => sh (cN i)) #0 ⋏
      app O.mem ![#0, sh (cS X)])
  | .inKt t, n, cN, _ => ∃¹ (grT O t (n + 1) (fun i => sh (cN i)) #0 ⋏ app O.cut ![#0])
  | .neg φ, n, cN, cS => ∼ trM O φ n cN cS
  | .and φ ψ, n, cN, cS => trM O φ n cN cS ⋏ trM O ψ n cN cS
  | .all x φ, n, cN, cS => ∀¹ ((app O.dom ![#0] ⋏ app O.num ![#0]) 🡒
      trM O φ (n + 1) (Function.update (fun i => sh (cN i)) x #0) (fun i => sh (cS i)))
  | .allS X φ, n, cN, cS => ∀¹ (app O.dom ![#0] 🡒
      trM O φ (n + 1) (fun i => sh (cN i)) (Function.update (fun i => sh (cS i)) X #0))

end syn

/-! ### The meaning of the translation -/

section sem

variable {M : Type} [SetStructure M]

theorem eval_app {k n : ℕ} (o : Semisentence ℒₛₑₜ k) (v : Fin k → Semiterm ℒₛₑₜ Empty n)
    (e : Fin n → M) : M ⊧/e (app o v) ↔ M ⊧/(fun i => (v i).val e Empty.elim) o := by
  unfold app
  simp only [eval_substs]
  rfl

theorem eval_app1 {n : ℕ} (o : Semisentence ℒₛₑₜ 1) (t : Semiterm ℒₛₑₜ Empty n)
    (e : Fin n → M) : M ⊧/e (app o ![t]) ↔ M ⊧/![t.val e Empty.elim] o := by
  rw [eval_app]
  have : (fun i => ((![t] : Fin 1 → Semiterm ℒₛₑₜ Empty n) i).val e Empty.elim) =
      ![t.val e Empty.elim] := by
    funext i
    fin_cases i
    rfl
  rw [this]

theorem eval_app2 {n : ℕ} (o : Semisentence ℒₛₑₜ 2) (t u : Semiterm ℒₛₑₜ Empty n)
    (e : Fin n → M) :
    M ⊧/e (app o ![t, u]) ↔ M ⊧/![t.val e Empty.elim, u.val e Empty.elim] o := by
  rw [eval_app]
  have : (fun i => ((![t, u] : Fin 2 → Semiterm ℒₛₑₜ Empty n) i).val e Empty.elim) =
      ![t.val e Empty.elim, u.val e Empty.elim] := by
    funext i
    fin_cases i <;> rfl
  rw [this]

theorem eval_app3 {n : ℕ} (o : Semisentence ℒₛₑₜ 3) (t u w : Semiterm ℒₛₑₜ Empty n)
    (e : Fin n → M) :
    M ⊧/e (app o ![t, u, w]) ↔
      M ⊧/![t.val e Empty.elim, u.val e Empty.elim, w.val e Empty.elim] o := by
  rw [eval_app]
  have : (fun i => ((![t, u, w] : Fin 3 → Semiterm ℒₛₑₜ Empty n) i).val e Empty.elim) =
      ![t.val e Empty.elim, u.val e Empty.elim, w.val e Empty.elim] := by
    funext i
    fin_cases i <;> rfl
  rw [this]

theorem eval_eqF {n : ℕ} (t u : Semiterm ℒₛₑₜ Empty n) (e : Fin n → M) :
    M ⊧/e (eqF t u) ↔ t.val e Empty.elim = u.val e Empty.elim := Iff.rfl

theorem val_sh {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) (x : M) (e : Fin n → M) :
    (sh t).val (x :> e) Empty.elim = t.val e Empty.elim := by
  unfold sh
  rw [Semiterm.val_bShift]

variable {N W : Type} [CommSemiring N] [PartialOrder N]

/-- **What the formulas for the atoms mean**, when the number `a` is coded by `enc a` and the
set `w` by `encS w`. -/
structure Spec (O : Ops) (mem : N → W → Prop) (enc : N → M) (encS : W → M) : Prop where
  inj : Function.Injective enc
  num : ∀ x : M, (M ⊧/![x] O.dom ∧ M ⊧/![x] O.num) ↔ ∃ a : N, x = enc a
  set : ∀ x : M, M ⊧/![x] O.dom ↔ ∃ w : W, x = encS w
  mem : ∀ (a : N) (w : W), M ⊧/![enc a, encS w] O.mem ↔ mem a w
  le : ∀ a b : N, (M ⊧/![enc a, enc b] O.mem ∨ enc a = enc b) ↔ a ≤ b
  numl : ∀ (k : ℕ) (x : M), (M ⊧/![x] O.dom ∧ M ⊧/![x] (O.numl k)) ↔ x = enc (k : N)
  add : ∀ (p q : N) (z : M), (M ⊧/![z] O.dom ∧ M ⊧/![enc p, enc q, z] O.add) ↔ z = enc (p + q)
  mul : ∀ (p q : N) (z : M), (M ⊧/![z] O.dom ∧ M ⊧/![enc p, enc q, z] O.mul) ↔ z = enc (p * q)

variable {O : Ops} {mem : N → W → Prop} {enc : N → M} {encS : W → M}

/-- The formula for the graph of a term defines the value of the term. -/
theorem eval_grT (sp : Spec O mem enc encS) (t : BTm) :
    ∀ (n : ℕ) (c : ℕ → Semiterm ℒₛₑₜ Empty n) (out : Semiterm ℒₛₑₜ Empty n) (e : Fin n → M)
      (a : ℕ → N), (∀ i, (c i).val e Empty.elim = enc (a i)) →
      (M ⊧/e (grT O t n c out) ↔ out.val e Empty.elim = enc (evalG t a)) := by
  induction t with
  | var i =>
    intro n c out e a hc
    simp only [grT, evalG]
    rw [eval_eqF, hc]
  | zero =>
    intro n c out e a hc
    simp only [grT, evalG]
    have h := sp.numl 0 (out.val e Empty.elim)
    rw [Nat.cast_zero] at h
    rw [← h, ← eval_app1, ← eval_app1]
    simp
  | one =>
    intro n c out e a hc
    simp only [grT, evalG]
    have h := sp.numl 1 (out.val e Empty.elim)
    rw [Nat.cast_one] at h
    rw [← h, ← eval_app1, ← eval_app1]
    simp
  | «lit» k =>
    intro n c out e a hc
    simp only [grT, evalG]
    rw [← sp.numl k (out.val e Empty.elim), ← eval_app1, ← eval_app1]
    simp
  | add s t ihs iht =>
    intro n c out e a hc
    have hc2 : ∀ (x y : M) (i : ℕ), (sh (sh (c i))).val (y :> x :> e) Empty.elim = enc (a i) :=
      fun x y i => by rw [val_sh, val_sh, hc]
    have key : M ⊧/e (grT O (.add s t) n c out) ↔
        M ⊧/![out.val e Empty.elim] O.dom ∧ ∃ x y : M, x = enc (evalG s a) ∧
          (y = enc (evalG t a) ∧ M ⊧/![x, y, out.val e Empty.elim] O.add) := by
      simp only [grT]
      have h1 : ∀ x y : M, M ⊧/(y :> x :> e)
          (grT O s (n + 2) (fun i => sh (sh (c i))) #1) ↔ x = enc (evalG s a) :=
        fun x y => ihs (n + 2) _ #1 (y :> x :> e) a (hc2 x y)
      have h2 : ∀ x y : M, M ⊧/(y :> x :> e)
          (grT O t (n + 2) (fun i => sh (sh (c i))) #0) ↔ y = enc (evalG t a) :=
        fun x y => iht (n + 2) _ #0 (y :> x :> e) a (hc2 x y)
      have h3 : ∀ x y : M, M ⊧/(y :> x :> e) (app O.add ![#1, #0, sh (sh out)]) ↔
          M ⊧/![x, y, out.val e Empty.elim] O.add := fun x y => by
        rw [eval_app3, val_sh, val_sh]
        rfl
      simp [eval_app1, h1, h2, h3]
    rw [key]
    simp only [evalG]
    rw [← sp.add]
    constructor
    · rintro ⟨hd, x, y, rfl, rfl, h⟩
      exact ⟨hd, h⟩
    · rintro ⟨hd, h⟩
      exact ⟨hd, _, _, rfl, rfl, h⟩
  | mul s t ihs iht =>
    intro n c out e a hc
    have hc2 : ∀ (x y : M) (i : ℕ), (sh (sh (c i))).val (y :> x :> e) Empty.elim = enc (a i) :=
      fun x y i => by rw [val_sh, val_sh, hc]
    have key : M ⊧/e (grT O (.mul s t) n c out) ↔
        M ⊧/![out.val e Empty.elim] O.dom ∧ ∃ x y : M, x = enc (evalG s a) ∧
          (y = enc (evalG t a) ∧ M ⊧/![x, y, out.val e Empty.elim] O.mul) := by
      simp only [grT]
      have h1 : ∀ x y : M, M ⊧/(y :> x :> e)
          (grT O s (n + 2) (fun i => sh (sh (c i))) #1) ↔ x = enc (evalG s a) :=
        fun x y => ihs (n + 2) _ #1 (y :> x :> e) a (hc2 x y)
      have h2 : ∀ x y : M, M ⊧/(y :> x :> e)
          (grT O t (n + 2) (fun i => sh (sh (c i))) #0) ↔ y = enc (evalG t a) :=
        fun x y => iht (n + 2) _ #0 (y :> x :> e) a (hc2 x y)
      have h3 : ∀ x y : M, M ⊧/(y :> x :> e) (app O.mul ![#1, #0, sh (sh out)]) ↔
          M ⊧/![x, y, out.val e Empty.elim] O.mul := fun x y => by
        rw [eval_app3, val_sh, val_sh]
        rfl
      simp [eval_app1, h1, h2, h3]
    rw [key]
    simp only [evalG]
    rw [← sp.mul]
    constructor
    · rintro ⟨hd, x, y, rfl, rfl, h⟩
      exact ⟨hd, h⟩
    · rintro ⟨hd, h⟩
      exact ⟨hd, _, _, rfl, rfl, h⟩

/-- **The translation of a formula of `L₂` holds exactly when the formula holds.** -/
theorem eval_trM (sp : Spec O mem enc encS) {cut : N → Prop}
    (hcut : ∀ a : N, M ⊧/![enc a] O.cut ↔ cut a) (φ : BFml) :
    ∀ (n : ℕ) (cN cS : ℕ → Semiterm ℒₛₑₜ Empty n) (e : Fin n → M) (a : ℕ → N) (s : ℕ → W),
      (∀ i, (cN i).val e Empty.elim = enc (a i)) →
      (∀ X, (cS X).val e Empty.elim = encS (s X)) →
      (M ⊧/e (trM O φ n cN cS) ↔ bholdsR mem cut φ a s) := by
  induction φ with
  | eq t u =>
    intro n cN cS e a s hN hS
    have h1 : ∀ x : M, M ⊧/(x :> e) (grT O t (n + 1) (fun i => sh (cN i)) #0) ↔
        x = enc (evalG t a) := fun x =>
      eval_grT sp t (n + 1) _ #0 (x :> e) a (fun i => by rw [val_sh, hN])
    have h2 : ∀ x : M, M ⊧/(x :> e) (grT O u (n + 1) (fun i => sh (cN i)) #0) ↔
        x = enc (evalG u a) := fun x =>
      eval_grT sp u (n + 1) _ #0 (x :> e) a (fun i => by rw [val_sh, hN])
    simp only [trM, bholdsR]
    simp only [eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, h1,
      h2]
    constructor
    · rintro ⟨x, rfl, h⟩
      exact sp.inj h
    · intro h
      exact ⟨_, rfl, congrArg enc h⟩
  | le t u =>
    intro n cN cS e a s hN hS
    have h1 : ∀ x y : M, M ⊧/(y :> x :> e)
        (grT O t (n + 2) (fun i => sh (sh (cN i))) #1) ↔ x = enc (evalG t a) := fun x y =>
      eval_grT sp t (n + 2) _ #1 (y :> x :> e) a (fun i => by rw [val_sh, val_sh, hN])
    have h2 : ∀ x y : M, M ⊧/(y :> x :> e)
        (grT O u (n + 2) (fun i => sh (sh (cN i))) #0) ↔ y = enc (evalG u a) := fun x y =>
      eval_grT sp u (n + 2) _ #0 (y :> x :> e) a (fun i => by rw [val_sh, val_sh, hN])
    have h3 : ∀ x y : M, M ⊧/(y :> x :> e) (app O.mem ![#1, #0]) ↔ M ⊧/![x, y] O.mem :=
      fun x y => by
        rw [eval_app2]
        rfl
    have h4 : ∀ x y : M, M ⊧/(y :> x :> e) (eqF #1 #0) ↔ x = y := fun x y => by
      rw [eval_eqF]
      rfl
    simp only [trM, bholdsR]
    simp only [eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, h1, h2, h3, h4]
    rw [← sp.le]
    constructor
    · rintro ⟨x, y, rfl, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩
  | mem t X =>
    intro n cN cS e a s hN hS
    have h1 : ∀ x : M, M ⊧/(x :> e) (grT O t (n + 1) (fun i => sh (cN i)) #0) ↔
        x = enc (evalG t a) := fun x =>
      eval_grT sp t (n + 1) _ #0 (x :> e) a (fun i => by rw [val_sh, hN])
    have h2 : ∀ x : M, M ⊧/(x :> e) (app O.mem ![#0, sh (cS X)]) ↔
        M ⊧/![x, encS (s X)] O.mem := fun x => by
      rw [eval_app2, val_sh, hS]
      rfl
    simp only [trM, bholdsR]
    simp only [eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, h1,
      h2]
    rw [← sp.mem]
    constructor
    · rintro ⟨x, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, rfl, h⟩
  | inKt t =>
    intro n cN cS e a s hN hS
    have h1 : ∀ x : M, M ⊧/(x :> e) (grT O t (n + 1) (fun i => sh (cN i)) #0) ↔
        x = enc (evalG t a) := fun x =>
      eval_grT sp t (n + 1) _ #0 (x :> e) a (fun i => by rw [val_sh, hN])
    have h2 : ∀ x : M, M ⊧/(x :> e) (app O.cut ![#0]) ↔ M ⊧/![x] O.cut := fun x => by
      rw [eval_app1]
      rfl
    simp only [trM, bholdsR]
    simp only [eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, h1,
      h2]
    rw [← hcut]
    constructor
    · rintro ⟨x, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, rfl, h⟩
  | neg φ ih =>
    intro n cN cS e a s hN hS
    simp only [trM, bholdsR]
    rw [← ih n cN cS e a s hN hS]
    simp
  | and φ ψ ih1 ih2 =>
    intro n cN cS e a s hN hS
    simp only [trM, bholdsR]
    rw [← ih1 n cN cS e a s hN hS, ← ih2 n cN cS e a s hN hS]
    simp
  | all x φ ih =>
    intro n cN cS e a s hN hS
    have hd : ∀ m : M, M ⊧/(m :> e) (app O.dom ![#0] ⋏ app O.num ![#0]) ↔
        ∃ b : N, m = enc b := fun m => by
      rw [← sp.num m]
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, eval_app1]
      rfl
    have hb : ∀ (m : M) (b : N), m = enc b →
        (M ⊧/(m :> e) (trM O φ (n + 1) (Function.update (fun i => sh (cN i)) x #0)
          (fun i => sh (cS i))) ↔ bholdsR mem cut φ (Function.update a x b) s) :=
      fun m b hm => ih (n + 1) _ _ (m :> e) (Function.update a x b) s
        (fun i => by
          by_cases hi : i = x
          · subst hi
            rw [Function.update_self, Function.update_self]
            exact hm
          · rw [Function.update_of_ne hi, Function.update_of_ne hi, val_sh, hN])
        (fun X => by rw [val_sh, hS])
    simp only [trM, bholdsR]
    simp only [eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    constructor
    · intro h b
      exact (hb (enc b) b rfl).mp (h (enc b) ((hd _).mpr ⟨b, rfl⟩))
    · intro h m hm
      obtain ⟨b, rfl⟩ := (hd m).mp hm
      exact (hb _ b rfl).mpr (h b)
  | allS X φ ih =>
    intro n cN cS e a s hN hS
    have hd : ∀ m : M, M ⊧/(m :> e) (app O.dom ![#0]) ↔ ∃ w : W, m = encS w := fun m => by
      rw [← sp.set m, eval_app1]
      rfl
    have hb : ∀ (m : M) (w : W), m = encS w →
        (M ⊧/(m :> e) (trM O φ (n + 1) (fun i => sh (cN i))
          (Function.update (fun i => sh (cS i)) X #0)) ↔
          bholdsR mem cut φ a (Function.update s X w)) :=
      fun m w hm => ih (n + 1) _ _ (m :> e) a (Function.update s X w)
        (fun i => by rw [val_sh, hN])
        (fun Y => by
          by_cases hY : Y = X
          · subst hY
            rw [Function.update_self, Function.update_self]
            exact hm
          · rw [Function.update_of_ne hY, Function.update_of_ne hY, val_sh, hS])
    simp only [trM, bholdsR]
    simp only [eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    constructor
    · intro h w
      exact (hb (encS w) w rfl).mp (h (encS w) ((hd _).mpr ⟨w, rfl⟩))
    · intro h m hm
      obtain ⟨w, rfl⟩ := (hd m).mp hm
      exact (hb _ w rfl).mpr (h w)

end sem

end FFL.FirstOrder.SetTheory
