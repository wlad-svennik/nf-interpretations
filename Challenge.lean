module

public import Mathlib.Data.List.Basic

/-!
# NF and NF + AxCount: models and uniform mutual interpretations

This Challenge reproduces the statement and its complete mathematical definition
closure from the uploaded `nf-interp` development. The names, types, and definition
bodies agree with the source. Only proof bodies are omitted. In particular, the
six elementary existence lemmas below specify the witnesses used by the original
choice-defined finite cardinals; they are proved from comprehension in the Solution.

No formalization-specific library is imported into this statement. The final two
theorems spell out the AxCount interpretations using Jensen NFU semantics.
-/

set_option autoImplicit false

@[expose] public section

namespace ConNF.NF

/-- Membership-and-equality formulas; bound variables use de Bruijn indices. -/
inductive Fm : Type
  | mem (i j : ℕ) : Fm
  | eq (i j : ℕ) : Fm
  | neg (φ : Fm) : Fm
  | and (φ ψ : Fm) : Fm
  | all (t : ℕ) (φ : Fm) : Fm

/-- Quantifier type annotations affect stratification, not satisfaction. -/
def Sat {V : Type} (mem : V → V → Prop) : Fm → List V → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ mem a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬Sat mem φ env
  | .and φ ψ, env => Sat mem φ env ∧ Sat mem ψ env
  | .all _ φ, env => ∀ a, Sat mem φ (a :: env)

/-- Membership raises type by one; equality preserves type. -/
def Strat : List ℕ → Fm → Prop
  | Γ, .mem i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some (t + 1)
  | Γ, .eq i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some t
  | Γ, .neg φ => Strat Γ φ
  | Γ, .and φ ψ => Strat Γ φ ∧ Strat Γ ψ
  | Γ, .all t φ => Strat (t :: Γ) φ

/-- NF consists of extensionality and every stratified comprehension instance. -/
structure IsNF (V : Type) (mem : V → V → Prop) : Prop where
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  comprehension : ∀ (t : ℕ) (Γ : List ℕ) (φ : Fm), Strat (t :: Γ) φ →
    ∀ params : List V, params.length = Γ.length → ∃ y, ∀ x, mem x y ↔ Sat mem φ (x :: params)

end ConNF.NF

namespace NFUCut

/-- NFU formulas have named variables and a predicate for sethood. -/
inductive Fml : Type
  | mem (x y : ℕ) : Fml
  | eq (x y : ℕ) : Fml
  | set (x : ℕ) : Fml
  | neg (φ : Fml) : Fml
  | and (φ ψ : Fml) : Fml
  | all (x : ℕ) (φ : Fml) : Fml

namespace Fml

def strat (σ : ℕ → ℕ) : Fml → Bool
  | mem x y => σ y == σ x + 1
  | eq x y => σ x == σ y
  | set _ => true
  | neg φ => strat σ φ
  | and φ ψ => strat σ φ && strat σ ψ
  | all _ φ => strat σ φ

end Fml

variable {V : Type}

def Sat (mem : V → V → Prop) (isSet : V → Prop) : Fml → (ℕ → V) → Prop
  | .mem x y, ρ => mem (ρ x) (ρ y)
  | .eq x y, ρ => ρ x = ρ y
  | .set x, ρ => isSet (ρ x)
  | .neg φ, ρ => ¬ Sat mem isSet φ ρ
  | .and φ ψ, ρ => Sat mem isSet φ ρ ∧ Sat mem isSet ψ ρ
  | .all x φ, ρ => ∀ a, Sat mem isSet φ (Function.update ρ x a)

/-- NFU: extensionality for sets and stratified comprehension, without Choice. -/
structure Model (V : Type) where
  mem : V → V → Prop
  isSet : V → Prop
  isSet_of_mem : ∀ {x y : V}, mem x y → isSet y
  ext : ∀ {x y : V}, isSet x → isSet y → (∀ z, mem z x ↔ mem z y) → x = y
  comp : ∀ (σ : ℕ → ℕ) (φ : Fml) (x : ℕ), φ.strat σ = true → ∀ ρ : ℕ → V,
    ∃ y, isSet y ∧ ∀ a, mem a y ↔ Sat mem isSet φ (Function.update ρ x a)

namespace Model

theorem exists_emp [Nonempty V] (M : Model V) :
    ∃ e, M.isSet e ∧ ∀ a, ¬ M.mem a e := by sorry

noncomputable def emp [Nonempty V] (M : Model V) : V := Classical.choose M.exists_emp

theorem exists_sing [Nonempty V] (M : Model V) (a : V) :
    ∃ u, M.isSet u ∧ ∀ c, M.mem c u ↔ c = a := by sorry

noncomputable def sing [Nonempty V] (M : Model V) (a : V) : V :=
  Classical.choose (M.exists_sing a)

theorem exists_adj [Nonempty V] (M : Model V) (x b : V) :
    ∃ y, M.isSet y ∧ ∀ c, M.mem c y ↔ M.mem c x ∨ c = b := by sorry

noncomputable def adj [Nonempty V] (M : Model V) (x b : V) : V :=
  Classical.choose (M.exists_adj x b)

/-- Zero is the Frege cardinal `{∅}`. -/
noncomputable def zero [Nonempty V] (M : Model V) : V := M.sing M.emp

theorem exists_succ [Nonempty V] (M : Model V) (k : V) :
    ∃ s, M.isSet s ∧ ∀ y, M.mem y s ↔
      ∃ x b, M.mem x k ∧ ¬ M.mem b x ∧ y = M.adj x b := by sorry

/-- Successor adjoins one new element to a representative of a cardinal. -/
noncomputable def succ [Nonempty V] (M : Model V) (k : V) : V :=
  Classical.choose (M.exists_succ k)

theorem exists_nat [Nonempty V] (M : Model V) :
    ∃ N, M.isSet N ∧ ∀ n, M.mem n N ↔
      ∀ I, (M.mem M.zero I ∧ ∀ k, M.mem k I → M.mem (M.succ k) I) → M.mem n I := by sorry

/-- The natural cardinals form the least inductive set. -/
noncomputable def nat [Nonempty V] (M : Model V) : V := Classical.choose M.exists_nat

theorem exists_univ [Nonempty V] (M : Model V) :
    ∃ u, M.isSet u ∧ ∀ a, M.mem a u := by sorry

noncomputable def univ [Nonempty V] (M : Model V) : V := Classical.choose M.exists_univ

/-- Infinity says that the universe belongs to no natural cardinal. -/
def Infinity [Nonempty V] (M : Model V) : Prop := ∀ n, M.mem n M.nat → ¬ M.mem M.univ n

end Model

open ConNF.NF (IsNF)

/-- Fixed parameter-free formulas uniformly interpret NF in every NFU + Infinity
model, and every NF model is an NFU + Infinity model by declaring every object a set. -/
theorem nf_nfu_inf_mutually_interpretable :
    (∃ δ ε η : Fml, ∀ (V : Type) [Nonempty V] (M : Model V) [Fact M.Infinity],
      ∃ (W : Type) (mem : W → W → Prop)
        (π : {x : V // Sat M.mem M.isSet δ (fun _ => x)} → W),
        IsNF W mem ∧ Function.Surjective π ∧
        (∀ x y, π x = π y ↔ Sat M.mem M.isSet η (Function.update (fun _ => x.1) 103 y.1)) ∧
        (∀ x y, mem (π x) (π y) ↔
          Sat M.mem M.isSet ε (Function.update (fun _ => x.1) 103 y.1))) ∧
    (∀ (V : Type) (mem : V → V → Prop), IsNF V mem →
      ∃ (_ : Nonempty V) (M : Model V), M.mem = mem ∧ (∀ x, M.isSet x) ∧ M.Infinity) := by sorry

end NFUCut


namespace Palomar

/-- A set-sized model of NF exists: extensionality and every instance of the
stratified comprehension scheme hold for one membership relation. -/
theorem exists_nf_model :
    ∃ (V : Type) (mem : V → V → Prop), ConNF.NF.IsNF V mem := by sorry

end Palomar

namespace JensenNFU

inductive TFm : Type
  | mem (i j : ℕ) : TFm
  | eq (i j : ℕ) : TFm
  | neg (φ : TFm) : TFm
  | and (φ ψ : TFm) : TFm
  | all (t : ℕ) (φ : TFm) : TFm

namespace TFm

def Sat {V : Type} (mem : V → V → Prop) : TFm → List V → Prop
  | .mem i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ mem a b
  | .eq i j, env => ∃ a b, env[i]? = some a ∧ env[j]? = some b ∧ a = b
  | .neg φ, env => ¬Sat mem φ env
  | .and φ ψ, env => Sat mem φ env ∧ Sat mem ψ env
  | .all _ φ, env => ∀ a, Sat mem φ (a :: env)

def Strat : List ℕ → TFm → Prop
  | Γ, .mem i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some (t + 1)
  | Γ, .eq i j => ∃ t, Γ[i]? = some t ∧ Γ[j]? = some t
  | Γ, .neg φ => Strat Γ φ
  | Γ, .and φ ψ => Strat Γ φ ∧ Strat Γ ψ
  | Γ, .all t φ => Strat (t :: Γ) φ

end TFm

/-- Jensen's NFU has extensionality for objects with members and stratified comprehension. -/
structure IsNFU (V : Type) (mem : V → V → Prop) : Prop where
  ext : ∀ x y, (∃ z, mem z x) → (∀ z, mem z x ↔ mem z y) → x = y
  comprehension : ∀ (t : ℕ) (Γ : List ℕ) (φ : TFm), TFm.Strat (t :: Γ) φ →
    ∀ params : List V, params.length = Γ.length → ∃ y, ∀ x, mem x y ↔ TFm.Sat mem φ (x :: params)

/-- Infinity: the universe is not finite, using the usual inductive family definition. -/
def UnivInfinite {V : Type} (mem : V → V → Prop) : Prop :=
  ∃ F : V, (∀ e, (∀ z, ¬mem z e) → mem e F) ∧
    (∀ a, mem a F → ∀ b a', (∀ z, mem z a' ↔ mem z a ∨ z = b) → mem a' F) ∧
    ∀ u, (∀ z, mem z u) → ¬mem u F

variable {V : Type*}

/-- Frege zero is the set of all objects without members. -/
def IsZeroN (mem : V → V → Prop) (z : V) : Prop := ∀ e, mem e z ↔ ∀ w, ¬mem w e

def IsSuccN (mem : V → V → Prop) (k k' : V) : Prop :=
  ∀ y, mem y k' ↔ ∃ x, mem x k ∧ ∃ b, ¬mem b x ∧ ∀ z, mem z y ↔ mem z x ∨ z = b

/-- The Frege natural numbers belong to every internally represented inductive family. -/
def IsNatN (mem : V → V → Prop) (n : V) : Prop :=
  ∀ F, ((∀ z, IsZeroN mem z → mem z F) ∧ ∀ k, mem k F → ∀ k', IsSuccN mem k k' → mem k' F) →
    mem n F

/-- Rosser's Axiom of Counting: singleton image preserves every Frege natural number. -/
def Counting (mem : V → V → Prop) : Prop :=
  ∀ n, IsNatN mem n → ∀ x, mem x n →
    ∃ y, mem y n ∧ ∀ s, mem s y ↔ ∃ a, mem a x ∧ ∀ z, mem z s ↔ z = a

end JensenNFU

namespace Palomar

/-- One pair of formulas defines a model of NF with Counting in every model of
NFU with Infinity and Counting. The injection identifies the target with that definable
domain and makes the interpreted equality ordinary equality. -/
theorem nfuic_interprets_nfc :
    ∃ δ ε : JensenNFU.TFm,
      ∀ (V : Type) (memV : V → V → Prop), Nonempty V →
        JensenNFU.IsNFU V memV → JensenNFU.UnivInfinite memV → JensenNFU.Counting memV →
        ∃ (A : Type) (memA : A → A → Prop) (f : A → V),
          Nonempty A ∧ ConNF.NF.IsNF A memA ∧ JensenNFU.Counting memA ∧
          Function.Injective f ∧
          (∀ x : V, JensenNFU.TFm.Sat memV δ [x] ↔ ∃ a, f a = x) ∧
          ∀ a b : A, JensenNFU.TFm.Sat memV ε [f a, f b] ↔ memA a b := by
  sorry

/-- The reverse interpretation is the identity: every model of NF with Counting
already satisfies NFU, Infinity, and Counting with the same membership. -/
theorem nfc_interprets_nfuic (V : Type) (memV : V → V → Prop)
    (hNF : ConNF.NF.IsNF V memV) (hC : JensenNFU.Counting memV) :
    JensenNFU.IsNFU V memV ∧ JensenNFU.UnivInfinite memV ∧ JensenNFU.Counting memV := by
  sorry

end Palomar
