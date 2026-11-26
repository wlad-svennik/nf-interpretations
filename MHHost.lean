module

public import MHAleph
public import Host

@[expose] public section

set_option autoImplicit false

/-!
# The levels of the constructible sets as hosts

In a model of `𝗠𝗛`, let `κ` be a limit ordinal above `ω` such that every constructible subset of
a member of the level at `κ` is a member of that level, and every constructible relation from
a member of the level into the level is bounded in it (`Full κ`). Then the level at `κ`, with
membership and the order of the constructible sets, is a host in the sense of `Host.lean`:
`levHost`.

* `FBd n φ`: the variables of the formula `φ` of `Host.lean` are below `n`; `fsz φ` is a bound.
* `HoldsB T Lt φ ρ`: satisfaction of `φ` in the structure whose domain is the members of `T`,
  with membership and the order given by the pairs in `Lt`.
* `formB n φ`: a bounded formula of set theory that defines `HoldsB`, with the first `n`
  variables, `T` and `Lt` as parameters. `holdsB_sub`, `holdsB_sub2`: one or two variables are
  replaced by new ones.
* `ltL_irrefl'`, `ltL_asymm`, `ltL_trans`, `ltL_of_mem`, `ltL_cover`: the order of the
  constructible sets on a level.
* `exists_ltSet`: the order on the level at `κ` is given by the pairs of a constructible set.
* `def_con`, `def_con2`: the subset of the level at `κ`, and the relation on it, defined over
  the level by a pure formula with parameters are constructible sets.
* `Full κ`, `levPreHost`, **`levHost`**.
* `op_val`, `suc_val`, `om_val`: the pairs, successors and natural numbers of the host are those
  of the model. **`closed_lev`**: if `μ < κ` and `Full μ`, the level at `μ` is a closed level
  of the host at `κ`, in the sense of `Host.Closed`.

That the heights `ℵₙ₊₁` of the constructible sets (`MHAleph.lean`) satisfy `Full` is not proved
here.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-! ### Formulas with bounded variables -/

/-- All the variables of the formula are below `n`. -/
def FBd (n : ℕ) : _root_.Form → Prop
  | .mem x y => x < n ∧ y < n
  | .lt x y => x < n ∧ y < n
  | .eq x y => x < n ∧ y < n
  | .rel _ x y z => x < n ∧ y < n ∧ z < n
  | .tru => True
  | .fls => True
  | .neg φ => FBd n φ
  | .and φ ψ => FBd n φ ∧ FBd n ψ
  | .or φ ψ => FBd n φ ∧ FBd n ψ
  | .imp φ ψ => FBd n φ ∧ FBd n ψ
  | .iff φ ψ => FBd n φ ∧ FBd n ψ
  | .all x φ => x < n ∧ FBd n φ
  | .ex x φ => x < n ∧ FBd n φ

/-- A bound for the variables of a formula. -/
def fsz : _root_.Form → ℕ
  | .mem x y => max x y + 1
  | .lt x y => max x y + 1
  | .eq x y => max x y + 1
  | .rel _ x y z => max x (max y z) + 1
  | .tru => 0
  | .fls => 0
  | .neg φ => fsz φ
  | .and φ ψ => max (fsz φ) (fsz ψ)
  | .or φ ψ => max (fsz φ) (fsz ψ)
  | .imp φ ψ => max (fsz φ) (fsz ψ)
  | .iff φ ψ => max (fsz φ) (fsz ψ)
  | .all x φ => max (x + 1) (fsz φ)
  | .ex x φ => max (x + 1) (fsz φ)

theorem fbd_mono {n m : ℕ} (h : n ≤ m) : ∀ φ : _root_.Form, FBd n φ → FBd m φ
  | .mem _ _, hb => ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩
  | .lt _ _, hb => ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩
  | .eq _ _, hb => ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩
  | .rel _ _ _ _, hb =>
    ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2.1 h, lt_of_lt_of_le hb.2.2 h⟩
  | .tru, _ => trivial
  | .fls, _ => trivial
  | .neg φ, hb => fbd_mono h φ hb
  | .and φ ψ, hb => ⟨fbd_mono h φ hb.1, fbd_mono h ψ hb.2⟩
  | .or φ ψ, hb => ⟨fbd_mono h φ hb.1, fbd_mono h ψ hb.2⟩
  | .imp φ ψ, hb => ⟨fbd_mono h φ hb.1, fbd_mono h ψ hb.2⟩
  | .iff φ ψ, hb => ⟨fbd_mono h φ hb.1, fbd_mono h ψ hb.2⟩
  | .all _ φ, hb => ⟨lt_of_lt_of_le hb.1 h, fbd_mono h φ hb.2⟩
  | .ex _ φ, hb => ⟨lt_of_lt_of_le hb.1 h, fbd_mono h φ hb.2⟩

theorem fbd_fsz : ∀ φ : _root_.Form, FBd (fsz φ) φ
  | .mem x y => ⟨Nat.lt_succ_of_le (le_max_left x y), Nat.lt_succ_of_le (le_max_right x y)⟩
  | .lt x y => ⟨Nat.lt_succ_of_le (le_max_left x y), Nat.lt_succ_of_le (le_max_right x y)⟩
  | .eq x y => ⟨Nat.lt_succ_of_le (le_max_left x y), Nat.lt_succ_of_le (le_max_right x y)⟩
  | .rel _ x y z => ⟨Nat.lt_succ_of_le (le_max_left x _),
      Nat.lt_succ_of_le (le_trans (le_max_left y z) (le_max_right x _)),
      Nat.lt_succ_of_le (le_trans (le_max_right y z) (le_max_right x _))⟩
  | .tru => trivial
  | .fls => trivial
  | .neg φ => fbd_fsz φ
  | .and φ ψ => ⟨fbd_mono (le_max_left _ _) φ (fbd_fsz φ), fbd_mono (le_max_right _ _) ψ (fbd_fsz ψ)⟩
  | .or φ ψ => ⟨fbd_mono (le_max_left _ _) φ (fbd_fsz φ), fbd_mono (le_max_right _ _) ψ (fbd_fsz ψ)⟩
  | .imp φ ψ => ⟨fbd_mono (le_max_left _ _) φ (fbd_fsz φ), fbd_mono (le_max_right _ _) ψ (fbd_fsz ψ)⟩
  | .iff φ ψ => ⟨fbd_mono (le_max_left _ _) φ (fbd_fsz φ), fbd_mono (le_max_right _ _) ψ (fbd_fsz ψ)⟩
  | .all x φ => ⟨lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_left _ _),
      fbd_mono (le_max_right _ _) φ (fbd_fsz φ)⟩
  | .ex x φ => ⟨lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_left _ _),
      fbd_mono (le_max_right _ _) φ (fbd_fsz φ)⟩

/-! ### Satisfaction in a set -/

section holdsB

variable {V : Type} [SetStructure V]

/-- Satisfaction in the structure whose domain is the members of `T`, with membership and the
order given by the pairs in `Lt`. The additional relation symbols are false. -/
def HoldsB (T Lt : V) : _root_.Form → (ℕ → V) → Prop
  | .mem x y, ρ => ρ x ∈ ρ y
  | .lt x y, ρ => Pr Lt (ρ x) (ρ y)
  | .eq x y, ρ => ρ x = ρ y
  | .rel _ _ _ _, _ => False
  | .tru, _ => True
  | .fls, _ => False
  | .neg φ, ρ => ¬HoldsB T Lt φ ρ
  | .and φ ψ, ρ => HoldsB T Lt φ ρ ∧ HoldsB T Lt ψ ρ
  | .or φ ψ, ρ => HoldsB T Lt φ ρ ∨ HoldsB T Lt ψ ρ
  | .imp φ ψ, ρ => HoldsB T Lt φ ρ → HoldsB T Lt ψ ρ
  | .iff φ ψ, ρ => (HoldsB T Lt φ ρ ↔ HoldsB T Lt ψ ρ)
  | .all x φ, ρ => ∀ a, a ∈ T → HoldsB T Lt φ (_root_.upd ρ x a)
  | .ex x φ, ρ => ∃ a, a ∈ T ∧ HoldsB T Lt φ (_root_.upd ρ x a)

theorem upd_agree {ρ ρ' : ℕ → V} {n : ℕ} (h : ∀ i, i < n → ρ i = ρ' i) (x : ℕ) (a : V) :
    ∀ i, i < n → _root_.upd ρ x a i = _root_.upd ρ' x a i := by
  intro i hi
  by_cases e : i = x
  · rw [e, _root_.upd_same, _root_.upd_same]
  · rw [_root_.upd_ne ρ a e, _root_.upd_ne ρ' a e]
    exact h i hi

/-- Satisfaction depends only on the values of the variables of the formula. -/
theorem holdsB_congr (T Lt : V) {n : ℕ} : ∀ (φ : _root_.Form), FBd n φ → ∀ ρ ρ' : ℕ → V,
    (∀ i, i < n → ρ i = ρ' i) → (HoldsB T Lt φ ρ ↔ HoldsB T Lt φ ρ')
  | .mem x y, hb, ρ, ρ', h => by
    simp only [HoldsB]
    rw [h x hb.1, h y hb.2]
  | .lt x y, hb, ρ, ρ', h => by
    simp only [HoldsB]
    rw [h x hb.1, h y hb.2]
  | .eq x y, hb, ρ, ρ', h => by
    simp only [HoldsB]
    rw [h x hb.1, h y hb.2]
  | .rel _ _ _ _, _, _, _, _ => Iff.rfl
  | .tru, _, _, _, _ => Iff.rfl
  | .fls, _, _, _, _ => Iff.rfl
  | .neg φ, hb, ρ, ρ', h => not_congr (holdsB_congr T Lt φ hb ρ ρ' h)
  | .and φ ψ, hb, ρ, ρ', h =>
    and_congr (holdsB_congr T Lt φ hb.1 ρ ρ' h) (holdsB_congr T Lt ψ hb.2 ρ ρ' h)
  | .or φ ψ, hb, ρ, ρ', h =>
    or_congr (holdsB_congr T Lt φ hb.1 ρ ρ' h) (holdsB_congr T Lt ψ hb.2 ρ ρ' h)
  | .imp φ ψ, hb, ρ, ρ', h =>
    imp_congr (holdsB_congr T Lt φ hb.1 ρ ρ' h) (holdsB_congr T Lt ψ hb.2 ρ ρ' h)
  | .iff φ ψ, hb, ρ, ρ', h =>
    iff_congr (holdsB_congr T Lt φ hb.1 ρ ρ' h) (holdsB_congr T Lt ψ hb.2 ρ ρ' h)
  | .all x φ, hb, ρ, ρ', h => forall_congr' fun a => imp_congr Iff.rfl
      (holdsB_congr T Lt φ hb.2 _ _ (upd_agree h x a))
  | .ex x φ, hb, ρ, ρ', h => exists_congr fun a => and_congr Iff.rfl
      (holdsB_congr T Lt φ hb.2 _ _ (upd_agree h x a))

/-- The assignment given by the first `n` values; the other variables take the value at `n`. -/
def envOf {n : ℕ} (v : Fin (n + 2) → V) : ℕ → V :=
  fun i => if h : i < n then v ⟨i, by omega⟩ else v ⟨n, by omega⟩

theorem envOf_lt {n : ℕ} (v : Fin (n + 2) → V) {i : ℕ} (h : i < n) (h' : i < n + 2) :
    envOf v i = v ⟨i, h'⟩ := by
  simp [envOf, h]

/-- The parameters: the values of the first `n` variables, then `T`, then `Q`. -/
def parOf (n : ℕ) (ρ : ℕ → V) (T Q : V) : Fin (n + 2) → V :=
  fun i => if i.val < n then ρ i.val else if i.val = n then T else Q

theorem parOf_T {n : ℕ} {ρ : ℕ → V} {T Q : V} (h : n < n + 2) : parOf n ρ T Q ⟨n, h⟩ = T := by
  simp [parOf]

theorem parOf_Q {n : ℕ} {ρ : ℕ → V} {T Q : V} (h : n + 1 < n + 2) :
    parOf n ρ T Q ⟨n + 1, h⟩ = Q := by
  simp [parOf]

theorem envOf_parOf {n : ℕ} {ρ : ℕ → V} {T Q : V} {i : ℕ} (h : i < n) :
    envOf (parOf n ρ T Q) i = ρ i := by
  simp [envOf, parOf, h]

/-- Send the variable `x` to the new variable, and shift the others. -/
def subF (n x : ℕ) : Fin (n + 2) → Fin (n + 3) :=
  fun i => if i.val = x then 0 else i.succ

/-- Send the variable `x` to the second new variable and `y` to the first, and shift the
others. -/
def subG (n x y : ℕ) : Fin (n + 2) → Fin (n + 5) :=
  fun i => if i.val = x then 1 else if i.val = y then 0 else ⟨i.val + 3, by omega⟩

theorem cons1 {m : ℕ} (a : V) (p : Fin m → V) (i : ℕ) (h : i < m) (h' : i + 1 < m + 1) :
    (a :> p) ⟨i + 1, h'⟩ = p ⟨i, h⟩ := rfl

theorem cons2 {m : ℕ} (a b : V) (p : Fin m → V) (i : ℕ) (h : i < m) (h' : i + 2 < m + 2) :
    (a :> b :> p) ⟨i + 2, h'⟩ = p ⟨i, h⟩ := rfl

theorem cons3 {m : ℕ} (a b c : V) (p : Fin m → V) (i : ℕ) (h : i < m)
    (h' : i + 3 < m + 3) : (a :> b :> c :> p) ⟨i + 3, h'⟩ = p ⟨i, h⟩ := rfl

theorem envOf_sub {n x : ℕ} (hx : x < n) (a : V) (v : Fin (n + 2) → V) :
    envOf (fun i => (a :> v) (subF n x i)) = _root_.upd (envOf v) x a := by
  funext i
  by_cases e : i = x
  · subst e
    rw [_root_.upd_same, envOf_lt _ hx (by omega)]
    simp [subF]
  · rw [_root_.upd_ne _ a e]
    by_cases hi : i < n
    · rw [envOf_lt _ hi (by omega), envOf_lt _ hi (by omega)]
      simp only [subF, if_neg e]
      exact cons1 a v i (by omega) (by omega)
    · simp only [envOf, dif_neg hi, subF, if_neg (show n ≠ x by omega)]
      exact cons1 a v n (by omega) (by omega)

theorem holdsB_sub {n x : ℕ} (hx : x < n) (φ : _root_.Form) (a : V) (v : Fin (n + 2) → V)
    (h1 : n < n + 2) (h2 : n + 1 < n + 2) :
    HoldsB ((a :> v) (subF n x ⟨n, h1⟩)) ((a :> v) (subF n x ⟨n + 1, h2⟩)) φ
        (envOf fun i => (a :> v) (subF n x i)) ↔
      HoldsB (v ⟨n, h1⟩) (v ⟨n + 1, h2⟩) φ (_root_.upd (envOf v) x a) := by
  have e1 : (a :> v) (subF n x ⟨n, h1⟩) = v ⟨n, h1⟩ := by
    simp only [subF, if_neg (show n ≠ x by omega)]
    exact cons1 a v n h1 (by omega)
  have e2 : (a :> v) (subF n x ⟨n + 1, h2⟩) = v ⟨n + 1, h2⟩ := by
    simp only [subF, if_neg (show n + 1 ≠ x by omega)]
    exact cons1 a v (n + 1) h2 (by omega)
  rw [e1, e2, envOf_sub hx a v]

theorem envOf_sub2 {n x y : ℕ} (hx : x < n) (hy : y < n) (hxy : x ≠ y) (b a q : V)
    (v : Fin (n + 2) → V) :
    envOf (fun i => (b :> a :> q :> v) (subG n x y i)) =
      _root_.upd (_root_.upd (envOf v) x a) y b := by
  funext i
  by_cases ey : i = y
  · subst ey
    rw [_root_.upd_same, envOf_lt _ hy (by omega)]
    simp [subG, Ne.symm hxy]
  · rw [_root_.upd_ne _ b ey]
    by_cases ex : i = x
    · subst ex
      rw [_root_.upd_same, envOf_lt _ hx (by omega)]
      simp [subG]
    · rw [_root_.upd_ne _ a ex]
      by_cases hi : i < n
      · rw [envOf_lt _ hi (by omega), envOf_lt _ hi (by omega)]
        simp only [subG, if_neg ex, if_neg ey]
        exact cons3 b a q v i (by omega) (by omega)
      · simp only [envOf, dif_neg hi, subG, if_neg (show n ≠ x by omega),
          if_neg (show n ≠ y by omega)]
        exact cons3 b a q v n (by omega) (by omega)

theorem holdsB_sub2 {n x y : ℕ} (hx : x < n) (hy : y < n) (hxy : x ≠ y) (φ : _root_.Form)
    (b a q : V) (v : Fin (n + 2) → V) (h1 : n < n + 2) (h2 : n + 1 < n + 2) :
    HoldsB ((b :> a :> q :> v) (subG n x y ⟨n, h1⟩)) ((b :> a :> q :> v) (subG n x y ⟨n + 1, h2⟩))
        φ (envOf fun i => (b :> a :> q :> v) (subG n x y i)) ↔
      HoldsB (v ⟨n, h1⟩) (v ⟨n + 1, h2⟩) φ (_root_.upd (_root_.upd (envOf v) x a) y b) := by
  have e1 : (b :> a :> q :> v) (subG n x y ⟨n, h1⟩) = v ⟨n, h1⟩ := by
    simp only [subG, if_neg (show n ≠ x by omega), if_neg (show n ≠ y by omega)]
    exact cons3 b a q v n h1 (by omega)
  have e2 : (b :> a :> q :> v) (subG n x y ⟨n + 1, h2⟩) = v ⟨n + 1, h2⟩ := by
    simp only [subG, if_neg (show n + 1 ≠ x by omega), if_neg (show n + 1 ≠ y by omega)]
    exact cons3 b a q v (n + 1) h2 (by omega)
  rw [e1, e2, envOf_sub2 hx hy hxy b a q v]

theorem holdsB_par {n x : ℕ} (hx : x < n) (φ : _root_.Form) (hb : FBd n φ) (ρ : ℕ → V)
    (T Q z : V) (h1 : n < n + 2) (h2 : n + 1 < n + 2) :
    HoldsB ((z :> parOf n ρ T Q) (subF n x ⟨n, h1⟩)) ((z :> parOf n ρ T Q) (subF n x ⟨n + 1, h2⟩))
        φ (envOf fun i => (z :> parOf n ρ T Q) (subF n x i)) ↔
      HoldsB T Q φ (_root_.upd ρ x z) := by
  refine (holdsB_sub hx φ z _ h1 h2).trans ?_
  rw [parOf_T, parOf_Q]
  exact holdsB_congr T Q φ hb _ _ (upd_agree (fun i hi => envOf_parOf hi) x z)

theorem holdsB_par2 {n x y : ℕ} (hx : x < n) (hy : y < n) (hxy : x ≠ y) (φ : _root_.Form)
    (hb : FBd n φ) (ρ : ℕ → V) (T Q b a q : V) (h1 : n < n + 2) (h2 : n + 1 < n + 2) :
    HoldsB ((b :> a :> q :> parOf n ρ T Q) (subG n x y ⟨n, h1⟩))
        ((b :> a :> q :> parOf n ρ T Q) (subG n x y ⟨n + 1, h2⟩)) φ
        (envOf fun i => (b :> a :> q :> parOf n ρ T Q) (subG n x y i)) ↔
      HoldsB T Q φ (_root_.upd (_root_.upd ρ x a) y b) := by
  refine (holdsB_sub2 hx hy hxy φ b a q _ h1 h2).trans ?_
  rw [parOf_T, parOf_Q]
  exact holdsB_congr T Q φ hb _ _
    (upd_agree (upd_agree (fun i hi => envOf_parOf hi) x a) y b)

end holdsB

/-- **A bounded formula for satisfaction in a set.** The first `n` variables are the values of
the variables of the formula; then come the set and the order. -/
def formB (n : ℕ) : (φ : _root_.Form) → FBd n φ →
    BDef (k := n + 2) (fun V _ v ↦ HoldsB (v ⟨n, by omega⟩) (v ⟨n + 1, by omega⟩) φ (envOf v))
  | .mem x y, hb =>
    (BDef.mem (k := n + 2) ⟨x, by have := hb.1; omega⟩ ⟨y, by have := hb.2; omega⟩).congr
      fun V _ v => by simp [HoldsB, envOf, hb.1, hb.2]
  | .lt x y, hb =>
    (prB.comp ![⟨n + 1, by omega⟩, ⟨x, by have := hb.1; omega⟩,
      ⟨y, by have := hb.2; omega⟩]).congr
      fun V _ v => by simp [HoldsB, envOf, hb.1, hb.2]
  | .eq x y, hb =>
    (BDef.eq (k := n + 2) ⟨x, by have := hb.1; omega⟩ ⟨y, by have := hb.2; omega⟩).congr
      fun V _ v => by simp [HoldsB, envOf, hb.1, hb.2]
  | .rel _ _ _ _, _ => (BDef.fls (k := n + 2)).congr fun V _ v => by simp [HoldsB]
  | .tru, _ => ((BDef.fls (k := n + 2)).not).congr fun V _ v => by simp [HoldsB]
  | .fls, _ => (BDef.fls (k := n + 2)).congr fun V _ v => by simp [HoldsB]
  | .neg φ, hb => ((formB n φ hb).not).congr fun _ _ _ => Iff.rfl
  | .and φ ψ, hb => ((formB n φ hb.1).and (formB n ψ hb.2)).congr fun _ _ _ => Iff.rfl
  | .or φ ψ, hb => ((formB n φ hb.1).or (formB n ψ hb.2)).congr fun _ _ _ => Iff.rfl
  | .imp φ ψ, hb => ((formB n φ hb.1).imp (formB n ψ hb.2)).congr fun _ _ _ => Iff.rfl
  | .iff φ ψ, hb => ((formB n φ hb.1).iff (formB n ψ hb.2)).congr fun _ _ _ => Iff.rfl
  | .all x φ, hb =>
    (BDef.ball ⟨n, by omega⟩ ((formB n φ hb.2).comp (subF n x))).congr fun V _ v =>
      forall_congr' fun a => imp_congr Iff.rfl (holdsB_sub hb.1 φ a v (by omega) (by omega))
  | .ex x φ, hb =>
    (BDef.bex ⟨n, by omega⟩ ((formB n φ hb.2).comp (subF n x))).congr fun V _ v =>
      exists_congr fun a => and_congr Iff.rfl (holdsB_sub hb.1 φ a v (by omega) (by omega))

/-! ### The order of the constructible sets on a level -/

section host

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem ltL_irrefl' {γ x : V} (hγ : Ord γ) (hx : x ∈ Lev γ) : ¬LtL x x := by
  obtain ⟨m, hm, hmin⟩ := ltL_least hγ ({x} : V)
    (fun z hz => by rw [show z = x by simpa using hz]; exact hx) ⟨x, by simp⟩
  have e : m = x := by simpa using hm
  rw [e] at hmin
  exact hmin x (by simp)

theorem ltL_asymm {γ x y : V} (hγ : Ord γ) (hx : x ∈ Lev γ) (hy : y ∈ Lev γ) (h : LtL x y) :
    ¬LtL y x := by
  intro h'
  obtain ⟨m, hm, hmin⟩ := ltL_least hγ ({x, y} : V)
    (fun z hz => by
      rcases (by simpa using hz : z = x ∨ z = y) with e | e
      · rw [e]; exact hx
      · rw [e]; exact hy) ⟨x, by simp⟩
  rcases (by simpa using hm : m = x ∨ m = y) with e | e
  · rw [e] at hmin
    exact hmin y (by simp) h'
  · rw [e] at hmin
    exact hmin x (by simp) h

theorem ltL_trans {γ x y z : V} (hγ : Ord γ) (hx : x ∈ Lev γ) (hy : y ∈ Lev γ)
    (hz : z ∈ Lev γ) (h1 : LtL x y) (h2 : LtL y z) : LtL x z := by
  rcases ltL_tri hγ hx hz with h | h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 (ltL_asymm hγ hy hz h2)
  · exfalso
    obtain ⟨m, hm, hmin⟩ := ltL_least hγ ({x, y, z} : V)
      (fun w hw => by
        rcases (by simpa using hw : w = x ∨ w = y ∨ w = z) with e | e | e
        · rw [e]; exact hx
        · rw [e]; exact hy
        · rw [e]; exact hz) ⟨x, by simp⟩
    rcases (by simpa using hm : m = x ∨ m = y ∨ m = z) with e | e | e
    · rw [e] at hmin
      exact hmin z (by simp) h
    · rw [e] at hmin
      exact hmin x (by simp) h1
    · rw [e] at hmin
      exact hmin y (by simp) h2

/-- A member comes before the set. -/
theorem ltL_of_mem {γ x y : V} (hγ : Ord γ) (hy : y ∈ Lev γ) (hxy : x ∈ y) : LtL x y := by
  obtain ⟨β₂, -, r₂⟩ := rkL_exists hγ hy
  have hx : x ∈ Lev β₂ := by
    rcases r₂.2.1 with e | ⟨s, -, y₁, -, y₂, -, y₃, -, hD⟩
    · rw [e] at hxy
      exact hxy
    · exact (hD.1 x hxy).1
  obtain ⟨β₁, hβ₁, r₁⟩ := rkL_exists r₂.1 hx
  exact (ltL_iff_rk r₁ r₂).mpr (Or.inl hβ₁)

/-- The sets before a member of a level are members of an earlier level. -/
theorem ltL_cover {γ a : V} (hγ : Ord γ) (ha : a ∈ Lev γ) :
    ∃ β, β ∈ γ ∧ ∀ b, LtL b a → b ∈ Lev (sc β) := by
  obtain ⟨β, hβ, r⟩ := rkL_exists hγ ha
  refine ⟨β, hβ, fun b hb => ?_⟩
  obtain ⟨β₁, β₂, r₁, r₂, hlt⟩ := hb
  rw [rkL_unique r₂ r] at hlt
  refine (rkL_mem r₁ (ord_sc r.1)).mpr ?_
  rcases hlt with h | ⟨h, -⟩
  · exact mem_sc.mpr (Or.inr h)
  · exact mem_sc.mpr (Or.inl h)

/-- **The order on a level is given by the pairs of a constructible set.** -/
theorem exists_ltSet {κ : V} (hκ : Big κ) :
    ∃ Q : V, Con Q ∧ ∀ x y, x ∈ Lev κ → y ∈ Lev κ → (Pr Q x y ↔ LtL x y) := by
  have g := big_scn hκ 4
  have h0 := empty_mem_lev g.1 (big_ne g)
  let Q : V := sepB (k := 1) (BDef.mem 0 1) (Lev (scn 4 κ)) ![LtS (scn 4 κ)]
  have hQ : ∀ z, z ∈ Q ↔ z ∈ Lev (scn 4 κ) ∧ z ∈ LtS (scn 4 κ) := fun z => mem_sepB _ _ _ z
  have hQL : Q ∈ Lev (sc (scn 4 κ)) :=
    def_mem_lev (ord_sc g.1) (self_mem_sc _) (nm_mem_lev g 7) h0 h0 h0
      (isD_of (s := nm 7) fun z => (hQ z).trans (and_congr Iff.rfl phi7.symm))
  refine ⟨Q, ⟨_, ord_sc g.1, hQL⟩, fun x y hx hy => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact ((lts_iff g.1).mp (pr_iff.mpr ((hQ _).mp (pr_iff.mp h)).2)).2.2
  · exact pr_iff.mpr ((hQ _).mpr ⟨kp_mem_lev hκ hx hy,
      pr_iff.mp ((lts_iff g.1).mpr ⟨lev_scn_sub hκ.1 4 x hx, lev_scn_sub hκ.1 4 y hy, h⟩)⟩)

/-! ### Levels at limit ordinals -/

theorem lev_lim_exists {κ x : V} (hκ : Lim κ) (hom : (om : V) ∈ κ) (hx : x ∈ Lev κ) :
    ∃ δ, δ ∈ κ ∧ Big δ ∧ x ∈ Lev δ := by
  obtain ⟨β, hβ, hin⟩ := (mem_lev hκ.1).mp hx
  have hβo := ord_mem hκ.1 hβ
  have h1 : x ∈ Lev (sc β) := inDef_mem hβo hin
  rcases ord_tri (ord_sc hβo) (ord_om (V := V)) with e | e | e
  · exact ⟨om, hom, big_om, lev_mono ord_om e x h1⟩
  · exact ⟨om, hom, big_om, e ▸ h1⟩
  · exact ⟨sc β, hκ.2.2 β hβ, ⟨ord_sc hβo, fun n hn => (ord_sc hβo).1 om e n hn⟩, h1⟩

theorem lev_lim_exists2 {κ x y : V} (hκ : Lim κ) (hom : (om : V) ∈ κ) (hx : x ∈ Lev κ)
    (hy : y ∈ Lev κ) : ∃ δ, δ ∈ κ ∧ Big δ ∧ x ∈ Lev δ ∧ y ∈ Lev δ := by
  obtain ⟨δ₁, d₁, b₁, h₁⟩ := lev_lim_exists hκ hom hx
  obtain ⟨δ₂, d₂, b₂, h₂⟩ := lev_lim_exists hκ hom hy
  rcases ord_tri b₁.1 b₂.1 with e | e | e
  · exact ⟨δ₂, d₂, b₂, lev_mono b₂.1 e x h₁, h₂⟩
  · exact ⟨δ₁, d₁, b₁, h₁, e ▸ h₂⟩
  · exact ⟨δ₁, d₁, b₁, h₁, lev_mono b₁.1 e y h₂⟩

/-- **Separation for bounded formulas in the level at a limit ordinal.** -/
theorem sep_lim {κ δ : V} (hκ : Lim κ) (hδ : δ ∈ κ) (hδb : Big δ) {k : ℕ} {R : MRel (k + 1)}
    (d : BDef R) (p : Fin k → V) (hp : ∀ i, p i ∈ Lev δ) :
    ∃ y, y ∈ Lev κ ∧ ∀ z, z ∈ y ↔ z ∈ Lev δ ∧ R V (z :> p) := by
  have ht : Good (fun a : V ↦ a ∈ Lev κ) (Lev δ) :=
    ⟨lev_mem hκ.1 hδ, sc δ, big_sc hδb, lev_mem hκ.1 (hκ.2.2 δ hδ),
      lev_mem (ord_sc hδb.1) (self_mem_sc δ)⟩
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef (closed_lev_lim hκ) d ht (lev_tr hδb.1) p
    (fun i => ⟨hp i, lev_mono hκ.1 hδ _ (hp i), δ, hδb, lev_mem hκ.1 hδ, hp i⟩)
  exact ⟨y, hy.1, hyz⟩

theorem con_inter {y a : V} (hy : Con y) (ha : Con a) :
    ∃ S : V, Con S ∧ ∀ z, z ∈ S ↔ z ∈ y ∧ z ∈ a := by
  obtain ⟨γ, hγ, h1, h2⟩ := con_big2 hy ha
  obtain ⟨S, hS, hSz⟩ := sep_good_bdef (closed_true (V := V)) (k := 2)
    ((BDef.mem 0 1).and (BDef.mem 0 2)) (good_of_con (con_lev hγ.1)) (lev_tr hγ.1) ![y, a] (by
      intro j
      match j with
      | 0 => exact ⟨h1, good_of_con hy⟩
      | 1 => exact ⟨h2, good_of_con ha⟩)
  have hSz' : ∀ z, z ∈ S ↔ z ∈ Lev γ ∧ (z ∈ y ∧ z ∈ a) := hSz
  exact ⟨S, con_of_good hS, fun z => ⟨fun h => ((hSz' z).mp h).2,
    fun h => (hSz' z).mpr ⟨lev_tr hγ.1 y h1 z h.1, h⟩⟩⟩

/-! ### The host -/

/-- **The height of a level that satisfies Separation and Collection**: a limit ordinal above
`ω` such that every constructible subset of a member of the level is a member of the level,
and every constructible relation from a member of the level into the level is bounded in the
level. -/
structure Full (κ : V) : Prop where
  lim : Lim κ
  omega : (om : V) ∈ κ
  sub : ∀ a x : V, a ∈ Lev κ → Con x → (∀ z, z ∈ x → z ∈ a) → x ∈ Lev κ
  bd : ∀ a R : V, a ∈ Lev κ → Con R → (∀ u, u ∈ a → ∃ v, v ∈ Lev κ ∧ kp u v ∈ R) →
    ∃ b, b ∈ Lev κ ∧ ∀ u, u ∈ a → ∃ v, v ∈ b ∧ kp u v ∈ R

/-- The members of the level at `κ`. -/
abbrev LevT (κ : V) : Type := {x : V // x ∈ Lev κ}

theorem val_upd {κ : V} (ρ : ℕ → LevT κ) (x : ℕ) (a : LevT κ) :
    (fun i => (_root_.upd ρ x a i).1) = _root_.upd (fun i => (ρ i).1) x a.1 := by
  funext i
  show (_root_.upd ρ x a i).1 = _root_.upd (fun i => (ρ i).1) x a.1 i
  by_cases e : i = x
  · rw [e, _root_.upd_same, _root_.upd_same]
  · rw [_root_.upd_ne ρ a e, _root_.upd_ne _ a.1 e]

/-- Satisfaction in the level is satisfaction in the set. -/
theorem holds_iff_holdsB {κ Q : V}
    (hQ : ∀ x y, x ∈ Lev κ → y ∈ Lev κ → (Pr Q x y ↔ LtL x y)) :
    ∀ (φ : _root_.Form), φ.Pure → ∀ ρ : ℕ → LevT κ,
      (_root_.Holds (fun a b : LevT κ => a.1 ∈ b.1) (fun a b : LevT κ => LtL a.1 b.1)
          _root_.noRel φ ρ ↔ HoldsB (Lev κ) Q φ (fun i => (ρ i).1))
  | .mem _ _, _, _ => Iff.rfl
  | .lt x y, _, ρ => (hQ _ _ (ρ x).2 (ρ y).2).symm
  | .eq _ _, _, _ => Subtype.ext_iff
  | .rel _ _ _ _, h, _ => h.elim
  | .tru, _, _ => Iff.rfl
  | .fls, _, _ => Iff.rfl
  | .neg φ, h, ρ => not_congr (holds_iff_holdsB hQ φ h ρ)
  | .and φ ψ, h, ρ => and_congr (holds_iff_holdsB hQ φ h.1 ρ) (holds_iff_holdsB hQ ψ h.2 ρ)
  | .or φ ψ, h, ρ => or_congr (holds_iff_holdsB hQ φ h.1 ρ) (holds_iff_holdsB hQ ψ h.2 ρ)
  | .imp φ ψ, h, ρ => imp_congr (holds_iff_holdsB hQ φ h.1 ρ) (holds_iff_holdsB hQ ψ h.2 ρ)
  | .iff φ ψ, h, ρ => iff_congr (holds_iff_holdsB hQ φ h.1 ρ) (holds_iff_holdsB hQ ψ h.2 ρ)
  | .all x φ, h, ρ => by
    constructor
    · intro hall a ha
      exact (congrArg (HoldsB (Lev κ) Q φ) (val_upd ρ x ⟨a, ha⟩)).mp
        ((holds_iff_holdsB hQ φ h (_root_.upd ρ x ⟨a, ha⟩)).mp (hall ⟨a, ha⟩))
    · intro hall a
      exact (holds_iff_holdsB hQ φ h (_root_.upd ρ x a)).mpr
        ((congrArg (HoldsB (Lev κ) Q φ) (val_upd ρ x a)).mpr (hall a.1 a.2))
  | .ex x φ, h, ρ => by
    constructor
    · intro hex
      obtain ⟨a, ha⟩ := hex
      exact ⟨a.1, a.2, (congrArg (HoldsB (Lev κ) Q φ) (val_upd ρ x a)).mp
        ((holds_iff_holdsB hQ φ h (_root_.upd ρ x a)).mp ha)⟩
    · intro hex
      obtain ⟨a, ha, hh⟩ := hex
      exact ⟨⟨a, ha⟩, (holds_iff_holdsB hQ φ h (_root_.upd ρ x ⟨a, ha⟩)).mpr
        ((congrArg (HoldsB (Lev κ) Q φ) (val_upd ρ x ⟨a, ha⟩)).mpr hh)⟩

/-- **The subset of the level defined over the level by a pure formula with parameters is the
trace of a constructible set.** -/
theorem def_con {κ : V} (hκ : Full κ) (φ : _root_.Form) (hφ : φ.Pure) (ρ : ℕ → LevT κ)
    (x : ℕ) : ∃ y : V, Con y ∧ ∀ w : LevT κ, w.1 ∈ y ↔
      _root_.Holds (fun a b : LevT κ => a.1 ∈ b.1) (fun a b : LevT κ => LtL a.1 b.1)
        _root_.noRel φ (_root_.upd ρ x w) := by
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hκ.lim)
  obtain ⟨γ, hγ, hQγ, hTγ⟩ := con_big2 hQc (con_lev hκ.lim.1)
  obtain ⟨n, hb, hx⟩ : ∃ n, FBd n φ ∧ x < n :=
    ⟨max (fsz φ) (x + 1), fbd_mono (le_max_left _ _) φ (fbd_fsz φ),
      lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _)⟩
  have hpγ : ∀ i, parOf n (fun i => (ρ i).1) (Lev κ) Q i ∈ Lev γ := by
    intro i
    unfold parOf
    split_ifs
    · exact lev_tr hγ.1 _ hTγ _ (ρ i.val).2
    · exact hTγ
    · exact hQγ
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef closed_true ((formB n φ hb).comp (subF n x))
    (good_of_con (con_lev hγ.1)) (lev_tr hγ.1) (parOf n (fun i => (ρ i).1) (Lev κ) Q)
    (fun i => ⟨hpγ i, good_of_con ⟨γ, hγ.1, hpγ i⟩⟩)
  have h1 : ∀ z, z ∈ y ↔ z ∈ Lev γ ∧ HoldsB (Lev κ) Q φ (_root_.upd (fun i => (ρ i).1) x z) :=
    fun z => (hyz z).trans (and_congr Iff.rfl
      (holdsB_par hx φ hb _ _ _ z (by omega) (by omega)))
  refine ⟨y, con_of_good hy, fun w => ?_⟩
  have e3 := congrArg (HoldsB (Lev κ) Q φ) (val_upd ρ x w)
  exact (h1 w.1).trans ⟨fun h => (holds_iff_holdsB hQ φ hφ (_root_.upd ρ x w)).mpr (e3.mpr h.2),
    fun h => ⟨lev_tr hγ.1 _ hTγ _ w.2,
      e3.mp ((holds_iff_holdsB hQ φ hφ (_root_.upd ρ x w)).mp h)⟩⟩

/-- **The relation on the level defined over the level by a pure formula with parameters is
given by the pairs of a constructible set.** -/
theorem def_con2 {κ : V} (hκ : Full κ) (φ : _root_.Form) (hφ : φ.Pure) (ρ : ℕ → LevT κ)
    {x y : ℕ} (hxy : x ≠ y) : ∃ R : V, Con R ∧ ∀ u v : LevT κ, kp u.1 v.1 ∈ R ↔
      _root_.Holds (fun a b : LevT κ => a.1 ∈ b.1) (fun a b : LevT κ => LtL a.1 b.1)
        _root_.noRel φ (_root_.upd (_root_.upd ρ x u) y v) := by
  obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hκ.lim)
  obtain ⟨γ₀, hγ₀, hQγ₀, hTγ₀⟩ := con_big2 hQc (con_lev hκ.lim.1)
  have hγ := big_scn hγ₀ 4
  have up : ∀ z, z ∈ Lev γ₀ → z ∈ Lev (scn 4 γ₀) := lev_scn_sub hγ₀.1 4
  obtain ⟨n, hb, hx, hy⟩ : ∃ n, FBd n φ ∧ x < n ∧ y < n :=
    ⟨max (fsz φ) (max (x + 1) (y + 1)), fbd_mono (le_max_left _ _) φ (fbd_fsz φ),
      lt_of_lt_of_le (Nat.lt_succ_self x) (le_trans (le_max_left _ _) (le_max_right _ _)),
      lt_of_lt_of_le (Nat.lt_succ_self y) (le_trans (le_max_right _ _) (le_max_right _ _))⟩
  have hpγ : ∀ i, parOf n (fun i => (ρ i).1) (Lev κ) Q i ∈ Lev (scn 4 γ₀) := by
    intro i
    unfold parOf
    split_ifs
    · exact up _ (lev_tr hγ₀.1 _ hTγ₀ _ (ρ i.val).2)
    · exact up _ hTγ₀
    · exact up _ hQγ₀
  obtain ⟨R, hR, hRz⟩ := sep_good_bdef closed_true
    (BDef.bex ⟨n + 1, by omega⟩ (BDef.bex ⟨n + 2, by omega⟩
      ((isOpB.comp ![2, 1, 0]).and ((formB n φ hb).comp (subG n x y)))))
    (good_of_con (con_lev hγ.1)) (lev_tr hγ.1) (parOf n (fun i => (ρ i).1) (Lev κ) Q)
    (fun i => ⟨hpγ i, good_of_con ⟨_, hγ.1, hpγ i⟩⟩)
  have h1 : ∀ z, z ∈ R ↔ z ∈ Lev (scn 4 γ₀) ∧ ∃ a, a ∈ Lev κ ∧ ∃ b, b ∈ Lev κ ∧
      (IsOp z a b ∧ HoldsB (Lev κ) Q φ
        (_root_.upd (_root_.upd (fun i => (ρ i).1) x a) y b)) :=
    fun z => (hRz z).trans (and_congr Iff.rfl (exists_congr fun a => and_congr
      (iff_of_eq (by rw [cons1 z _ n (by omega) (by omega), parOf_T]))
      (exists_congr fun b => and_congr
        (iff_of_eq (by rw [cons2 a z _ n (by omega) (by omega), parOf_T]))
        (and_congr Iff.rfl (holdsB_par2 hx hy hxy φ hb _ _ _ b a z (by omega) (by omega))))))
  refine ⟨R, con_of_good hR, fun u v => ?_⟩
  have e5 : (fun i => (_root_.upd (_root_.upd ρ x u) y v i).1) =
      _root_.upd (_root_.upd (fun i => (ρ i).1) x u.1) y v.1 :=
    (val_upd (_root_.upd ρ x u) y v).trans
      (congrArg (fun r => _root_.upd r y v.1) (val_upd ρ x u))
  have e6 := congrArg (HoldsB (Lev κ) Q φ) e5
  rw [h1, holds_iff_holdsB hQ φ hφ (_root_.upd (_root_.upd ρ x u) y v)]
  constructor
  · rintro ⟨-, a, -, b, -, hop, hh⟩
    obtain ⟨ea, eb⟩ := kp_inj (isOp_iff.mp hop)
    rw [← ea, ← eb] at hh
    exact e6.mpr hh
  · intro hh
    exact ⟨kp_mem_lev hγ₀ (lev_tr hγ₀.1 _ hTγ₀ _ u.2) (lev_tr hγ₀.1 _ hTγ₀ _ v.2),
      u.1, u.2, v.1, v.2, isOp_kp _ _, e6.mp hh⟩

/-- The data of a host for the level at `κ`. -/
noncomputable def levPreHost {κ : V} (hκ : Full κ) : PreHost where
  W := LevT κ
  mem := fun a b => a.1 ∈ b.1
  lt := fun a b => LtL a.1 b.1
  ext := fun x y h => Subtype.ext (mem_ext fun z =>
    ⟨fun hz => (h ⟨z, lev_tr hκ.lim.1 x.1 x.2 z hz⟩).mp hz,
      fun hz => (h ⟨z, lev_tr hκ.lim.1 y.1 y.2 z hz⟩).mpr hz⟩)
  pair := fun x y => by
    obtain ⟨δ, hδ, hδb, hx, hy⟩ := lev_lim_exists2 hκ.lim hκ.omega x.2 y.2
    obtain ⟨p, hp, hpz⟩ := sep_lim hκ.lim hδ hδb (k := 2) ((BDef.eq 0 1).or (BDef.eq 0 2))
      ![x.1, y.1] (by
        intro j
        match j with
        | 0 => exact hx
        | 1 => exact hy)
    have hpz' : ∀ z, z ∈ p ↔ z ∈ Lev δ ∧ (z = x.1 ∨ z = y.1) := hpz
    refine ⟨⟨p, hp⟩, fun z => ?_⟩
    show z.1 ∈ p ↔ z = x ∨ z = y
    rw [hpz', Subtype.ext_iff, Subtype.ext_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.elim (fun e => e ▸ hx) (fun e => e ▸ hy), h⟩⟩
  union := fun x => by
    obtain ⟨δ, hδ, hδb, hx⟩ := lev_lim_exists hκ.lim hκ.omega x.2
    obtain ⟨u, hu, huz⟩ := sep_lim hκ.lim hδ hδb (k := 1) (BDef.bex 1 (BDef.mem 1 0))
      ![x.1] (fun j => by
        have e := Fin.eq_zero j
        subst e
        exact hx)
    have huz' : ∀ z, z ∈ u ↔ z ∈ Lev δ ∧ ∃ w, w ∈ x.1 ∧ z ∈ w := huz
    refine ⟨⟨u, hu⟩, fun z => ?_⟩
    show z.1 ∈ u ↔ ∃ y : LevT κ, y.1 ∈ x.1 ∧ z.1 ∈ y.1
    rw [huz']
    constructor
    · rintro ⟨-, w, hw, hzw⟩
      exact ⟨⟨w, lev_tr hκ.lim.1 x.1 x.2 w hw⟩, hw, hzw⟩
    · rintro ⟨y, hy, hzy⟩
      exact ⟨lev_tr hδb.1 y.1 (lev_tr hδb.1 x.1 hx y.1 hy) z.1 hzy, y.1, hy, hzy⟩
  inf := by
    have hom : (om : V) ∈ Lev κ := ord_mem_lev_lim hκ.lim om hκ.omega
    have hin : ∀ z, z ∈ (om : V) → z ∈ Lev κ := fun z hz => lev_tr hκ.lim.1 om hom z hz
    refine ⟨⟨om, hom⟩, ⟨⟨∅, hin ∅ empty_mem_om⟩, empty_mem_om,
      fun z (hz : z.1 ∈ (∅ : V)) => absurd hz (by simp)⟩, fun x hx => ?_⟩
    refine ⟨⟨sc x.1, hin _ (sc_mem_om hx)⟩, sc_mem_om hx, fun z => ?_⟩
    show z.1 ∈ sc x.1 ↔ z.1 ∈ x.1 ∨ z = x
    rw [mem_sc, Subtype.ext_iff]
    exact or_comm
  sep := fun φ hφ ρ x a => by
    obtain ⟨y, hy, hyw⟩ := def_con hκ φ hφ ρ x
    obtain ⟨S, hS, hSz⟩ := con_inter hy ⟨κ, hκ.lim.1, a.2⟩
    exact ⟨⟨S, hκ.sub a.1 S a.2 hS (fun z hz => ((hSz z).mp hz).2)⟩, fun w =>
      (hSz w.1).trans (and_comm.trans (and_congr Iff.rfl (hyw w)))⟩
  coll := fun φ hφ ρ x y a hxy htot => by
    obtain ⟨R, hR, hRuv⟩ := def_con2 hκ φ hφ ρ hxy
    obtain ⟨b, hb, hbu⟩ := hκ.bd a.1 R a.2 hR (fun u hu => by
      have hu' : u ∈ Lev κ := lev_tr hκ.lim.1 a.1 a.2 u hu
      obtain ⟨v, hv⟩ := htot ⟨u, hu'⟩ hu
      exact ⟨v.1, v.2, (hRuv ⟨u, hu'⟩ v).mpr hv⟩)
    refine ⟨⟨b, hb⟩, fun u hu => ?_⟩
    obtain ⟨v, hvb, hv⟩ := hbu u.1 hu
    have hv' : v ∈ Lev κ := lev_tr hκ.lim.1 b hb v hvb
    exact ⟨⟨v, hv'⟩, hvb, (hRuv u ⟨v, hv'⟩).mp hv⟩
  lt_irrefl := fun x => ltL_irrefl' hκ.lim.1 x.2
  lt_trans := fun x y z => ltL_trans hκ.lim.1 x.2 y.2 z.2
  lt_tri := fun x y => by
    rcases ltL_tri hκ.lim.1 x.2 y.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  least := fun a hne => by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨m, hm, hmin⟩ := ltL_least hκ.lim.1 a.1
      (fun z hz => lev_tr hκ.lim.1 a.1 a.2 z hz) ⟨x.1, hx⟩
    exact ⟨⟨m, lev_tr hκ.lim.1 a.1 a.2 m hm⟩, hm, fun b hb => hmin b.1 hb⟩
  mem_lt := fun x y h => ltL_of_mem hκ.lim.1 y.2 h
  cover := fun a => by
    obtain ⟨β, hβ, hc⟩ := ltL_cover hκ.lim.1 a.2
    exact ⟨⟨Lev (sc β), lev_mem hκ.lim.1 (hκ.lim.2.2 β hβ)⟩, fun b hb => hc b.1 hb⟩

/-- **The level at `κ`, with membership and the order of the constructible sets, is a host.** -/
noncomputable def levHost {κ : V} (hκ : Full κ) : Host := (levPreHost hκ).toHost

/-! ### The closed levels of the host -/

section closed

variable {κ : V} (hκ : Full κ)

/-- The set that an element of the host is. -/
noncomputable def hval (a : (levHost hκ).W) : V := (show LevT κ from a).1

theorem hval_mem (a : (levHost hκ).W) : hval hκ a ∈ Lev κ := (show LevT κ from a).2

/-- The element of the host that a member of the level is. -/
noncomputable def hmk (x : V) (hx : x ∈ Lev κ) : (levHost hκ).W := (⟨x, hx⟩ : LevT κ)

theorem hlift {b : (levHost hκ).W} {x : V} (hx : x ∈ hval hκ b) :
    ∃ a : (levHost hκ).W, hval hκ a = x ∧ a ∈ b :=
  ⟨hmk hκ x (lev_tr hκ.lim.1 _ (hval_mem hκ b) x hx), rfl, hx⟩

theorem emp_val : hval hκ (levHost hκ).emp = ∅ :=
  mem_ext fun z => ⟨fun hz => by
    obtain ⟨a, -, ha⟩ := hlift hκ hz
    exact absurd ha ((levHost hκ).not_mem_emp a), fun hz => absurd hz (by simp)⟩

theorem up_val (a b : (levHost hκ).W) :
    hval hκ ((levHost hκ).up a b) = {hval hκ a, hval hκ b} := by
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨c, rfl, hc⟩ := hlift hκ hz
    rcases (levHost hκ).mem_up.mp hc with e | e <;> simp [e]
  · rcases (by simpa using hz : z = hval hκ a ∨ z = hval hκ b) with e | e
    · rw [e]
      exact (levHost hκ).mem_up.mpr (Or.inl rfl)
    · rw [e]
      exact (levHost hκ).mem_up.mpr (Or.inr rfl)

theorem sg_val (a : (levHost hκ).W) : hval hκ ((levHost hκ).sg a) = {hval hκ a} := by
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨c, rfl, hc⟩ := hlift hκ hz
    simp [(levHost hκ).mem_sg.mp hc]
  · rw [show z = hval hκ a by simpa using hz]
    exact (levHost hκ).mem_sg.mpr rfl

/-- The pairs of the host are the pairs of the model. -/
theorem op_val (a b : (levHost hκ).W) :
    hval hκ ((levHost hκ).op a b) = kp (hval hκ a) (hval hκ b) := by
  show hval hκ ((levHost hκ).up ((levHost hκ).sg a) ((levHost hκ).up a b)) = _
  rw [up_val, sg_val, up_val]
  rfl

theorem suc_val (x : (levHost hκ).W) : hval hκ ((levHost hκ).suc x) = sc (hval hκ x) := by
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨c, rfl, hc⟩ := hlift hκ hz
    rcases (levHost hκ).mem_suc.mp hc with h | h
    · exact mem_sc.mpr (Or.inr h)
    · exact mem_sc.mpr (Or.inl (congrArg (hval hκ) h))
  · rcases mem_sc.mp hz with e | h
    · rw [e]
      exact (levHost hκ).mem_suc.mpr (Or.inr rfl)
    · obtain ⟨c, rfl, hc⟩ := hlift hκ h
      exact (levHost hκ).mem_suc.mpr (Or.inl hc)

/-- The natural numbers of the host are the natural numbers of the model. -/
theorem om_val : hval hκ (levHost hκ).om = (om : V) := by
  have homκ : (om : V) ∈ Lev κ := ord_mem_lev_lim hκ.lim om hκ.omega
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨c, rfl, hc⟩ := hlift hκ hz
    have hind : (levHost hκ).Ind (hmk hκ om homκ) := (levHost hκ).ind_iff.mpr
      ⟨by
        show hval hκ (levHost hκ).emp ∈ (om : V)
        rw [emp_val hκ]
        exact empty_mem_om,
       fun x hx => by
        show hval hκ ((levHost hκ).suc x) ∈ (om : V)
        rw [suc_val hκ]
        exact sc_mem_om hx⟩
    exact (levHost hκ).mem_om.mp hc _ hind
  · have h0 : (∅ : V) ∈ hval hκ (levHost hκ).om := by
      rw [← emp_val hκ]
      exact (levHost hκ).emp_mem_om
    have hs : ∀ n, n ∈ hval hκ (levHost hκ).om → sc n ∈ hval hκ (levHost hκ).om := by
      intro n hn
      obtain ⟨c, rfl, hc⟩ := hlift hκ hn
      rw [← suc_val hκ]
      exact (levHost hκ).suc_mem_om hc
    exact om_ind (k := 1) (BDef.mem 0 1) ![hval hκ (levHost hκ).om] h0
      (fun n _ hn => hs n hn) z hz

/-- **The level at a smaller height of the same kind is a closed level of the host.** -/
theorem closed_lev {μ : V} (hμ : Full μ) (hμκ : μ ∈ κ) :
    (levHost hκ).Closed (hmk hκ (Lev μ) (lev_mem hκ.lim.1 hμκ)) := by
  have hsubκ : ∀ z, z ∈ Lev μ → z ∈ Lev κ := lev_mono hκ.lim.1 hμκ
  refine ⟨fun x y hxy hy => ?_, fun x y hxy hy => ?_, fun f hf hd hran => ?_,
    fun a ha => ?_, ?_⟩
  · exact lev_tr hμ.lim.1 (hval hκ y) hy (hval hκ x) hxy
  · exact hμ.sub (hval hκ y) (hval hκ x) hy ⟨κ, hκ.lim.1, hval_mem hκ x⟩ (fun z hz => by
      obtain ⟨c, rfl, hc⟩ := hlift hκ hz
      exact hxy c hc)
  · obtain ⟨b, hb, hbu⟩ := hμ.bd (hval hκ ((levHost hκ).dom f)) (hval hκ f) hd
      ⟨κ, hκ.lim.1, hval_mem hκ f⟩ (fun u hu => by
        obtain ⟨c, rfl, hc⟩ := hlift hκ hu
        obtain ⟨e, he⟩ := (levHost hκ).mem_dom.mp hc
        refine ⟨hval hκ e, hran c e he, ?_⟩
        rw [← op_val hκ]
        exact (levHost hκ).app_iff.mp he)
    refine ⟨hmk hκ b (hsubκ b hb), hb, fun a e hae => ?_⟩
    obtain ⟨v, hvb, hv⟩ := hbu (hval hκ a) ((levHost hκ).mem_dom.mpr ⟨e, hae⟩)
    have hvκ : v ∈ Lev κ := hsubκ v (lev_tr hμ.lim.1 b hb v hvb)
    have hae' : (levHost hκ).App f a (hmk hκ v hvκ) := (levHost hκ).app_iff.mpr (by
      show hval hκ ((levHost hκ).op a (hmk hκ v hvκ)) ∈ hval hκ f
      rw [op_val hκ]
      exact hv)
    rw [hf.2 a e (hmk hκ v hvκ) hae hae']
    exact hvb
  · have ha' : hval hκ a ∈ Lev μ := ha
    obtain ⟨β, hβ, hc⟩ := ltL_cover hμ.lim.1 ha'
    obtain ⟨Q, hQc, hQ⟩ := exists_ltSet (lim_big hμ.lim)
    have hscβ : Ord (sc β) := ord_sc (ord_mem hμ.lim.1 hβ)
    have hLβ : Lev (sc β) ∈ Lev μ := lev_mem hμ.lim.1 (hμ.lim.2.2 β hβ)
    have hac : Con (hval hκ a) := ⟨μ, hμ.lim.1, ha'⟩
    obtain ⟨γ, hγ, h1, h2, h3⟩ := con_big3 hQc hac (con_lev hscβ)
    obtain ⟨S, hS, hSz⟩ := sep_good_bdef (closed_true (V := V)) (k := 3)
      ((BDef.mem 0 1).and (prB.comp ![2, 0, 3])) (good_of_con (con_lev hγ.1)) (lev_tr hγ.1)
      ![Lev (sc β), Q, hval hκ a] (by
        intro j
        match j with
        | 0 => exact ⟨h3, good_of_con (con_lev hscβ)⟩
        | 1 => exact ⟨h1, good_of_con hQc⟩
        | 2 => exact ⟨h2, good_of_con hac⟩)
    have hSz' : ∀ z, z ∈ S ↔ z ∈ Lev γ ∧ (z ∈ Lev (sc β) ∧ Pr Q z (hval hκ a)) := hSz
    have hSμ : S ∈ Lev μ := hμ.sub (Lev (sc β)) S hLβ (con_of_good hS)
      (fun z hz => ((hSz' z).mp hz).2.1)
    refine ⟨hmk hκ S (hsubκ S hSμ), hSμ, fun y => ?_⟩
    show hval hκ y ∈ S ↔ hval hκ y ∈ Lev μ ∧ LtL (hval hκ y) (hval hκ a)
    rw [hSz']
    constructor
    · rintro ⟨-, hyβ, hpr⟩
      have hyμ : hval hκ y ∈ Lev μ := lev_mono hμ.lim.1 (hμ.lim.2.2 β hβ) _ hyβ
      exact ⟨hyμ, (hQ _ _ hyμ ha').mp hpr⟩
    · rintro ⟨hyμ, hlt⟩
      have hyβ := hc _ hlt
      exact ⟨lev_tr hγ.1 _ h3 _ hyβ, hyβ, (hQ _ _ hyμ ha').mpr hlt⟩
  · show hval hκ (levHost hκ).om ∈ Lev μ
    rw [om_val hκ]
    exact ord_mem_lev_lim hμ.lim om hμ.omega

end closed

end host

end MH

end FFL.FirstOrder.SetTheory
