module

public import MHER
public import HostCountSound
public import CountPull

@[expose] public section

set_option autoImplicit false

/-!
# From a supply of sets in a model of `𝗠𝗛` to the consistency of `𝗡𝗙𝗖`

The host side of the proof, assembled.

* `Host.Tower.count_clauses`: in any host, a tower with `2R + 2` consecutive closed levels
  above a closed level, the last of which has the height of the tower as its ordinals, gives a
  truth assignment on the numbers of the host that satisfies the instances of N and of the nine
  clauses for the Axiom of Counting below `q`, for `R = 5q + 6`.
* `MH.supply_clauses`: in a model of `𝗠𝗛`, a supply of sets (`MHSupply.lean`) for `10q + 15`
  gives such a host and truth assignment.
* **`MH.consistent_nfc_of_supplies`**: if for every standard `q` some model of `𝗠𝗛` has a supply
  for `10q + 15`, then `𝗡𝗙𝗖` is consistent.

What is not proved here: that the model of `𝗠𝗛` that is interpreted in a model of `𝗡𝗙𝗨𝗜𝗖` has
these supplies.
-/

namespace Host

variable {H : Host}

/-- Dropping the first of a sequence of consecutive closed levels; it becomes the member of
the new first level. -/
theorem LevSeq.shift {Ms : ℕ → H.W} {C : H.W} {n : ℕ} (h : H.LevSeq Ms C (n + 1)) :
    H.LevSeq (fun j => Ms (j + 1)) (Ms 0) n :=
  ⟨fun j hj => h.closed (j + 1) (by omega), fun j hj => h.mem (j + 1) (by omega),
    fun j hj => h.cons (j + 1) (by omega), h.mem 0 (by omega)⟩

/-- The standard numbers, in the numbers of a host, are the numerals. -/
theorem Nm.val_cast : ∀ k : ℕ, ((k : ℕ) : Nm H).val = H.nmr k
  | 0 => by
    rw [Nat.cast_zero]
    rfl
  | k + 1 => by
    rw [Nat.cast_succ, Nm.val_succ, Nm.val_cast k]
    rfl

namespace Tower

/-- **The clauses from a tower with enough closed levels above it.** -/
theorem count_clauses (T : Tower H) (q : ℕ) {Ms : ℕ → H.W} {C : H.W}
    (hl : H.LevSeq Ms C ((5 * q + 6) + (5 * q + 6) + 1)) (hC : H.Closed C)
    (hd : H.ords (Ms ((5 * q + 6) + (5 * q + 6) + 1)) = T.d) :
    ∃ τ : H.Nm → Prop, NSat τ ((q : ℕ) : H.Nm) ∧ CSat τ ((q : ℕ) : H.Nm) := by
  have ar := H.arithNm
  obtain ⟨e, h1, h2⟩ := FlatM.count_sound (Fm := T.flat) H.arithNm T.flat_ax T.flat_cax hl hC
    (fun a ha h0 => ⟨H.mem_suc.mpr (Or.inl (show a ∈ T.d from by rw [← hd]; exact ha)), h0⟩)
    (q := ((q : ℕ) : H.Nm)) (R := ((5 * q + 6 : ℕ) : H.Nm)) (R2 := ((5 * q + 4 : ℕ) : H.Nm))
    (by
      rw [show (5 * q + 6 : ℕ) = 5 * q + 4 + 1 + 1 from by omega]
      simp only [Nat.cast_add, Nat.cast_one])
    (by
      rw [← Nm.val_cast]
      simp only [Nat.cast_add, Nat.cast_one])
    (fun i hi => by
      have h3 : i ≤ ((q : ℕ) : H.Nm) := le_trans (ar.nf.le_add i 1) hi
      have h4 := ar.nf.add_le_add_r (ar.nf.mul_le_mul_l h3 5) 6
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h4)
  exact ⟨_, h1, h2⟩

end Tower

end Host

namespace FFL.FirstOrder.SetTheory

namespace MH

section

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **In a model of `𝗠𝗛`, a supply of sets for `10q + 15` gives a host and a truth assignment on
its numbers that satisfies the instances of N and of the nine clauses below `q`.** -/
theorem supply_clauses (q : ℕ) {T : ℕ → V} {ρ Sq : V}
    (sup : Supply ((5 * q + 6) + (5 * q + 6) + 1 + 1 + 1) T ρ Sq) :
    ∃ (H : Host) (τ : H.Nm → Prop), NSat τ ((q : ℕ) : H.Nm) ∧ CSat τ ((q : ℕ) : H.Nm) := by
  obtain ⟨ν₀, K', hK', Tw, Ms, C, -, -, hseq, hords, -⟩ := supply_er sup
  exact ⟨levHost hK', Tw.count_clauses q hseq.shift (hseq.closed 0 (by omega)) hords⟩

end

/-- **`𝗡𝗙𝗖` is consistent if for every standard `q` some model of `𝗠𝗛` has a supply of sets for
`10q + 15`.** -/
theorem consistent_nfc_of_supplies
    (h : ∀ q : ℕ, ∃ (V : Type) (_ : SetStructure V) (_ : Nonempty V)
      (_ : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛) (T : ℕ → V) (ρ Sq : V),
      Supply ((5 * q + 6) + (5 * q + 6) + 1 + 1 + 1) T ρ Sq) :
    Entailment.Consistent 𝗡𝗙𝗖 :=
  consistent_nfc_of_hosts fun q => by
    obtain ⟨V, i1, i2, i3, T, ρ, Sq, sup⟩ := h q
    exact supply_clauses q sup

end MH

end FFL.FirstOrder.SetTheory
