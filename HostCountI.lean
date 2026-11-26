module

public import HostERI
public import HostCountSound
public import HostArith

@[expose] public section

set_option autoImplicit false

/-!
# The clauses below a bound that is a number of the host

`MHCountSound.lean` has `Tower.count_clauses` for a standard bound `q`. Here `q` is any number
of the host: a tower with `10q + 14` consecutive closed levels above a closed level `C`, given
by a function of the host, the last of which has the height of the tower as its ordinals, gives
a *set of the host* whose members are the atoms true in a truth assignment that satisfies the
instances of N and of the nine clauses for the Axiom of Counting below `q`.
-/

namespace Host

variable {H : Host}

namespace Tower

/-- **The clauses from a tower with enough closed levels above it, for a bound that is a number
of the host.** -/
theorem count_clausesI (T : Tower H) (q : H.Nm) {Ms C M : H.W}
    (hl : H.LevSeqI Ms C ((5 * q + 6) + (5 * q + 6) + 1 : H.Nm).val)
    (hM : H.App Ms ((5 * q + 6) + (5 * q + 6) + 1 : H.Nm).val M)
    (hC : H.Closed C) (hd : H.ords M = T.d) :
    ∃ S : H.W, NSat (fun i : H.Nm => i.val ∈ S) q ∧ CSat (fun i : H.Nm => i.val ∈ S) q := by
  have ar := H.arithNm
  obtain ⟨e, h1, h2⟩ := FlatM.count_sound_gen (Fm := T.flat) H.arithNm T.flat_ax T.flat_cax
    (O := H.ords M) (nn := ((5 * q + 6) + (5 * q + 6) + 1 : H.Nm).val)
    (fun col hcol k hk => H.er_seqI hl hM hcol hk) hC
    (fun a ha h0 => ⟨H.mem_suc.mpr (Or.inl (show a ∈ T.d from by rw [← hd]; exact ha)), h0⟩)
    (q := q) (R := 5 * q + 6) (R2 := 5 * q + 4) (by ring) rfl
    (fun i hi => by
      have h3 : i ≤ q := le_trans (ar.nf.le_add i 1) hi
      exact ar.nf.add_le_add_r (ar.nf.mul_le_mul_l h3 5) 6)
  have hdt := T.flat.def_tr H.arithNm
  have hdi := H.def_incSeq
  have hda := (H.arithNm).def_Ad
  have hP : Def1 H (fun x => T.flat.AllT H.arithNm e x (5 * q + 6 : H.Nm).val) := by
    unfold FlatM.AllT Host.SubSeq
    hdef
  refine ⟨H.sepS H.om _ hP, NSat.congr (fun i _ => ?_) h1, CSat.congr (fun i _ => ?_) h2⟩
  · exact ⟨fun h => H.mem_sepS.mpr ⟨i.prop, h⟩, fun h => (H.mem_sepS.mp h).2⟩
  · exact ⟨fun h => H.mem_sepS.mpr ⟨i.prop, h⟩, fun h => (H.mem_sepS.mp h).2⟩

end Tower

end Host
