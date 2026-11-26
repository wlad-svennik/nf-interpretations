module

public import HostER

@[expose] public section

set_option autoImplicit false

/-!
# The partition theorem for an exponent that is a number of the host

`HostER.lean` proves the partition theorem of Erdős and Rado in a host by an induction in Lean
on the exponent, along a sequence of levels given as a function on the standard numbers. Here
the sequence of consecutive closed levels is a function of the host on `n + 1`, for a number
`n` of the host that may be nonstandard, and the induction is an induction in the host. The
step is `ERCtx.succ` of `HostER.lean`, which holds for every number of the host.

* `LevSeqI Ms C n`: `Ms` gives consecutive closed levels at `0, …, n`, and `C` is a member of
  the first.
* `erI`: every colouring of the sets of `j` ordinals of the level at `j ≤ n`, with colours in
  `C`, has a homogeneous set of ordinals of that level with a member and without a largest
  member.
* `er_seqI`: hence a homogeneous increasing sequence of every length that is a number of the
  host.

This is needed for the interpretation `𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗡𝗙𝗖`, where the bound `q` on the atoms, and so
the exponent `10q + 13`, range over a cut of the numbers of the model.
-/

namespace Host

variable {H : Host}

/-- **A sequence of consecutive closed levels, given by a function of the host** on `n + 1`:
every member of a level maps one-to-one into the level before, by a function of the host. `C`
is a member of the first level. -/
structure LevSeqI (H : Host) (Ms C n : H.W) : Prop where
  n_om : n ∈ H.om
  tot : ∀ j, j ∈ H.suc n → ∃ M, H.App Ms j M
  closed : ∀ j M, j ∈ H.suc n → H.App Ms j M → H.Closed M
  mem : ∀ j M M', j ∈ n → H.App Ms j M → H.App Ms (H.suc j) M' → M ∈ M'
  cons : ∀ j M M', j ∈ n → H.App Ms j M → H.App Ms (H.suc j) M' → ∀ x, x ∈ M' →
    ∃ g, H.IsFun g ∧ (∀ a, a ∈ x → ∃ c, c ∈ M ∧ H.App g a c) ∧
      ∀ a a' c, a ∈ x → a' ∈ x → H.App g a c → H.App g a' c → a = a'
  hC : ∀ M, H.App Ms H.emp M → C ∈ M

/-- **The partition theorem, for an exponent that is a number of the host.** -/
theorem erI {Ms C n : H.W} (hl : H.LevSeqI Ms C n) :
    ∀ j, j ∈ H.suc n → ∀ M, H.App Ms j M → C ∈ M ∧ ∀ col, H.ColOn col j (H.ords M) C →
      ∃ X, (∀ x, x ∈ X → x ∈ H.ords M) ∧ H.Large X ∧ H.HomC col j X := by
  have hd := H.def_incSeq
  have h0n : H.emp ∈ H.suc n := by
    rcases H.on_emp_mem_or (H.om_on hl.n_om) with h | h
    · exact H.mem_suc.mpr (Or.inr h.symm)
    · exact H.mem_suc.mpr (Or.inl h)
  have key := H.om_ind (fun j => j ∈ H.suc n → ∀ M, H.App Ms j M → (C ∈ M ∧ ∀ col,
      (H.IsFun col ∧ ∀ B, H.Card B j → (∀ z, z ∈ B → z ∈ M ∧ H.On z) →
        ∃ c, c ∈ C ∧ H.App col B c) →
      ∃ X, (∀ x, x ∈ X → x ∈ M ∧ H.On x) ∧ H.Large X ∧ H.HomC col j X)) (by hdef)
    (by
      intro _ M hM
      have hcl := hl.closed H.emp M h0n hM
      refine ⟨hl.hC M hM, fun col hcol => ⟨H.ords M, fun x hx => H.mem_ords.mp hx,
        ⟨⟨H.emp, H.mem_ords.mpr ⟨hcl.emp_mem, H.on_emp⟩⟩,
          fun x hx => ⟨H.suc x, H.ords_suc hcl hx, H.mem_suc.mpr (Or.inr rfl)⟩⟩,
        fun B B' c c' hB hB' _ _ hc hc' => ?_⟩⟩
      rw [H.card_emp_iff.mp hB] at hc
      rw [H.card_emp_iff.mp hB'] at hc'
      exact hcol.1.2 _ c c' hc hc')
    (by
      intro j hjom ih hsj M' hM'
      have hjn : j ∈ n := by
        rcases H.mem_suc.mp hsj with h | h
        · exact H.om_mem_trans hl.n_om h (H.mem_suc.mpr (Or.inr rfl))
        · rw [← h]
          exact H.mem_suc.mpr (Or.inr rfl)
      have hjs : j ∈ H.suc n := H.mem_suc.mpr (Or.inl hjn)
      obtain ⟨M, hM⟩ := hl.tot j hjs
      obtain ⟨hCM, ihM⟩ := ih hjs M hM
      have hMM' := hl.mem j M M' hjn hM hM'
      have hcl' := hl.closed (H.suc j) M' hsj hM'
      refine ⟨hcl'.trans C M hCM hMM', fun col hcol => ?_⟩
      have cx : H.ERCtx M M' C j col :=
        { hM := hl.closed j M hjs hM
          hM' := hcl'
          hMM' := hMM'
          cons := hl.cons j M M' hjn hM hM'
          hC := hCM
          hr := hjom
          hcol := hcol.1
          ctot := fun B hB hBs => hcol.2 B hB fun z hz => H.mem_ords.mp (hBs z hz) }
      obtain ⟨X, hX, hL, hh⟩ := cx.succ fun col₁ hcol₁ => by
        obtain ⟨X, hX, hL, hh⟩ := ihM col₁
          ⟨hcol₁.1, fun B hB hBs => hcol₁.2 B hB fun z hz => H.mem_ords.mpr (hBs z hz)⟩
        exact ⟨X, fun x hx => H.mem_ords.mpr (hX x hx), hL, hh⟩
      exact ⟨X, fun x hx => H.mem_ords.mp (hX x hx), hL, hh⟩)
  intro j hj M hM
  have hjom : j ∈ H.om := by
    rcases H.mem_suc.mp hj with h | h
    · exact H.mem_om_of_mem hl.n_om h
    · rw [h]
      exact hl.n_om
  obtain ⟨hC, h⟩ := key j hjom hj M hM
  refine ⟨hC, fun col hcol => ?_⟩
  obtain ⟨X, hX, hL, hh⟩ := h col
    ⟨hcol.1, fun B hB hBs => hcol.2 B hB fun z hz => H.mem_ords.mpr (hBs z hz)⟩
  exact ⟨X, fun x hx => H.mem_ords.mpr (hX x hx), hL, hh⟩

/-- **The partition theorem, for sequences and an exponent that is a number of the host.** -/
theorem er_seqI {Ms C n M : H.W} (hl : H.LevSeqI Ms C n) (hM : H.App Ms n M) {col : H.W}
    (hcol : H.ColOn col n (H.ords M) C) {k : H.W} (hk : k ∈ H.om) :
    ∃ s, H.IncSeq s k ∧ (∀ i a, H.App s i a → a ∈ H.ords M) ∧
      ∀ B B' c c', H.Card B n → H.Card B' n → H.SubV B s → H.SubV B' s →
        H.App col B c → H.App col B' c' → c = c' := by
  obtain ⟨X, hXsub, hXL, hXhom⟩ :=
    (H.erI hl n (H.mem_suc.mpr (Or.inr rfl)) M hM).2 col hcol
  obtain ⟨s, hs, hsX⟩ := H.large_seq hXL (fun x hx => (H.mem_ords.mp (hXsub x hx)).2) k hk
  refine ⟨s, hs, fun i a h => hXsub a (hsX i a h), fun B B' c c' hB hB' hBs hBs' hc hc' => ?_⟩
  exact hXhom B B' c c' hB hB'
    (fun z hz => by
      obtain ⟨j, hj⟩ := hBs z hz
      exact hsX j z hj)
    (fun z hz => by
      obtain ⟨j, hj⟩ := hBs' z hz
      exact hsX j z hj) hc hc'

end Host
