module

public import MHEnum

@[expose] public section

set_option autoImplicit false

/-!
# A tower of ordinal height in a level of the constructible sets

In a model of `𝗠𝗛`. **`exists_level_tower`**: let `d` be a nonzero ordinal and let there be a
ladder of sets (`Ladder`, `MHEnum.lean`) indexed by the ordinals up to `d + 1`, with a base
`γ₀` above `d + 1`. Then there are a full height `K'` and a tower (`Tower`, `Host.lean`) of
height `d` in the host `levHost` at `K'`.

The ladder of closed levels of the tower is the constructible set `Lam` of `exists_ladder`: its
values are levels at full heights (closed levels by `closed_lev`), each a member of the next,
each with `d + 1` as a member. The host is the level at a full height above the one that
bounds the ladder.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section ladder

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem hval_inj {κ : V} (hκ : Full κ) (a b : (levHost hκ).W) (h : hval hκ a = hval hκ b) :
    a = b := Subtype.ext h

/-- **A ladder of sets up to `d + 1` gives a tower of height `d`** in every level of the
constructible sets at a full height above the full height `K` of the top of the ladder. -/
theorem exists_level_tower_at {Sq U γ₀ d : V} (hd : Ord d) (hd0 : d ≠ ∅) (hγ₀ : Ord γ₀)
    (hdγ : sc d ∈ γ₀) (lad : Ladder (sc (sc d)) Sq U γ₀) :
    ∃ K : V, HgtF U K ∧ ∀ (K' : V) (hK' : Full K'), K ∈ K' →
      ∃ T : Host.Tower (levHost hK'), hval hK' T.d = d ∧ d ∈ K' := by
  have hθ : Ord (sc (sc d)) := ord_sc (ord_sc hd)
  obtain ⟨K, Lam, hK, hLamc, hLamsub, hLamf, hLammono, hKF, -⟩ := exists_ladder' hθ hγ₀ lad
  refine ⟨K, hKF, fun K' hK' hKK' => ?_⟩
  have hK'O := hK'.lim.1
  have hdθ : d ∈ sc (sc d) := mem_sc.mpr (Or.inr (self_mem_sc d))
  obtain ⟨μ₀, hμ₀K, -, hγμ₀, -⟩ := hLamf d hdθ
  have hγK : γ₀ ∈ K := hK.lim.1.1 μ₀ hμ₀K γ₀ hγμ₀
  have hscdK : sc d ∈ K := hK.lim.1.1 γ₀ hγK (sc d) hdγ
  have hθK : ∀ α, α ∈ sc (sc d) → α ∈ K := by
    intro α hα
    rcases mem_sc.mp hα with e | e
    · rw [e]
      exact hscdK
    · exact hK.lim.1.1 (sc d) hscdK α e
  have hθLK : ∀ α, α ∈ sc (sc d) → α ∈ Lev K :=
    fun α hα => ord_mem_lev_lim hK.lim α (hθK α hα)
  have hupK : ∀ x, x ∈ Lev K → x ∈ Lev K' := lev_mono hK'O hKK'
  have hLamK' : Lam ∈ Lev K' := hK'.sub (Lev K) Lam (lev_mem hK'O hKK') hLamc (fun q hq => by
    obtain ⟨α, hα, A, hA, e⟩ := mem_prodS.mp (hLamsub q hq)
    rw [e]
    exact kp_mem_lev_lim hK.lim hK.omega (hθLK α hα) hA)
  have hdK' : d ∈ Lev K' := hupK d (hθLK d hdθ)
  have hdomθ : ∀ α A, Pr Lam α A → α ∈ sc (sc d) := by
    intro α A h
    obtain ⟨α', hα', A', -, e⟩ := mem_prodS.mp (hLamsub _ (pr_iff.mp h))
    rw [(kp_inj e).1]
    exact hα'
  have happ : ∀ a b : (levHost hK').W, (levHost hK').App (hmk hK' Lam hLamK') a b ↔
      Pr Lam (hval hK' a) (hval hK' b) := by
    intro a b
    rw [(levHost hK').app_iff, pr_iff, ← op_val]
    exact Iff.rfl
  have hsuc2 : ∀ α : (levHost hK').W,
      α ∈ (levHost hK').suc ((levHost hK').suc (hmk hK' d hdK')) → hval hK' α ∈ sc (sc d) := by
    intro α hα
    have h : hval hK' α ∈ hval hK' ((levHost hK').suc ((levHost hK').suc (hmk hK' d hdK'))) :=
      hα
    rw [suc_val, suc_val] at h
    exact h
  have hOn : (levHost hK').On (hmk hK' d hdK') :=
    ⟨fun x y hxy hy => hd.1 (hval hK' y) hy (hval hK' x) hxy,
      fun y hy x z hxz hzy => hd.2 (hval hK' y) hy (hval hK' z) hzy (hval hK' x) hxz⟩
  have hne : hmk hK' d hdK' ≠ (levHost hK').emp := by
    intro e
    have h := congrArg (hval hK') e
    rw [emp_val] at h
    exact hd0 h
  have hFun : (levHost hK').IsFun (hmk hK' Lam hLamK') := by
    refine ⟨fun p hp => ?_, fun a b b' h1 h2 => ?_⟩
    · have hp' : hval hK' p ∈ Lam := hp
      obtain ⟨α, hα, A, hA, e⟩ := mem_prodS.mp (hLamsub _ hp')
      refine ⟨hmk hK' α (hupK α (hθLK α hα)), hmk hK' A (hupK A hA),
        (levHost hK').isOp_iff.mpr (hval_inj hK' _ _ ?_)⟩
      rw [op_val]
      exact e
    · have k1 := (happ a b).mp h1
      have k2 := (happ a b').mp h2
      obtain ⟨μ, -, -, -, hA⟩ := hLamf (hval hK' a) (hdomθ _ _ k1)
      exact hval_inj hK' _ _ (((hA _).mp k1).trans ((hA _).mp k2).symm)
  have hlev : ∀ α, α ∈ (levHost hK').suc ((levHost hK').suc (hmk hK' d hdK')) →
      α ≠ (levHost hK').emp → ∃ La, (levHost hK').App (hmk hK' Lam hLamK') α La ∧
        (levHost hK').Closed La := by
    intro α hα _
    obtain ⟨μ, hμK, hμfull, -, hA⟩ := hLamf (hval hK' α) (hsuc2 α hα)
    have hμK' : μ ∈ K' := hK'O.1 K hKK' μ hμK
    exact ⟨hmk hK' (Lev μ) (lev_mem hK'O hμK'), (happ _ _).mpr ((hA _).mpr rfl),
      closed_lev hK' hμfull hμK'⟩
  have hmono : ∀ α β La Lb, (levHost hK').App (hmk hK' Lam hLamK') α La →
      (levHost hK').App (hmk hK' Lam hLamK') β Lb → α ∈ β → La ∈ Lb :=
    fun α β La Lb h1 h2 hαβ => hLammono (hval hK' α) (hval hK' β) (hval hK' La) (hval hK' Lb)
      hαβ (hdomθ _ _ ((happ _ _).mp h2)) ((happ _ _).mp h1) ((happ _ _).mp h2)
  have hdmem : ∀ α La, α ∈ (levHost hK').suc ((levHost hK').suc (hmk hK' d hdK')) →
      α ≠ (levHost hK').emp → (levHost hK').App (hmk hK' Lam hLamK') α La →
      (levHost hK').suc (hmk hK' d hdK') ∈ La := by
    intro α La hα _ h
    obtain ⟨μ, -, hμfull, hγμ, hA⟩ := hLamf (hval hK' α) (hsuc2 α hα)
    have e : hval hK' La = Lev μ := (hA _).mp ((happ _ _).mp h)
    show hval hK' ((levHost hK').suc (hmk hK' d hdK')) ∈ hval hK' La
    rw [suc_val, e]
    exact ord_mem_lev_lim hμfull.lim (sc d) (hμfull.lim.1.1 γ₀ hγμ (sc d) hdγ)
  obtain ⟨T, hTd, -⟩ := (levHost hK').exists_tower (hmk hK' d hdK') (hmk hK' Lam hLamK') hOn hne
    hFun hlev hmono hdmem
  exact ⟨T, by rw [hTd]; rfl, hK'O.1 K hKK' d (hθK d hdθ)⟩

/-- **A ladder of sets up to `d + 1` gives a tower of height `d`** in a level of the
constructible sets. -/
theorem exists_level_tower {Sq U γ₀ d : V} (hd : Ord d) (hd0 : d ≠ ∅) (hγ₀ : Ord γ₀)
    (hdγ : sc d ∈ γ₀) (lad : Ladder (sc (sc d)) Sq U γ₀) :
    ∃ (K' : V) (hK' : Full K') (T : Host.Tower (levHost hK')), hval hK' T.d = d ∧ d ∈ K' := by
  obtain ⟨K, hKF, h⟩ := exists_level_tower_at hd hd0 hγ₀ hdγ lad
  obtain ⟨K', hK', hKK'⟩ := exists_full_above (hgtF_ord hKF)
  obtain ⟨T, h1, h2⟩ := h K' hK' hKK'
  exact ⟨K', hK', T, h1, h2⟩

end ladder

end MH

end FFL.FirstOrder.SetTheory
