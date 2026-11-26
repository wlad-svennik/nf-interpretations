module

public import NFConsistentViaNFU

set_option autoImplicit false

@[expose] public section

namespace Palomar

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- A set-sized NF model obtained from the uploaded Jensen NFU model and the
uploaded interpretation of NF in NFU + Infinity. -/
theorem exists_nf_model :
    ∃ (V : Type) (mem : V → V → Prop), ConNF.NF.IsNF V mem := by
  obtain ⟨V, mem, h, hinf⟩ := JensenNFU.exists_model
  letI : Nonempty V := by
    obtain ⟨y, -⟩ := h.comprehension 0 [] (JensenNFU.TFm.eq 0 0) ⟨0, rfl, rfl⟩ [] rfl
    exact ⟨y⟩
  letI : SetStructure V := ⟨fun y x ↦ mem x y⟩
  letI : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := Jensen.models_nfui_of_isNFU h hinf
  let U : Type := setTranslation.Model V
  letI : U↓[ℒₛₑₜᵤ] ⊧* 𝗡𝗙𝗨𝗜ₛ := setModel_models_nfus (M := V)
  exact ⟨SetTheoryU.nfTranslation.Model U,
    fun a b ↦ Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b],
    SetTheoryU.nfModel_isNF (M := U)⟩

end Palomar

#print axioms Palomar.exists_nf_model
#print axioms NFUCut.nf_nfu_inf_mutually_interpretable
