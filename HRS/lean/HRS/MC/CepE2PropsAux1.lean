import HRS.MC.CepE2

/-!
# Packet CEPE2PROPS, auxiliary 1: diagonal translation, `C¹` from a continuous gradient, periodicity of Moreau envelopes
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2Props

open HRS.MC.CepE1 HRS.MC.CepE2

/-- Copy of `HRS.MC.Cepa.cep_diag`. -/
def cep_diag (N : ℕ) : Ch N := WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)

variable {N : ℕ}

theorem cepe2p_add_smul_diag_apply (z : Ch N) (c : ℝ) (k : Fin N) :
    (z + c • cep_diag N) k = z k + c := by
  simp [cep_diag]

theorem cepe2p_alcove_add_iff (z : Ch N) (c : ℝ) : z + c • cep_diag N ∈ cep_Alcove N ↔ z ∈ cep_Alcove N := by
  simp only [cep_Alcove, mem_setOf_eq, cepe2p_add_smul_diag_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k l hkl => by linarith [h1 k l hkl], fun k l => by linarith [h2 k l]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k l hkl => by linarith [h1 k l hkl], fun k l => by linarith [h2 k l]⟩

theorem cepe2p_pot_add (a : ℝ) (z : Ch N) (c : ℝ) :
    cep_chamberPot a N (z + c • cep_diag N) = cep_chamberPot a N z := by
  simp only [cep_chamberPot, cepe2p_add_smul_diag_apply]
  congr 3 <;> ext k <;> congr 1 <;> ext l <;> split_ifs <;> simp

theorem cepe2p_env_add_le {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) (c : ℝ) :
    cepe2_env ha n (z + c • cep_diag N) ≤ cepe2_env ha n z := by
  obtain ⟨hA, -⟩ := cepe2_J_spec ha hn z
  have h := cepe2_env_min ha hn (z + c • cep_diag N)
    (y := cepe2_J ha n z + c • cep_diag N) ((cepe2p_alcove_add_iff _ c).2 hA)
  rw [cepe2p_pot_add] at h
  rw [cepe2_env_eq ha hn z]
  have e : z + c • cep_diag N - (cepe2_J ha n z + c • cep_diag N) = z - cepe2_J ha n z := by abel
  rw [e] at h
  exact h

theorem cepe2p_env_add {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) (c : ℝ) :
    cepe2_env ha n (z + c • cep_diag N) = cepe2_env ha n z := by
  refine le_antisymm (cepe2p_env_add_le ha hn z c) ?_
  have := cepe2p_env_add_le ha hn (z + c • cep_diag N) (-c)
  rwa [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at this

/-- `C¹` from a pointwise gradient that depends continuously on the point. -/
theorem cepe2p_contDiff_of_hasGradientAt {f : Ch N → ℝ} {g : Ch N → Ch N} (hg : Continuous g)
    (h : ∀ z, HasGradientAt f (g z) z) : ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun z => InnerProductSpace.toDual ℝ (Ch N) (g z), ?_, fun z => (h z).hasFDerivAt⟩
  exact (InnerProductSpace.toDual ℝ (Ch N)).continuous.comp hg

end HRS.MC.CepE2Props
