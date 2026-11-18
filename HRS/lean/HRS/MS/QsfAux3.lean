import HRS.MS.QsfAux2
import HRS.Energy.StaticLimitGauss
import HRS.MS.ThCorrSmAux2

/-!
# S4.5 packet A3: `exists_gaussian_feature`

`HRS.MS.Qsf`-free: namespace `S45`.  `S45.exists_gaussian_feature_proof` has exactly the type of the frozen
`HRS.Whole.exists_gaussian_feature` (tie in `QsfTie.lean`).

Proof: `s45_kdata` (Q34 chain for `s > 0`; log kernel with `HasLogMoment2` for `s = 0`) gives the operator `K`;
conjunct 1 is `s45_exists_response` for `ψ ∈ C_b^J ⊆ L²(μ)`; conjunct 2 is `s45_exists_gaussian` on `ℓ²` with the
standard Hilbert basis and `U_i = P_μ φ_i` (`‖U_i‖ ≤ 2 ‖φ_i‖_{C_b^J}` is summable), the coordinates being
`SeqL2.coord z i = ⟪e_i, z⟫`, and `s45_susceptibilityCov_eq`.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole HRS.Whole.Q34 HRS.MS.Thm HRS.MS.TcR
open HRS (Euc cbNorm MemCb smoothDist law IsCenteredGaussian)

variable {d : ℕ}

/-! ### The standard Hilbert basis of `SeqL2` -/

/-- The identity isometry `SeqL2 ≃ ℓ²`. -/
def s45_seqRepr : SeqL2 ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun := id
  invFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  norm_map' := fun _ => rfl

/-- The standard Hilbert basis `e_i` of `ℓ²`. -/
def s45_seqBasis : HilbertBasis ℕ ℝ SeqL2 := HilbertBasis.ofRepr s45_seqRepr

theorem s45_inner_seqBasis (i : ℕ) (z : SeqL2) : ⟪s45_seqBasis i, z⟫ = SeqL2.coord z i := by
  have h := HilbertBasis.repr_apply_apply s45_seqBasis z i
  rw [← h]
  rfl

instance s45_secondCountable_seq : SecondCountableTopology SeqL2 := by
  have : TopologicalSpace.SeparableSpace SeqL2 := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  exact UniformSpace.secondCountable_of_separable _

/-! ### The classes `P_ν φ_i` and their norms -/

theorem s45_U_norm_le {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {ψ : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) {B : ℝ} (hB : ∀ x, ‖ψ x‖ ≤ B) : ‖s45_U ψ hψ‖ ≤ 2 * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hp : |pair ν ψ| ≤ B := HRS.MS.Tc5.tc5_pair_le hB
  have h := Lp.norm_le_of_ae_bound (f := s45_U ψ hψ) (C := 2 * B) (by linarith)
    (by
      filter_upwards [s45_U_ae hψ] with x hx
      rw [hx]
      unfold projMean
      rw [Real.norm_eq_abs]
      calc |ψ x - pair ν ψ| ≤ |ψ x| + |pair ν ψ| := abs_sub _ _
        _ ≤ 2 * B := by
          have := hB x
          rw [Real.norm_eq_abs] at this
          linarith)
  simpa [measureUnivNNReal] using h

/-- **S4.5, `exists_gaussian_feature`.** -/
theorem exists_gaussian_feature_proof : type_of% @HRS.Whole.exists_gaussian_feature := by
  intro d s hd hs0 hsd J hJ ρ hρ M hM γ₀ hγ₀ φ hφ L hL
  haveI := isProbabilityMeasure_nu hρ
  obtain ⟨K, hK⟩ := s45_kdata (by omega) hs0 hsd hρ hM hL
  have hmem : ∀ ψ : Euc d → ℝ, MemCb J ψ → MemLp ψ 2 (withDensityReal ρ) :=
    fun ψ hψ => HRS.MS.Tc5.tc5_memLp_of_cb hψ
  refine ⟨fun ψ hψ => s45_exists_response hK hγ₀ (hmem ψ hψ), ?_⟩
  have hφm : ∀ i, MemLp (φ i) 2 (withDensityReal ρ) := fun i => hmem _ (hφ.1 i)
  have hU : Summable fun i => ‖s45_U (φ i) (hφm i)‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
      (hφ.2.mul_left 2)
    exact s45_U_norm_le (hφm i) fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 i) x
  obtain ⟨γ, hp, hg, hcov⟩ := s45_exists_gaussian hK hγ₀.le s45_seqBasis hU
  refine ⟨γ, ⟨hg, fun i j => ?_⟩⟩
  obtain ⟨hi, hv⟩ := hcov i j
  simp only [s45_inner_seqBasis] at hi hv
  exact ⟨hi, hv.trans (s45_susceptibilityCov_eq hK hγ₀ (hφm i) (hφm j)).symm⟩

end S45

end
