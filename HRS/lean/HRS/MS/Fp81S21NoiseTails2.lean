import HRS.MS.Fp81S21NoiseTails
import HRS.MS.Fp81S21GaussFeature3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.CovMeas
open HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- A single summable Hermite-coordinate profile controls every cutoff and
terminal time on every fixed horizon. Its finite-set tails vanish. -/
theorem fp81s21_movingNoise_coordinate_tails (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
        ∃ c : MultiIndex p.d → ℝ,
          (∀ α, 0 ≤ c α) ∧
          Summable (fun α => c α ^ 2) ∧
          (∀ H : ℝ, 0 < H →
            ∀ u ∈ Icc (0 : ℝ) H,
            ∀ t ∈ Icc (0 : ℝ) H,
            ∀ α : MultiIndex p.d,
              ‖movingNoiseCoordinate R u t α‖ ^ 2 ≤
                (2 * p.β⁻¹) * H * c α ^ 2) ∧
          (∀ ε : ℝ, 0 < ε →
            ∃ S : Finset (MultiIndex p.d),
              ∑' α : {α : MultiIndex p.d // α ∉ S}, c α.1 ^ 2 < ε) := by
  obtain ⟨δ0, hδ0, hδ0half, huniform⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Co, co, hco, hsquare, hdata⟩ := huniform δ hδ hδle R
  let c : MultiIndex p.d → ℝ := fp81s21_uniform_orbit_coefficient p Co
  have hD1 : HRS.MS.CovMeas.S101Data (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) 1 (2 * p.d + 8) c := by
    simpa [c] using hdata 1 (by norm_num)
  have hcnonneg : ∀ α, 0 ≤ c α := hD1.nonneg
  have hcsummable : Summable (fun α => c α ^ 2) := by
    simpa [c] using hsquare
  refine ⟨c, hcnonneg, hcsummable, ?_, ?_⟩
  · intro H hH u hu t ht α
    have hD : HRS.MS.CovMeas.S101Data (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) c := hdata H hH
    have hcut := fp81s21_movingNoiseCoordinate_norm_le_zero_of_cutoff
      p R hδ (hδle.trans hδ0half) hH hu ht α
    have hbase := fp81s21_movingNoiseCoordinate_sq_bound_of_S101Data
      p R hδ (hδle.trans hδ0half) hH hD
      ⟨le_rfl, hH.le⟩ ht ht.1 α
    calc
      ‖movingNoiseCoordinate R u t α‖ ^ 2 ≤
          ‖movingNoiseCoordinate R 0 t α‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcut
      _ ≤ (2 * p.β⁻¹) * H * c α ^ 2 := hbase
  · intro ε hε
    let w : MultiIndex p.d → ℝ≥0 := fun α => ⟨c α ^ 2, sq_nonneg _⟩
    let ε₀ : ℝ≥0 := ⟨ε, hε.le⟩
    have hwsummable : Summable w := by
      exact (NNReal.summable_mk (fun α => sq_nonneg (c α))).2 hcsummable
    have htail := (NNReal.tendsto_tsum_compl_atTop_zero w).eventually
      (gt_mem_nhds (show (0 : ℝ≥0) < ε₀ from hε))
    obtain ⟨S, hS⟩ := htail.exists
    have hSreal : (↑(∑' α : {α : MultiIndex p.d // α ∉ S}, w α) : ℝ) <
        (ε₀ : ℝ) := NNReal.coe_lt_coe.mpr hS
    rw [NNReal.coe_tsum] at hSreal
    change (∑' α : {α : MultiIndex p.d // α ∉ S}, c α.1 ^ 2) < ε at hSreal
    exact ⟨S, hSreal⟩

/-- The common isonormal series handoff, including its iid sequence, retained
series convergence, and covariance identities used by the combined feature. -/
theorem fp81s21_movingNoise_common_source
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg) :
    ∃ (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (hP : IsProbabilityMeasure P)
      (e : ℕ → GaussianFeatureHilbert)
      (ξ : ℕ → Ω → ℝ) (W : GaussianFeatureHilbert → Ω → ℝ),
      (∀ h h' : GaussianFeatureHilbert,
        HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h')
          (inner ℝ h h')) ∧
      HRS.IsStdGaussianSeq P ξ ∧
      (∀ h, Measurable (W h)) ∧
      (∀ h, MemLp (W h) 2 P) ∧
      (∀ h, Tendsto (fun m : ℕ =>
        ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (∀ r t : ℝ, 0 ≤ r → 0 ≤ t →
        ∀ ψ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∫ ω, W (J (@fp81s21_combinedFeature p δ R hμ₀ Mg K hK r ψ)) ω *
              W (J (@fp81s21_combinedFeature p δ R hμ₀ Mg K hK t φ)) ω ∂P =
            HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ) ∧
      (∀ (n : ℕ) (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ),
        (∀ i, 0 ≤ τ i) →
        (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
        HRS.IsCenteredGaussian
          (P.map fun ω i =>
            W (J (@fp81s21_combinedFeature p δ R hμ₀ Mg K hK
              (τ i) (φ i))) ω)) := by
  exact fp81s21_combinedFeature_gaussianSeries p hδ hδhalf R hμ₀ hK

#print axioms fp81s21_movingNoise_coordinate_tails
#print axioms fp81s21_movingNoise_common_source

end HRS.Fp81.S21

end
