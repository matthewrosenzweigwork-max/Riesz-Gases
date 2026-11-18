import HRS.Main.ThermLinAux2
import HRS.Main.T25PAux11
import HRS.Sections.AdjKAFinal
import HRS.Sections.AdjKGlue
import HRS.Uniform.Q45Gauss
import HRS.Uniform.Q54cAux36
import HRS.Sections.Q40bAux2
import HRS.Sections.AdjKDAux1

/-!
# THERMLIN, part 3: existence of the prepared linear process (Proposition A.33 at level `m`, with continuous paths)

Construction: on `Ω' = E_m × Ω_G` with `P' = ν ⊗ P_G`, `Y₀ = pr₁`, `Ω_G` carrying a continuous Gaussian Hilbert
martingale `G` with covariation density `covDensT` (`Q45.exists_gaussian_martingale`), `Zs` its stochastic
convolution against the dual evolution `V` (`adjk_evolution_moment_proof`, with a continuous version), `Zm` a
measurable modification (`thermlin_measurable_version`) and `Y^t = V^{t,0} Y₀ + Zm^t`.  The Gaussian clause is
`T25P.t25p_Zb_gaussian` and `T25P.t25p_cov_eq` (law identification of the stochastic convolution).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- `IsStochConv` is invariant under a.e. modification of the convolution. -/
theorem thermlin_isStochConv_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {M : ℝ → Ω → H} {a t : ℝ} {Z Z' : Ω → E}
    (h : IsStochConv P VE j M a t Z) (hZ : Z' =ᵐ[P] Z) : IsStochConv P VE j M a t Z' := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hl hmono hmesh => ?_⟩
  have := hh n r h0 hl hmono hmesh
  have e : ∫⁻ ω, ‖Z' ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hZ] with ω hω
    rw [hω]
  rw [e]
  exact this

/-- The covariation density of the stochastic convolution noise is a deterministic covariance density
(copy of `T25P.t25p_detCov`). -/
theorem thermlin_detCov {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} (hd : 2 ≤ d)
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {T' : ℝ}
    (hT' : 0 < T') : IsDetCovDensity T' (covDensT m β⁻¹ T' ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hMF := Q40b.q40b_meanField hd1 htr hT'
  have hjc := Q40b.q40b_jointCont hd1 htr T'
  have hprob : ∀ σ ∈ Set.Icc (0 : ℝ) T', IsProbDensity (ρ σ) := fun σ hσ => hMF.density σ hσ
  have hcts : ∀ σ ∈ Set.Icc (0 : ℝ) T', Continuous (ρ σ) := fun σ hσ =>
    hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hσ, Set.mem_univ _⟩)
  have hweak := adjkd_weak_cont hd htr T'
  exact Q54c.isDetCovDensity_covDens hm (inv_nonneg.2 htr.hβ.le) hprob hweak hcts

end HRS.ThermLin
