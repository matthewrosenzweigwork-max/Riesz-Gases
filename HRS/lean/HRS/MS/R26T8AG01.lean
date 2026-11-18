import HRS.MS.R26T8AG01m

/-!
# S8.2 observed-time layer, packet T8A.G01: graph cutoffs with pole-envelope derivative bounds

`θ_n = (∏_i (1 - ψ(m⁻² ‖X_i‖²))) · ∏_{i<j} ψ(m² ‖X_i - X_j‖²)` with `m = n + 1` and `ψ` the smooth transition
`ψ t = smoothTransition((t-1)/3)`.  Each `θ_n` is smooth with compact support away from the collision set, takes values
in `[0,1]`, is eventually one near every collision-free point, and its first two derivatives are bounded by a fixed
multiple of the pole envelope (uniformly in `n`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_graph_cutoffs (d N : ℕ) :
    ∃ theta : ℕ → EucConfig d N → ℝ,
      (∀ n, ContDiff ℝ ∞ (theta n) ∧ HasCompactSupport (theta n) ∧
        tsupport (theta n) ⊆ (eucCollisionSet d N)ᶜ) ∧
      (∀ n X, 0 ≤ theta n X ∧ theta n X ≤ 1) ∧
      (∀ X, X ∉ eucCollisionSet d N → ∀ᶠ n in atTop, theta n =ᶠ[𝓝 X] (fun _ => 1)) ∧
      ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ n X, X ∉ eucCollisionSet d N →
        ‖fderiv ℝ (theta n) X‖ + ‖iteratedFDeriv ℝ 2 (theta n) X‖ ≤ C * r26t8a_configPoleEnvelope M X := by
  refine ⟨r26t8a_g01_theta d N, fun n => ⟨r26t8a_g01_theta_contDiff d N n,
    r26t8a_g01_theta_compact d N n, r26t8a_g01_theta_tsupport d N n⟩,
    fun n X => r26t8a_g01_theta_bounds d N n X, fun X hX => r26t8a_g01_theta_eventually d N X hX, ?_⟩
  obtain ⟨C, hC, hb⟩ := r26t8a_g01m_theta_bd d N
  refine ⟨C, 2, hC, by norm_num, fun n X hX => ?_⟩
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
  exact hb n X hX

end HRS.MS.R26T8A

end
