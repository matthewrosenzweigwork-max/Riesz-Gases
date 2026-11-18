import HRS.MS.Fp81S21WickFam15
import HRS.MS.Fp81S21QuadPoly

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- A supplied half-Wick family is continuous on the full product L² space
and admits jointly measurable representatives correct at every nonnegative time. -/
theorem fp81s21_wickFam_supplied_wick_continuous_joint
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (K : ℝ)
    (G : GaussianRealization R)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P)
    (hgood : ∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ K,
      ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
        HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
        W u = fp81s21_wickFam_operator R G (T u) K hL hJoint)
    (hag : ∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
      (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P] fun ω => OscDual.eval (G.Z u ω) φ)
    (hcont : ∀ f, ContinuousOn (fun u => T u f) (Ici (0 : ℝ))) :
    ∀ k, ContinuousOn (fun u => W u k) (Ici (0 : ℝ)) ∧
      ∃ F : ℝ × G.Ω → ℝ, Measurable F ∧ ∀ u : ℝ, 0 ≤ u →
        MemLp (fun ω => F (u, ω)) 2 G.P ∧
        (fun ω => F (u, ω)) =ᵐ[G.P] (W u k : G.Ω → ℝ) := by
  classical
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hjoint : ∀ u : ℝ, 0 ≤ u → ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω) := by
    intro u hu
    obtain ⟨hL, hJ, hW⟩ := hgood u hu
    exact hJ
  have hb : ∀ u ∈ Ici (0 : ℝ), ‖W u‖ ≤ K ^ 2 / Real.sqrt 2 := by
    intro u hu
    obtain ⟨hL, hJ, hWu⟩ := hgood u (Set.mem_Ici.mp hu)
    rw [hWu]
    simpa [fp81s21_wickFam_operator, μ] using fp81s21_wickB311_operator_norm (T u) K hL hJ
  have hs : ∀ u ∈ Ici (0 : ℝ), ∀ k, W u k = W u (fp81s21_wickB23_symmetrize μ k) := by
    intro u hu k
    obtain ⟨hL, hJ, hWu⟩ := hgood u (Set.mem_Ici.mp hu)
    rw [hWu]
    simpa [fp81s21_wickFam_operator, μ] using fp81s21_wickB311_operator_symmetrize (T u) K hL hJ k
  have hgen : ∀ k ∈ fp81s21_wickB32_generators μ,
      ContinuousOn (fun u => W u k) (Ici (0 : ℝ)) := by
    intro k hk
    obtain ⟨n, c, φ, hdata, hkernel, rfl⟩ := hk
    have hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i) :=
      fun i => fp81s21_isOscTest_of_r2 hdata i
    have hφLp : ∀ i, MemLp (φ i) 2 μ := fun i =>
      (hdata.smooth i).continuous.memLp_of_hasCompactSupport (hdata.compactSupport i)
    obtain ⟨V, hV, hVa⟩ := fp81s21_wickFam_oscillator_polynomial_continuous p R G T
      hjoint hag hcont φ hφ hφLp c
    apply hV.congr
    intro u hu
    have hu0 : 0 ≤ u := Set.mem_Ici.mp hu
    obtain ⟨hL, hJ, hWu⟩ := hgood u hu0
    apply Lp.ext
    change (W u (hkernel.toLp (fp81s21_wickG_finite_rank_kernel φ c)) : G.Ω → ℝ) =ᵐ[G.P] (V u : G.Ω → ℝ)
    rw [hWu]
    have ha := fp81s21_wickFam_oscillator_finite_rank R G (T u) K hL hJ φ hφ c hkernel
    filter_upwards [ha, hVa u hu0] with ω ha' hv'
    exact ha'.trans hv'.symm
  have hc := fp81s21_wickFam_continuous_of_symmetric_generators μ G.P (Ici (0 : ℝ)) W
    (K ^ 2 / Real.sqrt 2) hb hs hgen
  intro k
  exact ⟨hc k, fp81s21_wickFam_joint_of_continuous G.P (fun u => W u k) (hc k)⟩

#print axioms fp81s21_wickFam_supplied_wick_continuous_joint
end HRS.Fp81.S21
end
