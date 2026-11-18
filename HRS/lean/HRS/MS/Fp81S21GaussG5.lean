import HRS.MS.Fp81S21GaussUnif2
import HRS.MS.Fp81S21WickApprox18

/-! Actual two-time Gaussian law of the weak chart coefficient increment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A weak-chart moment representative inherits the centered Gaussian law of
its two-time coordinate differences from the actual physical realization. -/
theorem fp81s21_g5_coord_increment_centered
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (G : GaussianRealization R) (q : ℝ → G.Ω → r26t6_Coeff) (M : ℝ)
    (hq : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) q M)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (j : ℕ) :
    HRS.IsCenteredGaussian (G.P.map (fun ω => q u ω j - q v ω j)) := by
  let φ : Euc p.d → ℝ := E.test j
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    r2Test_isOscTest _ (E.test_smooth j)
  let T : ℝ := max u v + 1
  let τ : Fin 2 → ℝ := fun i => if i = 0 then u else v
  let V : G.Ω → EuclideanSpace ℝ (Fin 2) := fun ω =>
    WithLp.toLp 2 fun i => OscDual.eval (G.Z (τ i) ω) φ
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i k =>
    HRS.Whole.linearGaussianCov (r26t3_coeff R) p.β⁻¹
      (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ) (τ i) (τ k) φ φ
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    EuclideanSpace.proj 0 - EuclideanSpace.proj 1
  have hτ : ∀ i : Fin 2, τ i ∈ Icc (0 : ℝ) T := by
    have huT : u ≤ T := by dsimp [T]; linarith [le_max_left u v]
    have hvT : v ≤ T := by dsimp [T]; linarith [le_max_right u v]
    intro i
    fin_cases i
    · simpa [τ] using (show u ∈ Icc (0 : ℝ) T from ⟨hu, huT⟩)
    · simpa [τ] using (show v ∈ Icc (0 : ℝ) T from ⟨hv, hvT⟩)
  have hLaw : G.P.map V = multivariateGaussian 0 S := by
    simpa [V, S, HRS.Whole.linearGaussianCov, r26t3_coeff, r26t3_mu] using
      (G.evolution T).gaussian 2 τ (fun _ => φ) hτ (fun _ => hφ)
  have hVm : Measurable V := by
    apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    apply measurable_pi_iff.2
    intro i
    have heq : (fun ω => OscDual.eval (G.Z (τ i) ω) φ) =
        gaussianOscEval (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d
          (wholeSpaceIndex p.d : ℝ)) ∘ G.Z (τ i) := by
      funext ω
      exact (gaussianOscEval_apply ⟨φ, hφ⟩ _).symm
    rw [heq]
    exact (gaussianOscEval (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d
      (wholeSpaceIndex p.d : ℝ))).continuous.measurable.comp ((G.evolution T).meas (τ i))
  have hcenter : HRS.IsCenteredGaussian (G.P.map V) := by
    rw [hLaw]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg 2 S
  have hmap : G.P.map (fun ω => L (V ω)) = (G.P.map V).map L := by
    rw [Measure.map_map L.continuous.measurable hVm]
    rfl
  have hdiff : HRS.IsCenteredGaussian (G.P.map (fun ω => L (V ω))) := by
    rw [hmap]
    exact HRS.MS.R26T3.s21g2_s12_cg_map hcenter L
  have hcoord (w : ℝ) (hw : 0 ≤ w) :
      ∀ᵐ ω ∂G.P, q w ω j = OscDual.eval (G.Z w ω) φ := by
    filter_upwards [(hq.2 w hw).2.2] with ω hω
    rw [← fp81s21_chartAction_test_coordinate E (q w ω) j]
    exact hω.1 (E.test j) (E.test_smooth j)
  have hae : (fun ω => q u ω j - q v ω j) =ᵐ[G.P] (fun ω => L (V ω)) := by
    filter_upwards [hcoord u hu, hcoord v hv] with ω hωu hωv
    simp [L, V, τ, hωu, hωv]
  rw [Measure.map_congr hae]
  exact hdiff

#print axioms fp81s21_g5_coord_increment_centered
end HRS.Fp81.S21
end
