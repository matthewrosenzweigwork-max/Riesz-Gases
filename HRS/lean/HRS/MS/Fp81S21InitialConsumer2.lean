import HRS.MS.Fp81S21InitialConsumer
import HRS.MS.Fp81S21MainL2Bounded2
import HRS.MS.Fp81S21LargeShift6
import HRS.MS.Fp81S21IidGaussUniq2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3

/-- For positive coupling, bounded-start convergence and the exponential tail
combine into convergence uniform over every nonnegative start. -/
theorem fp81s21_initial_static_uniform_pos (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
          ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
            ∀ a : ℝ, 0 ≤ a →
              ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                IsCenteredGaussianSeq G (fun i j =>
                  HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
                    (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
                ∀ Φ : SeqL2 → ℝ, Φ ∈ CbUnitBall SeqL2 5 →
                  |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
                    (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
                    (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
                      ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                        fp81s21_initial_ellv R (r26t3_qwin R a) x,
                        fp81s21_initial_ellv R (r26t3_qwin R a) x]
                      ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_initial_main_l2_bounded_shift p hγ
  obtain ⟨δl, hδl, hδlh, hl⟩ := fp81s21_initial_large_shift p hγ
  let δ0 := min δb δl
  have hδ0 : 0 < δ0 := lt_min hδb hδl
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδbh
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R ε hε
  have hδb' : δ ≤ δb := hδle.trans (min_le_left _ _)
  have hδl' : δ ≤ δl := hδle.trans (min_le_right _ _)
  obtain ⟨C, c, hC, hc, hlarge⟩ := hl δ hδ hδl' R
  let L : ℝ := max (2 * C / ε) 1
  let A : ℝ := Real.log L / c
  have hL1 : 1 ≤ L := le_max_right _ _
  have hLpos : 0 < L := by linarith
  have hA : 0 ≤ A := div_nonneg (Real.log_nonneg hL1) hc.le
  have hExp : Real.exp (-c * A) = L⁻¹ := by
    rw [show -c * A = -Real.log L by
      dsimp [A]
      field_simp [hc.ne']]
    rw [Real.exp_neg, Real.exp_log hLpos]
  have hratio : 2 * C / ε ≤ L := le_max_left _ _
  have hratio' : 2 * C ≤ L * ε := (div_le_iff₀ hε).mp hratio
  have hsmall : C * Real.exp (-c * A) ≤ ε / 2 := by
    rw [hExp, inv_eq_one_div, mul_one_div]
    apply (div_le_iff₀ hLpos).2
    nlinarith
  obtain ⟨E⟩ := initialSteinEnv_exists hδ (hδle.trans hδ0h) R hγ
  obtain ⟨Kb, Cb, cb, hKb, hCb, hcb, F, hFK, hdecay, hbounded⟩ :=
    hb δ hδ hδb' R E
  obtain ⟨Nb, hNb⟩ := hbounded A hA (ε / 2) (by linarith)
  let N0 := max Nb 2
  refine ⟨N0, ?_⟩
  intro N hN0 hN2 a ha G _ hG Φ hΦ
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN0
  by_cases hle : a ≤ A
  · have hΦbounds : ∀ i : ℕ, i ≤ 5 → ∀ z,
        ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1 := by
      intro i hi z
      exact HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hΦ hi z
    have h := hNb N hNbN hN2 a ⟨ha, hle⟩ (G := G) hG Φ hΦ.1 hΦbounds
    exact h.trans (by linarith)
  · have hAlea : A ≤ a := le_of_not_ge hle
    have hExpA : Real.exp (-c * a) ≤ Real.exp (-c * A) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hA hc.le]
    have h := hlarge N hN2 a ha (G := G) hG Φ hΦ
    have htail : C * Real.exp (-c * a) ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_left hExpA hC).trans hsmall
    exact h.trans (by linarith)

/-- At zero coupling, the iid Gaussian endpoint already supplies convergence
uniform over all nonnegative starts. -/
theorem fp81s21_initial_static_uniform_zero (p : Parameters) (hγ : p.γ = 0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
          ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
            ∀ a : ℝ, 0 ≤ a →
              ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                IsCenteredGaussianSeq G (fun i j =>
                  HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
                    (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
                ∀ Φ : SeqL2 → ℝ, Φ ∈ CbUnitBall SeqL2 5 →
                  |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
                    (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
                    (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
                      ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                        fp81s21_initial_ellv R (r26t3_qwin R a) x,
                        fp81s21_initial_ellv R (r26t3_qwin R a) x]
                      ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  obtain ⟨δ0, hδ0, hδ0h, hmain⟩ := fp81s21_iid_gaussian_endpoint p hγ
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R ε hε
  obtain ⟨N0, hN0⟩ := hmain δ hδ hδle R ε hε
  refine ⟨N0, ?_⟩
  intro N hN0N hN2 a ha G hGp hG Φ hΦ
  have h := hN0 N hN0N hN2 a ha G hGp hG Φ hΦ
  exact h

#print axioms fp81s21_initial_static_uniform_pos
#print axioms fp81s21_initial_static_uniform_zero
end HRS.Fp81.S21
end
