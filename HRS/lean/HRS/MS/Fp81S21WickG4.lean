import HRS.MS.Fp81S21WickG3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

private def fp81s21_wickG_symCoeff {n : ℕ} (d : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := fun i j => (d i j + d j i) / 2

private theorem fp81s21_wickG_symCoeff_sym {n : ℕ} (d : Fin n → Fin n → ℝ) :
    ∀ i j, fp81s21_wickG_symCoeff d i j = fp81s21_wickG_symCoeff d j i := by
  intro i j
  simp [fp81s21_wickG_symCoeff, add_comm]

private theorem fp81s21_wickG_symCoeff_sq_sum_le {n : ℕ} (d : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (fp81s21_wickG_symCoeff d i j) ^ 2 ≤ ∑ i, ∑ j, d i j ^ 2 := by
  have hpoint : ∀ i j,
      (fp81s21_wickG_symCoeff d i j) ^ 2 ≤ (d i j ^ 2 + d j i ^ 2) / 2 := by
    intro i j
    simp only [fp81s21_wickG_symCoeff]
    nlinarith [sq_nonneg (d i j - d j i)]
  calc
    ∑ i, ∑ j, (fp81s21_wickG_symCoeff d i j) ^ 2 ≤
        ∑ i, ∑ j, (d i j ^ 2 + d j i ^ 2) / 2 := by
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = ∑ i, ∑ j, d i j ^ 2 := by
      have hscale (f : Fin n → Fin n → ℝ) (c : ℝ) :
          (∑ i, ∑ j, f i j * c) = (∑ i, ∑ j, f i j) * c := by
        calc
          (∑ i, ∑ j, f i j * c) = ∑ i, (∑ j, f i j) * c := by
            congr 1
            funext i
            rw [← Finset.sum_mul]
          _ = (∑ i, ∑ j, f i j) * c := by rw [← Finset.sum_mul]
      have hswap : (∑ i, ∑ j, d j i ^ 2) = ∑ i, ∑ j, d i j ^ 2 := by
        rw [Finset.sum_comm]
      calc
        (∑ i, ∑ j, (d i j ^ 2 + d j i ^ 2) / 2) =
            (∑ i, ∑ j, (d i j ^ 2 + d j i ^ 2)) * (1 / 2 : ℝ) := by
              calc
                _ = ∑ i, ∑ j, (d i j ^ 2 + d j i ^ 2) * (1 / 2 : ℝ) := by
                  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
                _ = _ := hscale (fun i j => d i j ^ 2 + d j i ^ 2) _
        _ = (∑ i, ∑ j, d i j ^ 2 + ∑ i, ∑ j, d j i ^ 2) * (1 / 2 : ℝ) := by
              congr 1
              calc
                (∑ i, ∑ j, (d i j ^ 2 + d j i ^ 2)) =
                    ∑ i, ((∑ j, d i j ^ 2) + (∑ j, d j i ^ 2)) := by
                      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
                _ = _ := Finset.sum_add_distrib
        _ = ∑ i, ∑ j, d i j ^ 2 := by rw [hswap]; ring

/-- Arbitrary finite coefficient matrices define the same centered quadratic
form as their symmetric parts.  With covariance form bounded by `Λ²`, the
half-Wick polynomial has the dimension-free variance bound `Λ⁴ / 2` times
the coefficient Frobenius norm. -/
theorem fp81s21_wickG_finite_half_wick_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {g : Fin n → Ω → ℝ}
    (hg : HRS.MS.R2Chaos.S94GFam P g) (Λ : ℝ) (hΛ :
      ∀ α : Fin n → ℝ,
        HRS.MS.R2Chaos.s94q P g α ≤ Λ ^ 2 * ∑ i, α i ^ 2)
    (d : Fin n → Fin n → ℝ) :
    ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j *
      (g i ω * g j ω - ∫ ω', g i ω' * g j ω' ∂P)) ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Λ ^ 4 * ∑ i, ∑ j, d i j ^ 2 := by
  let D := fp81s21_wickG_symCoeff d
  let Q : Fin n → Fin n → Ω → ℝ := fun i j ω =>
    g i ω * g j ω - ∫ ω', g i ω' * g j ω' ∂P
  have hswap : ∀ ω, (∑ i, ∑ j, d i j * Q i j ω) =
      ∑ i, ∑ j, D i j * Q i j ω := by
    intro ω
    have htranspose : (∑ i, ∑ j, d j i * Q i j ω) =
        ∑ i, ∑ j, d i j * Q i j ω := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Q]
      have hcov : ∫ ω', g j ω' * g i ω' ∂P = ∫ ω', g i ω' * g j ω' ∂P := by
        exact integral_congr_ae (ae_of_all _ fun ω' => mul_comm (g j ω') (g i ω'))
      rw [mul_comm (g j ω) (g i ω), hcov]
    dsimp [D, fp81s21_wickG_symCoeff]
    calc
      ∑ i, ∑ j, d i j * Q i j ω =
          (1 / 2 : ℝ) * (∑ i, ∑ j, d i j * Q i j ω) +
            (1 / 2 : ℝ) * (∑ i, ∑ j, d j i * Q i j ω) := by
              rw [htranspose]
              ring
      _ = ∑ i, ∑ j, (d i j + d j i) / 2 * Q i j ω := by
        have hterm : ∀ i j,
            (d i j + d j i) / 2 * Q i j ω =
              (1 / 2 : ℝ) * (d i j * Q i j ω) +
                (1 / 2 : ℝ) * (d j i * Q i j ω) := by
          intro i j
          ring
        have hscale (f : Fin n → Fin n → ℝ) :
            (1 / 2 : ℝ) * (∑ i, ∑ j, f i j) =
              ∑ i, ∑ j, (1 / 2 : ℝ) * f i j := by
          calc
            (1 / 2 : ℝ) * (∑ i, ∑ j, f i j) =
                ∑ i, (1 / 2 : ℝ) * (∑ j, f i j) := by rw [Finset.mul_sum]
            _ = ∑ i, ∑ j, (1 / 2 : ℝ) * f i j := by
              exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        calc
          (1 / 2 : ℝ) * (∑ i, ∑ j, d i j * Q i j ω) +
              (1 / 2 : ℝ) * (∑ i, ∑ j, d j i * Q i j ω) =
              ∑ i, ∑ j, (1 / 2 : ℝ) * (d i j * Q i j ω) +
                ∑ i, ∑ j, (1 / 2 : ℝ) * (d j i * Q i j ω) := by
                  rw [hscale, hscale]
          _ = ∑ i, ∑ j, ((1 / 2 : ℝ) * (d i j * Q i j ω) +
                (1 / 2 : ℝ) * (d j i * Q i j ω)) := by
                  calc
                    (∑ i, ∑ j, (1 / 2 : ℝ) * (d i j * Q i j ω)) +
                        ∑ i, ∑ j, (1 / 2 : ℝ) * (d j i * Q i j ω) =
                        ∑ i, ((∑ j, (1 / 2 : ℝ) * (d i j * Q i j ω)) +
                          (∑ j, (1 / 2 : ℝ) * (d j i * Q i j ω))) := by
                            rw [← Finset.sum_add_distrib]
                    _ = _ := by
                      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib.symm
          _ = _ := by
            exact Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => hterm i j |>.symm
  have hquad := hg.quad_var (sq_nonneg Λ) hΛ D
    (fp81s21_wickG_symCoeff_sym d)
  have hDnorm := fp81s21_wickG_symCoeff_sq_sum_le d
  have hpoint : ∀ ω,
      ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * Q i j ω) ^ 2 =
        (1 / 4 : ℝ) * (∑ i, ∑ j, D i j * Q i j ω) ^ 2 := by
    intro ω
    rw [hswap ω]
    ring
  have hcoord4 : ∀ i, MemLp (g i) 4 P := by
    intro i
    let α : Fin n → ℝ := Pi.single i 1
    have hlinear : HRS.MS.R2Chaos.s94lin g α = g i := by
      funext ω
      simp [HRS.MS.R2Chaos.s94lin, α, Pi.single_apply]
    obtain ⟨v, hv⟩ := hg.gauss α
    have hlaw : HasGaussianLaw (HRS.MS.R2Chaos.s94lin g α) P := by
      refine ⟨hg.meas_lin α, ?_⟩
      have hG : IsGaussian (P.map (fun ω => ∑ k, α k * g k ω)) := by
        rw [hv]
        infer_instance
      have hfun : (fun ω => ∑ k, α k * g k ω) = HRS.MS.R2Chaos.s94lin g α := by
        funext ω
        rfl
      rw [← hfun]
      exact hG
    rw [← hlinear]
    exact hlaw.memLp (by norm_num)
  have hQmem : ∀ i j, MemLp (Q i j) 2 P := by
    intro i j
    have hprod : MemLp (fun ω => g i ω * g j ω) 2 P :=
      HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (A := g i) (B := g j)
        (hcoord4 i) (hcoord4 j)
    have hconst : MemLp (fun _ : Ω => ∫ ω', g i ω' * g j ω' ∂P) 2 P := by
      exact memLp_const _
    exact hprod.sub hconst
  have hSrow : ∀ i, MemLp (fun ω => ∑ j, D i j * Q i j ω) 2 P := by
    intro i
    exact memLp_finsetSum (f := fun j ω => D i j * Q i j ω) Finset.univ
      fun j _ => (hQmem i j).const_mul (D i j)
  have hS : MemLp (fun ω => ∑ i, ∑ j, D i j * Q i j ω) 2 P := by
    exact memLp_finsetSum (f := fun i ω => ∑ j, D i j * Q i j ω) Finset.univ
      fun i _ => hSrow i
  have hSsq : Integrable (fun ω => (∑ i, ∑ j, D i j * Q i j ω) ^ 2) P := hS.integrable_sq
  have hfun : (fun ω => ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * Q i j ω) ^ 2) =
      fun ω => (1 / 4 : ℝ) * (∑ i, ∑ j, D i j * Q i j ω) ^ 2 := by
    funext ω
    exact hpoint ω
  rw [show (fun ω => ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * Q i j ω) ^ 2) =
      fun ω => (1 / 4 : ℝ) * (∑ i, ∑ j, D i j * Q i j ω) ^ 2 from hfun,
      integral_const_mul]
  calc
    (1 / 4 : ℝ) * ∫ ω, (∑ i, ∑ j, D i j * Q i j ω) ^ 2 ∂P ≤
        (1 / 4 : ℝ) * (2 * (Λ ^ 2) ^ 2 * ∑ i, ∑ j, D i j ^ 2) := by
          exact mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ ≤ (1 / 2 : ℝ) * Λ ^ 4 * ∑ i, ∑ j, d i j ^ 2 := by
      have hn : 0 ≤ ∑ i, ∑ j, d i j ^ 2 := Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hΛ4 : 0 ≤ Λ ^ 4 := by positivity
      nlinarith [hDnorm]

#print axioms fp81s21_wickG_finite_half_wick_bound

end HRS.Fp81.S21

end
