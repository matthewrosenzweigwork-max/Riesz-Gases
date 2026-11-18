import HRS.MS.R26T8AT1
import HRS.MS.R26T8AZ7b

/-!
# S8.2 T8A T2: linearity and diagonal-congruence of `rawNewton` and `localNewton` on conormal pair functions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_T2_rawNewton_congr (hd : 2 ≤ d) (nu : ℝ) (chi : Euc d → ℝ) {F1 F2 : Euc d → Euc d → ℝ}
    (h : ∀ x y, x ≠ y → F1 x y = F2 x y) (x y : Euc d) :
    rawNewton nu chi F1 x y = rawNewton nu chi F2 x y := by
  unfold rawNewton
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [r26t8a_ae_ne_zero hd] with z hz
  have e : ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • z) - ((1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • z) = z := by module
  unfold midPair
  rw [h _ _ (by intro h0; apply hz; rw [← e, h0, sub_self])]

theorem r26t8a_T2_rawNewton_lin (nu : ℝ) (chi : Euc d → ℝ) {F1 F2 : Euc d → Euc d → ℝ} (c : ℝ)
    (h1 : ∀ x y : Euc d, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
      midPair F1 ((1 / 2 : ℝ) • (x + y)) z))
    (h2 : ∀ x y : Euc d, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
      midPair F2 ((1 / 2 : ℝ) • (x + y)) z)) {x y : Euc d} (hxy : x ≠ y) :
    rawNewton nu chi (fun x y => F1 x y + c * F2 x y) x y = rawNewton nu chi F1 x y + c * rawNewton nu chi F2 x y := by
  unfold rawNewton
  have e : ∀ z, newtonKernel d nu (x - y - z) * chi z * midPair (fun x y => F1 x y + c * F2 x y)
      ((1 / 2 : ℝ) • (x + y)) z = newtonKernel d nu (x - y - z) * chi z * midPair F1 ((1 / 2 : ℝ) • (x + y)) z +
      c * (newtonKernel d nu (x - y - z) * chi z * midPair F2 ((1 / 2 : ℝ) • (x + y)) z) := fun z => by
    unfold midPair; ring
  simp only [e]
  rw [integral_add (h1 x y hxy) ((h2 x y hxy).const_mul c), integral_const_mul]
  ring

theorem r26t8a_T2_localNewton_lin (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (k b : ℕ) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {F1 F2 : Euc d → Euc d → ℝ} {A1 A2 : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : Conormal k b M sigma A1 F1) (h2 : Conormal k b M sigma A2 F2) (c : ℝ) {x y : Euc d} (hxy : x ≠ y) :
    localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi (fun x y => F1 x y + c * F2 x y) x y =
      localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F1 x y +
        c * localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F2 x y := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_raw_newton_bound_same d hd k b beta⁻¹ M sigma (inv_pos.2 hbeta) hM hsd chi hchi
  obtain ⟨i1, r1⟩ := hC1 F1 A1 hA1 h1
  obtain ⟨i2, r2⟩ := hC1 F2 A2 hA2 h2
  have hsd2 : sigma - 2 < d := by linarith
  obtain ⟨a1, a2, a3⟩ := r26t8a_T1_integrability hd a beta M (sigma - 2) ha hbeta hM hsd2 rho hrho hchi
    (mul_nonneg hC10 hA1) r1
  obtain ⟨b1, b2, b3⟩ := r26t8a_T1_integrability hd a beta M (sigma - 2) ha hbeta hM hsd2 rho hrho hchi
    (mul_nonneg hC10 hA2) r2
  unfold localNewton
  rw [r26t8a_T1_center_congr hd rho (k2 := fun x y => rawNewton beta⁻¹ chi F1 x y + c * rawNewton beta⁻¹ chi F2 x y)
    (fun x y hxy => r26t8a_T2_rawNewton_lin beta⁻¹ chi c i1 i2 hxy) hxy]
  exact r26t8a_T1_center_lin _ c a1 b1 a2 b2 a3 b3 x y

end HRS.MS.R26T8A
