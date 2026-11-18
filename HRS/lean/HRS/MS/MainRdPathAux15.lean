import HRS.MS.MainRdPathAux14

/-!
# S.A.9, packet P3i: the pointwise bound for the tail of the stochastic convolution

`sa9_pt_bound`: for a configuration `x` of `N` particles and `r ∈ [0,t]`,
`c² ∑_{i,j} Tm_N^j(r, x_i) ≤ c²N ∑_j (4 Nsum_j + 4 E_δ + 2 E_D) + 2 d K² c² R⁻² ∑_i |x_i|²`
with `Nsum_j = ∑_{y ∈ net} Tm_∞^j(r, y)` for a finite `δ`-net of the ball of radius `R`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField

variable {d : ℕ}

section Pt

variable {q m : ℕ} {T K₁ K : ℝ} {CfN CfL : WholeCoeff d}

theorem sa9_pt_bound (hm : 1 ≤ m) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    (hN : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfN T K₁) (hL : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfL T K)
    {t : ℝ} (htT : t ≤ T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {D : ℝ}
    (hdiff : ∀ g : mhn_Hc d,
      MemCb (m + 1) (fun x => propagatorW CfN r t (mhn_phi g) x - propagatorW CfL r t (mhn_phi g) x) ∧
        cbNorm (m + 1) (fun x => propagatorW CfN r t (mhn_phi g) x - propagatorW CfL r t (mhn_phi g) x) ≤
          D * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) (mhn_phi g))
    (Lc : ℕ) {R δ : ℝ} (hR : 0 < R) (net : Finset (Euc d))
    (hnet : ∀ x : Euc d, ‖x‖ ≤ R → ∃ y ∈ net, ‖x - y‖ < δ) {N : ℕ} (cN : ℝ) (xs : Fin N → Euc d) :
    ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) * sa9_Tm h CfN t ia.2 Lc (r, xs ia.1) ≤
      ENNReal.ofReal (cN ^ 2 * N) * ∑ j : Fin d, (4 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) +
        4 * ENNReal.ofReal (((d : ℝ) * d * |K| * δ) ^ 2) + 2 * ENNReal.ofReal (D ^ 2)) +
      2 * d * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (cN ^ 2 / R ^ 2) *
        ∑ i : Fin N, ENNReal.ofReal (‖xs i‖ ^ 2) := by
  classical
  set Eδ : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) * d * |K| * δ) ^ 2) with hEδ
  set ED : ℝ≥0∞ := ENNReal.ofReal (D ^ 2) with hED
  set K2 : ℝ≥0∞ := ENNReal.ofReal (K ^ 2) with hK2
  have hKK : ENNReal.ofReal (K ^ 2) = K2 := rfl
  -- the pointwise bound for one particle and one component
  have hone : ∀ (j : Fin d) (x : Euc d), sa9_Tm h CfN t j Lc (r, x) ≤
      4 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 4 * Eδ + 2 * ED + 2 * K2 * ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2) := by
    intro j x
    have h1 := sa9_Tm_cmp h hP hN hL htT hr hdiff j Lc x
    have h2 : sa9_Tm h CfL t j Lc (r, x) ≤ 2 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 2 * Eδ +
        K2 * ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2) := by
      by_cases hx : ‖x‖ ≤ R
      · obtain ⟨y, hy, hxy⟩ := hnet x hx
        have h3 := sa9_Tm_lip hm h hP hL htT hr j Lc x y
        have h4 : ENNReal.ofReal (((d : ℝ) * d * |K| * ‖x - y‖) ^ 2) ≤ Eδ := by
          refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
          exact mul_le_mul_of_nonneg_left hxy.le (by positivity)
        have h5 : sa9_Tm h CfL t j Lc (r, y) ≤ ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) :=
          Finset.single_le_sum (f := fun y => sa9_Tm h CfL t j Lc (r, y)) (fun _ _ => zero_le) hy
        calc sa9_Tm h CfL t j Lc (r, x) ≤ 2 * sa9_Tm h CfL t j Lc (r, y) +
              2 * ENNReal.ofReal (((d : ℝ) * d * |K| * ‖x - y‖) ^ 2) := h3
          _ ≤ 2 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 2 * Eδ + 0 := by
              rw [add_zero]; gcongr
          _ ≤ _ := by gcongr; exact zero_le
      · push Not at hx
        have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        calc sa9_Tm h CfL t j Lc (r, x) ≤ K2 := sa9_Tm_le hL h hP htT j Lc r x
          _ = K2 * 1 := (mul_one _).symm
          _ ≤ K2 * ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2) := by gcongr
          _ ≤ 2 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 2 * Eδ + K2 * ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2) :=
              le_add_self
    calc sa9_Tm h CfN t j Lc (r, x) ≤ 2 * sa9_Tm h CfL t j Lc (r, x) + 2 * ED := h1
      _ ≤ 2 * (2 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 2 * Eδ +
            K2 * ENNReal.ofReal (‖x‖ ^ 2 / R ^ 2)) + 2 * ED := by gcongr
      _ = _ := by ring
  set A : Fin d → ℝ≥0∞ := fun j => 4 * ∑ y ∈ net, sa9_Tm h CfL t j Lc (r, y) + 4 * Eδ + 2 * ED with hA
  calc ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) * sa9_Tm h CfN t ia.2 Lc (r, xs ia.1)
      ≤ ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) * (A ia.2 +
          2 * K2 * ENNReal.ofReal (‖xs ia.1‖ ^ 2 / R ^ 2)) :=
        Finset.sum_le_sum fun ia _ => mul_le_mul' le_rfl (hone ia.2 (xs ia.1))
    _ = ENNReal.ofReal (cN ^ 2) * ∑ ia : Fin N × Fin d, A ia.2 +
        ENNReal.ofReal (cN ^ 2) * ∑ ia : Fin N × Fin d, 2 * K2 * ENNReal.ofReal (‖xs ia.1‖ ^ 2 / R ^ 2) := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        simp only [← Finset.mul_sum]
    _ = _ := by
        have e1 : ∑ ia : Fin N × Fin d, A ia.2 = (N : ℝ≥0∞) * ∑ j, A j := by
          rw [Fintype.sum_prod_type]
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have e2 : ∑ ia : Fin N × Fin d, 2 * K2 * ENNReal.ofReal (‖xs ia.1‖ ^ 2 / R ^ 2) =
            (d : ℝ≥0∞) * (2 * K2) * ∑ i, ENNReal.ofReal (‖xs i‖ ^ 2 / R ^ 2) := by
          rw [Fintype.sum_prod_type]
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
          ring
        have e3 : ENNReal.ofReal (cN ^ 2) * ∑ i, ENNReal.ofReal (‖xs i‖ ^ 2 / R ^ 2) =
            ENNReal.ofReal (cN ^ 2 / R ^ 2) * ∑ i, ENNReal.ofReal (‖xs i‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        have e4 : ENNReal.ofReal (cN ^ 2 * N) = ENNReal.ofReal (cN ^ 2) * (N : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_natCast]
        rw [e1, e2, e4]
        have : ENNReal.ofReal (cN ^ 2) * ((d : ℝ≥0∞) * (2 * K2) * ∑ i, ENNReal.ofReal (‖xs i‖ ^ 2 / R ^ 2)) =
            2 * d * K2 * (ENNReal.ofReal (cN ^ 2) * ∑ i, ENNReal.ofReal (‖xs i‖ ^ 2 / R ^ 2)) := by ring
        rw [this, e3]
        ring

end Pt

end HRS.MS.MainRdPath
