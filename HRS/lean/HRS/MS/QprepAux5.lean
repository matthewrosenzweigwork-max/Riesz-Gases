import HRS.MS.QprepAux4

/-!
# S4.6 packet A5: uniform bound of the tilted integrand

`s46_J` is the integrand of `s45_gibbs_ibp` (confinement `a'`, temperature `γ`) for a test functional `G'`.
`s46_J_bound`: for `G̃_R = F e^{-c ∑ U(x_i)} Θ_R`, `R ≥ 1`, and `X` off the collision set,
`|J(G̃_R)(X)| ≤ K (1 + ‖X‖) e^{N|c|(|U(0)| + B_U ‖X‖)} e^{-(γ a'/4)‖X‖²}`, with `K` independent of `R` and `X`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- The integrand of the Gibbs integration by parts for the canonical law with confinement `a'` at temperature `γ`. -/
def s46_J (d : ℕ) (s a' γ : ℝ) {N : ℕ} (v : Euc d → Euc d) (G : EucConfig d N → ℝ)
    (X : EucConfig d N) : ℝ :=
  (((∑ k, S45.s45_div v (X k)) * G X + fderiv ℝ G X (fun k => v (X k))) -
    γ * (G X * (∑ i, a' * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫))) *
    Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement a') X)

theorem s46_fderiv_tilt_apply {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {F : EucConfig d N → ℝ}
    (hF : ContDiff ℝ 1 F) {R : ℝ} (X w : EucConfig d N) :
    fderiv ℝ (fun Y => s46_G c U F Y * s46_Theta R Y) X w =
      s46_Theta R X * fderiv ℝ (s46_G c U F) X w + s46_G c U F X * fderiv ℝ (s46_Theta R) X w := by
  have hG : DifferentiableAt ℝ (s46_G c U F) X :=
    ((s46_G_contDiff hU hF).differentiable (by simp)) X
  have hT : DifferentiableAt ℝ (s46_Theta R : EucConfig d N → ℝ) X :=
    ((s46_Theta_contDiff (R := R)).differentiable (by simp)) X
  have := hG.hasFDerivAt.fun_mul hT.hasFDerivAt
  rw [this.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem s46_abs_U_le {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {BU : ℝ} (hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU)
    (x : Euc d) : |U x| ≤ |U 0| + BU * ‖x‖ := by
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hUd z) (fun z _ => hUb z)
    (mem_univ (0 : Euc d)) (mem_univ x)
  rw [Real.norm_eq_abs, sub_zero] at h
  calc |U x| = |(U x - U 0) + U 0| := by ring_nf
    _ ≤ |U x - U 0| + |U 0| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- The exponential factor of the tilt. -/
theorem s46_exp_le {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {BU : ℝ}
    (hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU) (X : EucConfig d N) :
    Real.exp (-c * ∑ i, U (X i)) ≤ Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) := by
  have hBU0 : 0 ≤ BU := (norm_nonneg _).trans (hUb 0)
  refine Real.exp_le_exp.2 ?_
  calc -c * ∑ i, U (X i) ≤ |-c * ∑ i, U (X i)| := le_abs_self _
    _ = |c| * |∑ i, U (X i)| := by rw [abs_mul, abs_neg]
    _ ≤ |c| * ∑ i : Fin N, (|U 0| + BU * ‖X‖) := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => ?_)) (abs_nonneg _)
        refine (s46_abs_U_le hU hUb (X i)).trans ?_
        have := norm_le_pi_norm X i
        nlinarith [hBU0]
    _ = N * |c| * (|U 0| + BU * ‖X‖) := by simp; ring

theorem s46_G_bound {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {BU : ℝ}
    (hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU) {F : EucConfig d N → ℝ} {BF : ℝ} (hBF : ∀ X, |F X| ≤ BF)
    (X : EucConfig d N) :
    |s46_G c U F X| ≤ BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) := by
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  unfold s46_G
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hBF X) (s46_exp_le hU hUb X) (Real.exp_pos _).le hBF0

theorem s46_dG_bound {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {BU : ℝ}
    (hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU) {F : EucConfig d N → ℝ} (hFd : Differentiable ℝ F) {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) {v : Euc d → Euc d} {Bv : ℝ}
    (hBv : ∀ x, ‖v x‖ ≤ Bv) (X : EucConfig d N) :
    |fderiv ℝ (s46_G c U F) X (fun k => v (X k))| ≤
      Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) * (DF * Bv + |c| * BF * N * BU * Bv) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  have hDF0 : 0 ≤ DF := (norm_nonneg _).trans (hDF 0)
  have hBU0 : 0 ≤ BU := (norm_nonneg _).trans (hUb 0)
  have hvf : ‖(fun k => v (X k) : EucConfig d N)‖ ≤ Bv :=
    (pi_norm_le_iff_of_nonneg hBv0).2 fun k => hBv _
  rw [s46_fderiv_G_apply hU hFd]
  have h1 : |fderiv ℝ F X (fun k => v (X k))| ≤ DF * Bv := by
    calc |fderiv ℝ F X (fun k => v (X k))| = ‖fderiv ℝ F X (fun k => v (X k))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ F X‖ * ‖(fun k => v (X k) : EucConfig d N)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ DF * Bv := mul_le_mul (hDF X) hvf (norm_nonneg _) hDF0
  have h2 : |∑ i, fderiv ℝ U (X i) (v (X i))| ≤ N * (BU * Bv) := by
    calc |∑ i, fderiv ℝ U (X i) (v (X i))| ≤ ∑ i, |fderiv ℝ U (X i) (v (X i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, BU * Bv := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.norm_eq_abs]
          exact ((fderiv ℝ U (X i)).le_opNorm _).trans
            (mul_le_mul (hUb _) (hBv _) (norm_nonneg _) hBU0)
      _ = N * (BU * Bv) := by simp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (s46_exp_le hU hUb X) ?_ (abs_nonneg _) (Real.exp_pos _).le
  calc |fderiv ℝ F X (fun k => v (X k)) - c * F X * ∑ i, fderiv ℝ U (X i) (v (X i))|
      ≤ |fderiv ℝ F X (fun k => v (X k))| + |c * F X * ∑ i, fderiv ℝ U (X i) (v (X i))| := abs_sub _ _
    _ ≤ DF * Bv + |c| * BF * (N * (BU * Bv)) := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hBF X) (abs_nonneg _)) h2 (abs_nonneg _)
          (by positivity)
    _ = DF * Bv + |c| * BF * N * BU * Bv := by ring

theorem s46_dTheta_bound (hN : 1 ≤ N) {Dθ : ℝ} (hDθ0 : 0 ≤ Dθ) (hDθ : ∀ t, |deriv s46_theta t| ≤ Dθ)
    {v : Euc d → Euc d} {Bv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv) {R : ℝ} (hR : 1 ≤ R) (X : EucConfig d N) :
    |fderiv ℝ (s46_Theta R : EucConfig d N → ℝ) X (fun k => v (X k))| ≤ Dθ * Bv * (N + 2) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : 0 < R := by linarith
  rw [s46_fderiv_Theta_apply]
  by_cases h2 : 2 < s46_S X / R ^ 2
  · rw [s46_deriv_theta_zero h2]; simp; positivity
  · push Not at h2
    have hS2 : s46_S X ≤ 2 * R ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at h2
    have hsum : |∑ i, 2 * ⟪X i, v (X i)⟫| ≤ Bv * (N + 2 * R ^ 2) := by
      calc |∑ i, 2 * ⟪X i, v (X i)⟫| ≤ ∑ i, |2 * ⟪X i, v (X i)⟫| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, Bv * (1 + ‖X i‖ ^ 2) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            have h3 : |⟪X i, v (X i)⟫| ≤ ‖X i‖ * Bv :=
              (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hBv _) (norm_nonneg _))
            nlinarith [sq_nonneg (‖X i‖ - 1), norm_nonneg (X i)]
        _ = Bv * (N + s46_S X) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [s46_S]
        _ ≤ Bv * (N + 2 * R ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hBv0
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < R ^ 2)]
    calc |deriv s46_theta (s46_S X / R ^ 2)| * (|∑ i, 2 * ⟪X i, v (X i)⟫| / R ^ 2)
        ≤ Dθ * (Bv * (N + 2 * R ^ 2) / R ^ 2) :=
          mul_le_mul (hDθ _) (div_le_div_of_nonneg_right hsum (by positivity)) (by positivity) hDθ0
      _ ≤ Dθ * (Bv * (N + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hDθ0
          have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
          have hR20 : (0 : ℝ) < R ^ 2 := by positivity
          calc Bv * (N + 2 * R ^ 2) / R ^ 2 = Bv * N / R ^ 2 + 2 * Bv := by field_simp
            _ ≤ Bv * N + 2 * Bv := by
                have := div_le_self (mul_nonneg hBv0 hN0.le) hR2
                linarith
            _ = Bv * (N + 2) := by ring
      _ = _ := by ring

theorem s46_pair_sum_bound {s : ℝ} (hN : 1 ≤ N) {γ w E CP : ℝ} (hw0 : 0 ≤ w)
    {v : Euc d → Euc d} (hCP0 : 0 ≤ CP) (hE0 : 0 ≤ E) (X : EucConfig d N)
    (hterm : ∀ i j : Fin N, i < j →
      w * |⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫| ≤ CP * E) :
    w * |(1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫| ≤ N * CP * E := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : w * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫| ≤ CP * E * ((N : ℝ) * N) := by
    calc w * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫|
        ≤ w * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            |⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫| := by
          refine mul_le_mul_of_nonneg_left ?_ hw0
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            w * |⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫| := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), CP * E :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hterm i j (by simpa using hj)
      _ = (CP * E) * ∑ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
      _ ≤ CP * E * ((N : ℝ) * N) :=
          mul_le_mul_of_nonneg_left (S45.s45_card_pairs_le N) (by positivity)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
  calc w * (1 / (N : ℝ) * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫|)
      = 1 / (N : ℝ) * (w * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫|) := by ring
    _ ≤ 1 / (N : ℝ) * (CP * E * ((N : ℝ) * N)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = N * CP * E := by field_simp

/-- The abstract algebra of the bound: `A`, `B`, `P`, `GT`, `w` are numbers. -/
theorem s46_alg {A B P GT w γ : ℝ} (hγ : 0 < γ) (hw : 0 < w) :
    |(A - γ * (GT * (B + P))) * w| ≤ w * |A| + γ * |GT| * (w * |B|) + γ * |GT| * (w * |P|) := by
  rw [abs_mul, abs_of_pos hw]
  have : |A - γ * (GT * (B + P))| ≤ |A| + γ * |GT| * (|B| + |P|) := by
    calc |A - γ * (GT * (B + P))| ≤ |A| + |γ * (GT * (B + P))| := abs_sub _ _
      _ = |A| + γ * (|GT| * |B + P|) := by rw [abs_mul, abs_of_pos hγ, abs_mul]
      _ ≤ |A| + γ * (|GT| * (|B| + |P|)) := by gcongr; exact abs_add_le _ _
      _ = _ := by ring
  calc |A - γ * (GT * (B + P))| * w ≤ (|A| + γ * |GT| * (|B| + |P|)) * w :=
        mul_le_mul_of_nonneg_right this hw.le
    _ = _ := by ring

theorem s46_final_ineq {Cw Nn dd Dv BF DF Bv c BU Dθ γ a' CP E Em nX : ℝ} (hCw : 0 ≤ Cw) (hN : 0 ≤ Nn)
    (hd : 0 ≤ dd) (hDv : 0 ≤ Dv) (hBF : 0 ≤ BF) (hDF : 0 ≤ DF) (hBv : 0 ≤ Bv) (hBU : 0 ≤ BU)
    (hDθ : 0 ≤ Dθ) (hγ : 0 < γ) (ha' : 0 < a') (hCP : 0 ≤ CP) (hE : 0 ≤ E) (hEm : 0 ≤ Em) (hn : 0 ≤ nX) :
    Cw * E * (Nn * (dd * Dv) * (BF * Em) + (Em * (DF * Bv + |c| * BF * Nn * BU * Bv) +
        BF * Em * (Dθ * Bv * (Nn + 2)))) + γ * (BF * Em) * (Cw * E * (Nn * a' * nX * Bv)) +
        γ * (BF * Em) * (Nn * CP * E) ≤
      (Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2))) +
        γ * BF * Nn * a' * Bv * Cw + γ * BF * Nn * CP) * (1 + nX) * Em * E := by
  have c1 : 0 ≤ Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2))) := by
    positivity
  have c2 : 0 ≤ γ * BF * Nn * a' * Bv * Cw := by positivity
  have c3 : 0 ≤ γ * BF * Nn * CP := by positivity
  have e : Cw * E * (Nn * (dd * Dv) * (BF * Em) + (Em * (DF * Bv + |c| * BF * Nn * BU * Bv) +
        BF * Em * (Dθ * Bv * (Nn + 2)))) + γ * (BF * Em) * (Cw * E * (Nn * a' * nX * Bv)) +
        γ * (BF * Em) * (Nn * CP * E) =
      E * Em * ((Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2)))) +
        γ * BF * Nn * a' * Bv * Cw * nX + γ * BF * Nn * CP) := by ring
  rw [e]
  have : (Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2)))) +
        γ * BF * Nn * a' * Bv * Cw * nX + γ * BF * Nn * CP ≤
      (Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2))) +
        γ * BF * Nn * a' * Bv * Cw + γ * BF * Nn * CP) * (1 + nX) := by
    nlinarith [mul_nonneg c1 hn, mul_nonneg c3 hn, mul_nonneg c2 hn]
  calc E * Em * _ ≤ E * Em * ((Cw * (Nn * (dd * Dv) * BF + (DF * Bv + |c| * BF * Nn * BU * Bv + BF * Dθ * Bv * (Nn + 2))) +
        γ * BF * Nn * a' * Bv * Cw + γ * BF * Nn * CP) * (1 + nX)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem s46_J_bound {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) {a' γ : ℝ} (ha' : 0 < a') (hγ : 0 < γ)
    (hN : 1 ≤ N) {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {BU : ℝ}
    (hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU) {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ}
    (hBv : ∀ x, ‖v x‖ ≤ Bv) (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ}
    (hF : ContDiff ℝ 1 F) {BF DF : ℝ} (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ X : EucConfig d N, (∀ i j, i ≠ j → X i ≠ X j) →
      |s46_J d s a' γ v (fun Y => s46_G c U F Y * s46_Theta R Y) X| ≤
        K * (1 + ‖X‖) * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) *
          Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hDv0 : 0 ≤ Dv := (norm_nonneg _).trans (hDv 0)
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  have hDF0 : 0 ≤ DF := (norm_nonneg _).trans (hDF 0)
  have hBU0 : 0 ≤ BU := (norm_nonneg _).trans (hUb 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Cw, hCw0, hCw⟩ := s46_w0_le (d := d) (N := N) (s := s) ha' hγ hN
  obtain ⟨CP, hCP0, hCP⟩ := s46_pair_w0 (d := d) (N := N) hs0 ha' hγ hN hDv0
  obtain ⟨Dθ, hDθ0, hDθ⟩ := s46_deriv_theta_bound
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  refine ⟨Cw * (N * (d * Dv) * BF + (DF * Bv + |c| * BF * N * BU * Bv + BF * Dθ * Bv * (N + 2)))
      + γ * BF * N * a' * Bv * Cw + γ * BF * N * CP, by positivity, fun R hR X hX => ?_⟩
  have hR0 : 0 < R := by linarith
  have hE0 : 0 ≤ Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) := (Real.exp_pos _).le
  have hEm0 : 0 < Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) := Real.exp_pos _
  have hn : 0 ≤ ‖X‖ := norm_nonneg _
  have hw0 : 0 < Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement a') X) :=
    Real.exp_pos _
  have hwE := hCw X hX
  have hB1 : |∑ i, a' * ⟪X i, v (X i)⟫| ≤ N * a' * ‖X‖ * Bv := by
    calc |∑ i, a' * ⟪X i, v (X i)⟫| ≤ ∑ i, |a' * ⟪X i, v (X i)⟫| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, a' * (‖X‖ * Bv) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg ha'.le]
          refine mul_le_mul_of_nonneg_left ?_ ha'.le
          calc |⟪X i, v (X i)⟫| ≤ ‖X i‖ * ‖v (X i)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖X‖ * Bv := mul_le_mul (norm_le_pi_norm X i) (hBv _) (norm_nonneg _) (norm_nonneg _)
      _ = N * a' * ‖X‖ * Bv := by simp; ring
  have hP1 := s46_pair_sum_bound (s := s) (v := v) hN (γ := γ) hw0.le hCP0 hE0 X
    (fun i j hij => hCP X hX i j hij _ (S45.s45_lip hvd hDv _ _))
  have hGb := s46_G_bound (c := c) hU hUb hBF X
  have hdG := s46_dG_bound (c := c) hU hUb hFd hBF hDF hBv X
  have hdΘ := s46_dTheta_bound hN hDθ0 hDθ hBv hR X
  have hdiv : |∑ k, S45.s45_div v (X k)| ≤ N * (d * Dv) := by
    calc |∑ k, S45.s45_div v (X k)| ≤ ∑ k, |S45.s45_div v (X k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, (d * Dv) := Finset.sum_le_sum fun k _ => S45.s45_div_le hDv _
      _ = N * (d * Dv) := by simp
  have hΘ0 := s46_theta_nonneg (s46_S X / R ^ 2)
  have hΘ1 := s46_theta_le_one (s46_S X / R ^ 2)
  have hΘe : s46_Theta R X = s46_theta (s46_S X / R ^ 2) := rfl
  have hΘ0' : 0 ≤ s46_Theta R X := hΘ0
  have hΘ1' : s46_Theta R X ≤ 1 := hΘ1
  have hGt : |s46_G c U F X * s46_Theta R X| ≤ BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) := by
    rw [abs_mul, abs_of_nonneg hΘ0']
    calc |s46_G c U F X| * s46_Theta R X ≤ |s46_G c U F X| * 1 :=
          mul_le_mul_of_nonneg_left hΘ1' (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hGb
  have hdGt : |fderiv ℝ (fun Y => s46_G c U F Y * s46_Theta R Y) X (fun k => v (X k))| ≤
      Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) * (DF * Bv + |c| * BF * N * BU * Bv) +
        BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) * (Dθ * Bv * (N + 2)) := by
    rw [s46_fderiv_tilt_apply hU hF]
    calc |s46_Theta R X * fderiv ℝ (s46_G c U F) X (fun k => v (X k)) +
          s46_G c U F X * fderiv ℝ (s46_Theta R) X (fun k => v (X k))|
        ≤ |s46_Theta R X * fderiv ℝ (s46_G c U F) X (fun k => v (X k))| +
          |s46_G c U F X * fderiv ℝ (s46_Theta R) X (fun k => v (X k))| := abs_add_le _ _
      _ ≤ _ := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_of_nonneg hΘ0']
            calc s46_Theta R X * |fderiv ℝ (s46_G c U F) X (fun k => v (X k))|
                ≤ 1 * |fderiv ℝ (s46_G c U F) X (fun k => v (X k))| :=
                  mul_le_mul_of_nonneg_right hΘ1' (abs_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact hdG
          · rw [abs_mul]
            exact mul_le_mul hGb hdΘ (abs_nonneg _) (by positivity)
  unfold s46_J
  generalize hAdef : (∑ k, S45.s45_div v (X k)) * (s46_G c U F X * s46_Theta R X) +
      fderiv ℝ (fun Y => s46_G c U F Y * s46_Theta R Y) X (fun k => v (X k)) = A
  have hA1 : |A| ≤ N * (d * Dv) * (BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖))) +
      (Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) * (DF * Bv + |c| * BF * N * BU * Bv) +
        BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) * (Dθ * Bv * (N + 2))) := by
    rw [← hAdef]
    calc _ ≤ |(∑ k, S45.s45_div v (X k)) * (s46_G c U F X * s46_Theta R X)| +
          |fderiv ℝ (fun Y => s46_G c U F Y * s46_Theta R Y) X (fun k => v (X k))| := abs_add_le _ _
      _ ≤ _ := by
          refine add_le_add ?_ hdGt
          rw [abs_mul]
          exact mul_le_mul hdiv hGt (abs_nonneg _) (by positivity)
  have hmain := s46_alg (A := A) (B := ∑ i, a' * ⟪X i, v (X i)⟫)
    (P := (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫)
    (GT := s46_G c U F X * s46_Theta R X)
    (w := Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement a') X)) hγ hw0
  refine hmain.trans ?_
  have t1 := mul_le_mul hwE hA1 (abs_nonneg _) (by positivity)
  have t2 : γ * |s46_G c U F X * s46_Theta R X| * (Real.exp (-γ * canonicalHamiltonian (rieszKernel d s)
      (confinement a') X) * |∑ i, a' * ⟪X i, v (X i)⟫|) ≤
      γ * (BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖))) *
        (Cw * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) * (N * a' * ‖X‖ * Bv)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hGt hγ.le) ?_ (by positivity) (by positivity)
    exact mul_le_mul hwE hB1 (abs_nonneg _) (by positivity)
  have t3 : γ * |s46_G c U F X * s46_Theta R X| * (Real.exp (-γ * canonicalHamiltonian (rieszKernel d s)
      (confinement a') X) * |(1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫|) ≤
      γ * (BF * Real.exp (N * |c| * (|U 0| + BU * ‖X‖))) *
        (N * CP * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hGt hγ.le) hP1 (by positivity) (by positivity)
  have hfin := s46_final_ineq (Cw := Cw) (Nn := N) (dd := d) (Dv := Dv) (BF := BF) (DF := DF)
    (Bv := Bv) (c := c) (BU := BU) (Dθ := Dθ) (γ := γ) (a' := a') (CP := CP)
    (E := Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2))) (Em := Real.exp (N * |c| * (|U 0| + BU * ‖X‖)))
    (nX := ‖X‖) hCw0 hN0.le (by positivity) hDv0 hBF0 hDF0 hBv0 hBU0 hDθ0 hγ ha' hCP0 hE0 hEm0.le hn
  calc _ ≤ _ := add_le_add (add_le_add t1 t2) t3
    _ ≤ _ := hfin

end S46

end
