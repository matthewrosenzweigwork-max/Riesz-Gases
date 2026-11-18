import HRS.MS.FixEqP3Aux24

/-!
# S5.7 `fixed_equation` (worker S57P), part 37: the three kernel pieces of `κ^N - κ`

`κ^N_t - κ_t = el(w₁,A^N) + el(w₂,A^N) + el(w,A^N - A)` with `w₁ = (√(2q_N)-√(2q))√ρ_N`, `w₂ = √(2q)(√ρ_N-√ρ)`, `w = √(2qρ)`;
`S57pKd` data for `w₁`, `w₂` (`∫w₁² = (√(2q_N)-√(2q))²`, `∫w₂² ≤ 2qτ_N`), and the algebraic decomposition.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {s : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {T : ℝ}

theorem s57p_pw_apply {q : ℝ} (hq : 0 ≤ q) (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    s57pw T q ρ (r, x) = Real.sqrt (2 * q) * Real.sqrt (ρ r x) := by
  have hcl : max 0 (min r T) = r := by rw [min_eq_left hr.2, max_eq_right hr.1]
  simp only [s57pw, s57pρc, hcl]
  exact Real.sqrt_mul (by positivity) _

theorem s57p_lint_rho {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t))
    {a : ℝ} (ha : 0 ≤ a) : ∫⁻ x : Euc d, ENNReal.ofReal (a * ρ r x) = ENNReal.ofReal a := by
  have hP := hprob r hr
  have hint : Integrable (ρ r) := Integrable.of_integral_ne_zero (by rw [hP.integral_one]; norm_num)
  simp_rw [ENNReal.ofReal_mul ha]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall hP.nonneg), hP.integral_one]
  simp

theorem s57p_w1_data (hD : S57pFeData s Q ν c ρ T) (hT : 0 ≤ T) {q qN : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t)) :
    S57pKd T (fun p => s57pw T qN ρ p - s57pw T q ρ p) ((Real.sqrt (2 * qN) - Real.sqrt (2 * q)) ^ 2) := by
  have h1 := s57p_wdata hD hT hq hprob
  have h2 := s57p_wdata hD hT hqN hprob
  refine ⟨hT, h2.hw.sub h1.hw, sq_nonneg _, fun r hr => ?_⟩
  have e : ∀ x : Euc d, (s57pw T qN ρ (r, x) - s57pw T q ρ (r, x)) ^ 2 =
      (Real.sqrt (2 * qN) - Real.sqrt (2 * q)) ^ 2 * ρ r x := by
    intro x
    rw [s57p_pw_apply hqN hprob hr, s57p_pw_apply hq hprob hr, ← sub_mul, mul_pow, Real.sq_sqrt ((hprob r hr).nonneg x)]
  simp_rw [e]
  exact (s57p_lint_rho hr hprob (sq_nonneg _)).le

theorem s57p_sqrt_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sqrt_nonneg a
  have h4 := Real.sqrt_nonneg b
  rcases le_total a b with h | h
  · have : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · have : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (by linarith)]
    nlinarith

theorem s57p_w2_data {ρN : ℝ → Euc d → ℝ} {νN : ℝ} {cN : ℝ → Euc d → Euc d} (hD : S57pFeData s Q ν c ρ T)
    (hDN : S57pFeData s Q νN cN ρN T) (hT : 0 ≤ T)
    {q τ : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t))
    (hprobN : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρN t)) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ) :
    S57pKd T (fun p => s57pw T q ρN p - s57pw T q ρ p) (2 * q * τ) := by
  have h1 := s57p_wdata hD hT hq hprob
  have h2 := s57p_wdata hDN hT hq hprobN
  refine ⟨hT, h2.hw.sub h1.hw, by positivity, fun r hr => ?_⟩
  have e : ∀ x : Euc d, (s57pw T q ρN (r, x) - s57pw T q ρ (r, x)) ^ 2 ≤ 2 * q * |ρN r x - ρ r x| := by
    intro x
    rw [s57p_pw_apply hq hprobN hr, s57p_pw_apply hq hprob hr, ← mul_sub, mul_pow, Real.sq_sqrt (by positivity)]
    exact mul_le_mul_of_nonneg_left (s57p_sqrt_sq_le ((hprobN r hr).nonneg x) ((hprob r hr).nonneg x)) (by positivity)
  calc ∫⁻ x : Euc d, ENNReal.ofReal ((s57pw T q ρN (r, x) - s57pw T q ρ (r, x)) ^ 2)
      ≤ ∫⁻ x : Euc d, ENNReal.ofReal (2 * q) * ENNReal.ofReal |ρN r x - ρ r x| :=
        lintegral_mono fun x => by rw [← ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_le_ofReal (e x)
    _ = ENNReal.ofReal (2 * q) * ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * q) * ENNReal.ofReal τ := mul_le_mul' le_rfl (hτ r hr)
    _ = ENNReal.ofReal (2 * q * τ) := (ENNReal.ofReal_mul (by positivity)).symm

theorem s57p_el_decomp {wN wm w : ℝ × Euc d → ℝ} {AN A : ℝ × Euc d → Euc d} {t : ℝ}
    (h1 : MemLp (s57pkf wN AN t) 2 (s57pμ d T)) (h2 : MemLp (s57pkf w A t) 2 (s57pμ d T))
    (h3 : MemLp (s57pkf (fun p => wN p - wm p) AN t) 2 (s57pμ d T))
    (h4 : MemLp (s57pkf (fun p => wm p - w p) AN t) 2 (s57pμ d T))
    (h5 : MemLp (s57pkf w (fun p => AN p - A p) t) 2 (s57pμ d T)) :
    s57pel T wN AN t - s57pel T w A t = s57pel T (fun p => wN p - wm p) AN t +
      s57pel T (fun p => wm p - w p) AN t + s57pel T w (fun p => AN p - A p) t := by
  have e : s57pkf wN AN t - s57pkf w A t = (s57pkf (fun p => wN p - wm p) AN t + s57pkf (fun p => wm p - w p) AN t) +
      s57pkf w (fun p => AN p - A p) t := by
    funext p
    simp only [Pi.sub_apply, Pi.add_apply, s57pkf]
    split_ifs
    · rw [sub_smul, sub_smul, smul_sub]; abel
    · simp
  have h12 : MemLp (s57pkf wN AN t - s57pkf w A t) 2 (s57pμ d T) := h1.sub h2
  have h345 : MemLp ((s57pkf (fun p => wN p - wm p) AN t + s57pkf (fun p => wm p - w p) AN t) +
      s57pkf w (fun p => AN p - A p) t) 2 (s57pμ d T) := (h3.add h4).add h5
  rw [s57p_el_eq h1, s57p_el_eq h2, s57p_el_eq h3, s57p_el_eq h4, s57p_el_eq h5, ← MemLp.toLp_sub h1 h2,
    ← MemLp.toLp_add h3 h4, ← MemLp.toLp_add (h3.add h4) h5]
  exact MemLp.toLp_congr h12 h345 (by rw [e])

end HRS.MS.FixEq
