import HRS.Whole.Critical
import HRS.Whole.Q34Aux3
import HRS.MS.CritWholeCap
import HRS.MS.CritWholeTaylor

/-!
# S8.1.K3 -- exact scalar pole coefficient and the compact-beta cavity-count adapter

Worker S81, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81bd_`.

* `s81bd_pole_taylor_log`: for `0 < λ ≤ 1`,
  `∫ taylorH(λ g(x-y)) d(ρ dy) = (|S^{d-1}|/d) ρ(x) λ² log(1/λ) + O(λ²)`, `g = |·|^{-d/2}`.
* `s81bd_pole_taylor_beta_N`: with `λ = β/N`, `N-1` cavity particles and `β` in a compact positive
  interval, `(N-1) ∫ taylorH(λ g) = β² |S^{d-1}|/d ρ(x) log N / N + O(1/N)`, uniformly (including the
  finite branch `N < β`).
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

theorem s81bd_pole_taylor_log {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (Λ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
      IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ x : Euc d,
        Integrable (fun y => taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)))
          (withDensityReal ρ) ∧
        |(∫ y, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ)) -
            (sphereArea d / (d : ℝ)) * ρ x * lam ^ 2 * Real.log (lam⁻¹)| ≤
          C * lam ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hA := s81bd_sphereArea_pos' hd1
  obtain ⟨C2, hC2, hK2⟩ := s81bd_taylor_cap_error hd (max M 0)
  refine ⟨C2 + (sphereArea d / d * max M 0 + sphereArea d * (Λ : ℝ) + 1) / 2, by positivity, ?_⟩
  intro ρ hρ hM hlip lam hlam0 hlam1 x
  have hM' : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hH : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam0).2 hlam1
  obtain ⟨hI1, hE1⟩ := s81bd_cap_square_log hd (max M 0) Λ ρ hρ hM' hlip lam⁻¹ hH x
  obtain ⟨hI2, hE2⟩ := hK2 ρ hρ hM' lam hlam0 hlam1 x
  set U : Euc d → ℝ := fun y => truncKernel d ((d : ℝ) / 2) lam⁻¹ (x - y) ^ 2 with hU
  set D : Euc d → ℝ := fun y => taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) -
    (1 / 2 : ℝ) * lam ^ 2 * truncKernel d ((d : ℝ) / 2) lam⁻¹ (x - y) ^ 2 with hD
  have hsplit : (fun y => taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y))) =
      fun y => D y + ((1 / 2 : ℝ) * lam ^ 2) * U y := by
    funext y; simp only [hD, hU]; ring
  have hint : Integrable (fun y => taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)))
      (withDensityReal ρ) := by
    rw [hsplit]
    exact hI2.add (hI1.const_mul _)
  refine ⟨hint, ?_⟩
  have hval : (∫ y, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ)) =
      (∫ y, D y ∂(withDensityReal ρ)) + ((1 / 2 : ℝ) * lam ^ 2) *
        ∫ y, U y ∂(withDensityReal ρ) := by
    rw [hsplit, integral_add hI2 (hI1.const_mul _), integral_const_mul]
  have key : (∫ y, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ)) -
      (sphereArea d / (d : ℝ)) * ρ x * lam ^ 2 * Real.log (lam⁻¹) =
      (∫ y, D y ∂(withDensityReal ρ)) + ((1 / 2 : ℝ) * lam ^ 2) *
        ((∫ y, U y ∂(withDensityReal ρ)) -
          (2 * sphereArea d / (d : ℝ)) * ρ x * Real.log lam⁻¹) := by
    rw [hval]; ring
  rw [key]
  have hl2 : 0 ≤ (1 / 2 : ℝ) * lam ^ 2 := by positivity
  calc |(∫ y, D y ∂(withDensityReal ρ)) + ((1 / 2 : ℝ) * lam ^ 2) *
          ((∫ y, U y ∂(withDensityReal ρ)) - (2 * sphereArea d / (d : ℝ)) * ρ x * Real.log lam⁻¹)|
      ≤ |∫ y, D y ∂(withDensityReal ρ)| + |((1 / 2 : ℝ) * lam ^ 2) *
          ((∫ y, U y ∂(withDensityReal ρ)) - (2 * sphereArea d / (d : ℝ)) * ρ x * Real.log lam⁻¹)| :=
        abs_add_le _ _
    _ ≤ C2 * lam ^ 2 + ((1 / 2 : ℝ) * lam ^ 2) *
          (sphereArea d / d * max M 0 + sphereArea d * (Λ : ℝ) + 1) := by
        refine add_le_add hE2 ?_
        rw [abs_mul, abs_of_nonneg hl2]
        exact mul_le_mul_of_nonneg_left hE1 hl2
    _ = _ := by ring

/-- The one-pole potential `g * ν` at the critical exponent is integrable and bounded. -/
theorem s81bd_kernel_int {d : ℕ} (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (x : Euc d) :
    Integrable (fun y => rieszKernel d ((d : ℝ) / 2) (x - y)) (withDensityReal ρ) ∧
      ∫ y, rieszKernel d ((d : ℝ) / 2) (x - y) ∂(withDensityReal ρ) ≤
        M * sphereArea d / ((d : ℝ) - (d : ℝ) / 2) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hL := Q34.lintegral_kernel_le hd hs0 (show (d : ℝ) / 2 < d by linarith) hρ hM x
  have hrk : ∀ z : Euc d, rieszKernel d ((d : ℝ) / 2) z = ‖z‖ ^ (-((d : ℝ) / 2)) :=
    Q34.rieszKernel_eq hs0.ne'
  have hnn : ∀ y : Euc d, 0 ≤ rieszKernel d ((d : ℝ) / 2) (x - y) := fun y => by
    rw [hrk]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hmeas : Measurable (fun y : Euc d => rieszKernel d ((d : ℝ) / 2) (x - y)) :=
    (Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hpos : 0 ≤ M * sphereArea d / ((d : ℝ) - (d : ℝ) / 2) + 1 := by
    have := Q34.sphereArea_nonneg hd
    have : 0 < (d : ℝ) - (d : ℝ) / 2 := by linarith
    positivity
  have hL' : ∫⁻ y, ENNReal.ofReal (rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - (d : ℝ) / 2) + 1) := by
    simpa only [hrk] using hL
  exact Q34.integrable_of_lintegral_le hmeas hnn hpos hL'

set_option maxHeartbeats 1600000 in
theorem s81bd_pole_taylor_beta_N {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (Λ : ℝ≥0)
    (βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
      IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
        Integrable (fun y => taylorH ((β / N) * rieszKernel d ((d : ℝ) / 2) (x - y)))
          (withDensityReal ρ) ∧
        |((N - 1 : ℕ) : ℝ) *
              (∫ y, taylorH ((β / N) * rieszKernel d ((d : ℝ) / 2) (x - y))
                ∂(withDensityReal ρ)) -
            (β ^ 2 * sphereArea d / (d : ℝ)) * ρ x * (Real.log N / N)| ≤
          C / N := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hA := s81bd_sphereArea_pos' hd1
  have hβp : 0 < βp := hβm.trans_le hβ
  obtain ⟨C1, hC1, hK⟩ := s81bd_pole_taylor_log hd (max M 0) Λ
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set Lb : ℝ := |Real.log βm| + |Real.log βp| with hLb
  set Gm : ℝ := M' * sphereArea d / ((d : ℝ) - (d : ℝ) / 2) + 1 with hGm
  have hGm0 : 0 ≤ Gm := by
    have : 0 < (d : ℝ) - (d : ℝ) / 2 := by linarith
    positivity
  set K2 : ℝ := βp * Gm + βp ^ 2 * (sphereArea d / d) * M' with hK2
  have hK20 : 0 ≤ K2 := by positivity
  refine ⟨C1 * βp ^ 2 + sphereArea d / d * M' * βp ^ 2 * (1 + Lb) + K2 * βp, by positivity, ?_⟩
  intro ρ hρ hM hlip β hβmem N hN x
  have hM' : ∀ x, ρ x ≤ M' := fun x => (hM x).trans (le_max_left _ _)
  have hβ0 : 0 < β := hβm.trans_le hβmem.1
  have hβle : β ≤ βp := hβmem.2
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hprob := Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hgI, hgle⟩ := s81bd_kernel_int hd1 hρ hM' x
  set lam : ℝ := β / N with hlam
  have hlam0 : 0 < lam := div_pos hβ0 hn0
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by positivity
  have hk0 : ∀ y : Euc d, 0 ≤ rieszKernel d ((d : ℝ) / 2) (x - y) := fun y => by
    rw [Q34.rieszKernel_eq hs0]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hmeasT : Measurable (fun y : Euc d =>
      taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y))) :=
    (by unfold taylorH; fun_prop : Measurable taylorH).comp
      (measurable_const.mul ((Q34.measurable_rieszKernel hs0).comp
        (measurable_const.sub measurable_id)))
  have hT_le : ∀ y : Euc d, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ≤
      lam * rieszKernel d ((d : ℝ) / 2) (x - y) := fun y =>
    L49.l49_H_le_self (mul_nonneg hlam0.le (hk0 y))
  have hT_nn : ∀ y : Euc d, 0 ≤ taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) := fun y =>
    L49.l49_H_nonneg _
  have hint : Integrable (fun y => taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)))
      (withDensityReal ρ) := by
    refine Integrable.mono' (hgI.const_mul lam) hmeasT.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hT_nn y)]
    exact hT_le y
  refine ⟨hint, ?_⟩
  rw [hcast]
  by_cases hcase : lam ≤ 1
  · -- the main branch `β ≤ N`
    obtain ⟨-, hE⟩ := hK ρ hρ hM' hlip lam hlam0 hcase x
    set J : ℝ := ∫ y, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ)
      with hJ
    set A : ℝ := sphereArea d with hAdef
    set a : ℝ := Real.log N with ha
    set b : ℝ := Real.log β with hb
    set n : ℝ := (N : ℝ) with hn
    have hlaminv : Real.log lam⁻¹ = a - b := by
      rw [hlam, inv_div, Real.log_div hn0.ne' hβ0.ne']
    have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
    have han : a ≤ n := by
      have := Real.log_le_sub_one_of_pos hn0
      linarith
    have hb_le : |b| ≤ Lb := by
      have h1 : Real.log βm ≤ b := Real.log_le_log hβm hβmem.1
      have h2 : b ≤ Real.log βp := Real.log_le_log hβ0 hβle
      rw [hLb]
      have := abs_nonneg (Real.log βm)
      have := abs_nonneg (Real.log βp)
      rw [abs_le]
      constructor <;> cases abs_cases (Real.log βm) <;> cases abs_cases (Real.log βp) <;> linarith
    set Q : ℝ := A / d * ρ x * lam ^ 2 * Real.log lam⁻¹ with hQ
    -- the two pieces
    have hpiece1 : |(n - 1) * (J - Q)| ≤ C1 * βp ^ 2 / n := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ n - 1)]
      calc (n - 1) * |J - Q| ≤ (n - 1) * (C1 * lam ^ 2) :=
            mul_le_mul_of_nonneg_left hE (by linarith)
        _ = C1 * β ^ 2 * ((n - 1) / n ^ 2) := by rw [hlam]; field_simp
        _ ≤ C1 * βp ^ 2 * (1 / n) := by
            have h1 : (n - 1) / n ^ 2 ≤ 1 / n := by
              rw [div_le_div_iff₀ (by positivity) hn0]; nlinarith
            have h2 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ0.le hβle 2
            have h3 : 0 ≤ (n - 1) / n ^ 2 := div_nonneg (by linarith) (by positivity)
            calc C1 * β ^ 2 * ((n - 1) / n ^ 2) ≤ C1 * βp ^ 2 * ((n - 1) / n ^ 2) := by
                  gcongr
              _ ≤ C1 * βp ^ 2 * (1 / n) := by gcongr
        _ = C1 * βp ^ 2 / n := by ring
    set Kc : ℝ := A / d * ρ x * β ^ 2 with hKc
    have hKc0 : 0 ≤ Kc := by
      have := hρ.nonneg x
      positivity
    have hKcle : Kc ≤ A / d * M' * βp ^ 2 := by
      have h2 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ0.le hβle 2
      have h3 := hM' x
      have h4 := hρ.nonneg x
      rw [hKc]
      have : 0 ≤ A / d := by positivity
      calc A / d * ρ x * β ^ 2 ≤ A / d * M' * β ^ 2 := by gcongr
        _ ≤ A / d * M' * βp ^ 2 := by gcongr
    have hpiece2eq : (n - 1) * Q - (β ^ 2 * A / d) * ρ x * (a / n) =
        -(Kc * (a + (n - 1) * b)) / n ^ 2 := by
      rw [hQ, hlaminv, hlam, hKc]
      field_simp
      ring
    have hpiece2 : |(n - 1) * Q - (β ^ 2 * A / d) * ρ x * (a / n)| ≤
        A / d * M' * βp ^ 2 * (1 + Lb) / n := by
      rw [hpiece2eq, abs_div, abs_neg, abs_mul, abs_of_nonneg hKc0, abs_of_nonneg (by positivity : (0:ℝ) ≤ n ^ 2)]
      have h1 : |a + (n - 1) * b| ≤ n * (1 + Lb) := by
        calc |a + (n - 1) * b| ≤ |a| + |(n - 1) * b| := abs_add_le _ _
          _ = a + (n - 1) * |b| := by
              rw [abs_of_nonneg ha0, abs_mul, abs_of_nonneg (by linarith : 0 ≤ n - 1)]
          _ ≤ n + n * Lb := by
              have : (n - 1) * |b| ≤ n * Lb := by
                have := abs_nonneg b
                calc (n - 1) * |b| ≤ n * |b| := by nlinarith
                  _ ≤ n * Lb := by gcongr
              linarith
          _ = n * (1 + Lb) := by ring
      have hLb0 : 0 ≤ Lb := by positivity
      calc Kc * |a + (n - 1) * b| / n ^ 2 ≤ Kc * (n * (1 + Lb)) / n ^ 2 := by gcongr
        _ = Kc * (1 + Lb) / n := by field_simp
        _ ≤ A / d * M' * βp ^ 2 * (1 + Lb) / n := by gcongr
    have hsplit : (n - 1) * J - (β ^ 2 * A / d) * ρ x * (a / n) =
        (n - 1) * (J - Q) + ((n - 1) * Q - (β ^ 2 * A / d) * ρ x * (a / n)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have hfin : C1 * βp ^ 2 / n + A / d * M' * βp ^ 2 * (1 + Lb) / n ≤
        (C1 * βp ^ 2 + A / d * M' * βp ^ 2 * (1 + Lb) + K2 * βp) / n := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hn0.le
      have : 0 ≤ K2 * βp := by positivity
      linarith
    exact (add_le_add hpiece1 hpiece2).trans hfin
  · -- the finite branch `N < β`
    push Not at hcase
    have hnb : (N : ℝ) < βp := by
      have : (N : ℝ) < β := by
        have := (lt_div_iff₀ hn0).1 hcase
        linarith
      linarith
    set A : ℝ := sphereArea d with hAdef
    set J : ℝ := ∫ y, taylorH (lam * rieszKernel d ((d : ℝ) / 2) (x - y)) ∂(withDensityReal ρ)
      with hJ
    set a : ℝ := Real.log N with ha
    set n : ℝ := (N : ℝ) with hn
    have hJ0 : 0 ≤ J := integral_nonneg hT_nn
    have hJle : J ≤ lam * Gm := by
      have h1 : J ≤ ∫ y, lam * rieszKernel d ((d : ℝ) / 2) (x - y) ∂(withDensityReal ρ) :=
        integral_mono hint (hgI.const_mul lam) hT_le
      rw [integral_const_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hgle hlam0.le)
    have hnJ : (n - 1) * J ≤ βp * Gm := by
      calc (n - 1) * J ≤ n * J := by nlinarith
        _ ≤ n * (lam * Gm) := mul_le_mul_of_nonneg_left hJle hn0.le
        _ = β * Gm := by rw [hlam]; field_simp
        _ ≤ βp * Gm := mul_le_mul_of_nonneg_right hβle hGm0
    have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
    have han : a ≤ n := by
      have := Real.log_le_sub_one_of_pos hn0
      linarith
    have hT0 : 0 ≤ (β ^ 2 * A / d) * ρ x * (a / n) := by
      have := hρ.nonneg x
      positivity
    have hTle : (β ^ 2 * A / d) * ρ x * (a / n) ≤ βp ^ 2 * (A / d) * M' := by
      have h1 : a / n ≤ 1 := (div_le_one hn0).2 han
      have h2 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ0.le hβle 2
      have h3 := hM' x
      have h4 := hρ.nonneg x
      have h5 : 0 ≤ A / d := by positivity
      calc (β ^ 2 * A / d) * ρ x * (a / n) ≤ (β ^ 2 * A / d) * ρ x * 1 := by
            gcongr
        _ = β ^ 2 * (A / d) * ρ x := by ring
        _ ≤ βp ^ 2 * (A / d) * M' := by gcongr
    have habs : |(n - 1) * J - (β ^ 2 * A / d) * ρ x * (a / n)| ≤ K2 := by
      rw [abs_le]
      constructor
      · have : 0 ≤ (n - 1) * J := mul_nonneg (by linarith) hJ0
        have : 0 ≤ βp * Gm := by positivity
        rw [hK2]; nlinarith
      · rw [hK2]; linarith
    refine habs.trans ?_
    have hKe : K2 ≤ K2 * βp / n := by
      rw [le_div_iff₀ hn0]
      nlinarith
    refine hKe.trans ?_
    refine div_le_div_of_nonneg_right ?_ hn0.le
    have h1 : 0 ≤ C1 * βp ^ 2 := by positivity
    have h2 : 0 ≤ A / d * M' * βp ^ 2 * (1 + Lb) := by positivity
    linarith

end HRS.Whole.BreakdownS81
