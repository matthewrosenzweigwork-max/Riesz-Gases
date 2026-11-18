import HRS.MS.CritForceMom14

/-!
# S8.2 NormalForm packet R04, part 1: the capped single-anchor row

`ψ_N(t) = t · min(1, K t / N)` and the estimate
`∫ ⟨z⟩^M ψ_N(pole(a,z)) dμ(z) ≤ C ⟨a⟩^M log(eN) / N`
for an arbitrary anchor `a` and a Gaussian-bounded density `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82P

open HRS HRS.Whole HRS.MS.S82N

variable {d : ℕ}

/-- The capped pole profile. -/
def s82p_psi (K : ℝ) (N : ℕ) (t : ℝ) : ℝ := t * min 1 (K * t / N)

lemma s82p_psi_nonneg (K : ℝ) (hK : 0 ≤ K) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ s82p_psi K N t := by
  unfold s82p_psi
  exact mul_nonneg ht (le_min zero_le_one (by positivity))

lemma s82p_psi_le (K : ℝ) (hK : 0 ≤ K) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : s82p_psi K N t ≤ t := by
  unfold s82p_psi
  calc t * min 1 (K * t / N) ≤ t * 1 := by gcongr; exact min_le_left _ _
    _ = t := mul_one t

lemma s82p_psi_mono (K : ℝ) (hK : 0 ≤ K) (N : ℕ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    s82p_psi K N t ≤ s82p_psi K N u := by
  unfold s82p_psi
  have h1 : min 1 (K * t / N) ≤ min 1 (K * u / N) := min_le_min_left _ (by gcongr)
  have h2 : 0 ≤ min 1 (K * t / N) := le_min zero_le_one (by positivity)
  have hu : 0 ≤ u := ht.trans htu
  calc t * min 1 (K * t / N) ≤ u * min 1 (K * t / N) := mul_le_mul_of_nonneg_right htu h2
    _ ≤ u * min 1 (K * u / N) := mul_le_mul_of_nonneg_left h1 hu

/-- The radial dominating profile. -/
def s82p_g (s B : ℝ) (r : ℝ) : ℝ := min (2 * r ^ (s - 1)) (2 * B / r)

lemma s82p_g_measurable (s B : ℝ) : Measurable (s82p_g s B) := by
  unfold s82p_g
  fun_prop

lemma s82p_g_nonneg (s B : ℝ) (hB : 0 ≤ B) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ s82p_g s B r :=
  le_min (by positivity) (by positivity)

lemma s82p_g_integrable (s B : ℝ) (hs : 0 < s) (hB : 0 < B) :
    IntervalIntegrable (s82p_g s B) volume 0 1 := by
  have h1 : IntervalIntegrable (fun r : ℝ => r ^ (s - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine (h1.const_mul 2).mono_fun (s82p_g_measurable s B).aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun r hr => ?_
  rw [Set.uIoc_of_le zero_le_one] at hr
  have hr' : 0 < r := hr.1
  have h0 : 0 ≤ s82p_g s B r := s82p_g_nonneg s B hB.le hr'.le
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg h0, abs_of_nonneg (by positivity)]
  exact min_le_left _ _

lemma s82p_int_rpow (s ρ : ℝ) (hs : 0 < s) (hρ : 0 < ρ) :
    ∫ r in (0 : ℝ)..ρ, 2 * r ^ (s - 1) = 2 * ρ ^ s / s := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have e : s - 1 + 1 = s := by ring
  rw [e, Real.zero_rpow hs.ne']
  ring

lemma s82p_int_g (s B L : ℝ) (hs : 0 < s) (hB : 0 < B) (hL0 : 0 ≤ L)
    (hL : B < 1 → Real.log (1 / B) ≤ L) :
    ∫ r in (0 : ℝ)..1, s82p_g s B r ≤ (2 * B / s) * (1 + L) := by
  have hgi := s82p_g_integrable s B hs hB
  have hi2 : ∀ ρ : ℝ, 0 < ρ →
      IntervalIntegrable (fun r : ℝ => 2 * r ^ (s - 1)) volume 0 ρ := fun ρ _ =>
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < s - 1)).const_mul 2
  by_cases hB1 : B < 1
  · set ρ0 : ℝ := B ^ s⁻¹ with hρ0
    have hρ0pos : 0 < ρ0 := Real.rpow_pos_of_pos hB _
    have hρ0lt : ρ0 < 1 := Real.rpow_lt_one hB.le hB1 (inv_pos.2 hs)
    have hρs : ρ0 ^ s = B := Real.rpow_inv_rpow hB.le hs.ne'
    have hlog : Real.log ρ0 = s⁻¹ * Real.log B := Real.log_rpow hB _
    have hsub1 : IntervalIntegrable (s82p_g s B) volume 0 ρ0 :=
      hgi.mono_set (by rw [Set.uIcc_of_le hρ0pos.le, Set.uIcc_of_le zero_le_one]
                       exact Icc_subset_Icc le_rfl hρ0lt.le)
    have hsub2 : IntervalIntegrable (s82p_g s B) volume ρ0 1 :=
      hgi.mono_set (by rw [Set.uIcc_of_le hρ0lt.le, Set.uIcc_of_le zero_le_one]
                       exact Icc_subset_Icc hρ0pos.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hsub1 hsub2]
    have b1 : ∫ r in (0 : ℝ)..ρ0, s82p_g s B r ≤ 2 * B / s := by
      calc ∫ r in (0 : ℝ)..ρ0, s82p_g s B r ≤ ∫ r in (0 : ℝ)..ρ0, 2 * r ^ (s - 1) :=
            intervalIntegral.integral_mono_on hρ0pos.le hsub1 (hi2 ρ0 hρ0pos)
              (fun r _ => min_le_left _ _)
        _ = 2 * B / s := by rw [s82p_int_rpow s ρ0 hs hρ0pos, hρs]
    have b2 : ∫ r in ρ0..1, s82p_g s B r ≤ 2 * B / s * L := by
      have hic : IntervalIntegrable (fun r : ℝ => (2 * B) * r⁻¹) volume ρ0 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hρ0lt.le]
        exact continuousOn_const.mul (continuousOn_inv₀.mono fun r hr => (hρ0pos.trans_le hr.1).ne')
      calc ∫ r in ρ0..1, s82p_g s B r ≤ ∫ r in ρ0..1, (2 * B) * r⁻¹ :=
            intervalIntegral.integral_mono_on hρ0lt.le hsub2 hic
              (fun r _ => by
                show min (2 * r ^ (s - 1)) (2 * B / r) ≤ (2 * B) * r⁻¹
                rw [← div_eq_mul_inv]; exact min_le_right _ _)
        _ = 2 * B * (-Real.log ρ0) := by
            rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hρ0pos one_pos]
            rw [one_div, Real.log_inv]
        _ = 2 * B / s * Real.log (1 / B) := by
            rw [hlog, one_div, Real.log_inv]; ring
        _ ≤ 2 * B / s * L := by
            gcongr
            exact hL hB1
    calc _ ≤ 2 * B / s + 2 * B / s * L := add_le_add b1 b2
      _ = _ := by ring
  · push Not at hB1
    calc ∫ r in (0 : ℝ)..1, s82p_g s B r ≤ ∫ r in (0 : ℝ)..1, 2 * r ^ (s - 1) :=
          intervalIntegral.integral_mono_on zero_le_one hgi (hi2 1 one_pos)
            (fun r _ => min_le_left _ _)
      _ = 2 / s := by rw [s82p_int_rpow s 1 hs one_pos]; simp
      _ ≤ (2 * B / s) * (1 + L) := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
          nlinarith

/-- The radial profile estimate. -/
lemma s82p_profile (hd : 2 ≤ d) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    r ^ (d - 1) * s82p_psi K N (1 + r ^ (-s82n_critS d)) ≤
      s82p_g (s82n_critS d) (2 * K / N) r := by
  obtain ⟨f1, f2, f3, f4⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  have hw1 : w ≤ 1 := Real.rpow_le_one hr.le hr1 hs.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hwinv : 1 ≤ w⁻¹ := (one_le_inv₀ hw0).2 hw1
  have hwinv0 : 0 < w⁻¹ := inv_pos.2 hw0
  rw [f3, f1]
  have hmono : s82p_psi K N (1 + w⁻¹) ≤ s82p_psi K N (2 * w⁻¹) :=
    s82p_psi_mono K hK N (by linarith) (by linarith)
  set m : ℝ := min 1 (K * (2 * w⁻¹) / N) with hm
  have hm1 : m ≤ 1 := min_le_left _ _
  have hm2 : m ≤ K * (2 * w⁻¹) / N := min_le_right _ _
  have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
  have hpsi : s82p_psi K N (2 * w⁻¹) = 2 * w⁻¹ * m := rfl
  have hA : w ^ 2 / r * (2 * w⁻¹) = 2 * (w / r) := by field_simp
  have hpos : 0 ≤ w ^ 2 / r := by positivity
  calc w ^ 2 / r * s82p_psi K N (1 + w⁻¹) ≤ w ^ 2 / r * (2 * w⁻¹ * m) := by
        rw [← hpsi]; exact mul_le_mul_of_nonneg_left hmono hpos
    _ ≤ _ := by
        unfold s82p_g
        rw [f2]
        refine le_min ?_ ?_
        · calc w ^ 2 / r * (2 * w⁻¹ * m) = 2 * (w / r) * m := by rw [← hA]; ring
            _ ≤ 2 * (w / r) * 1 := by gcongr
            _ = 2 * (w / r) := mul_one _
        · calc w ^ 2 / r * (2 * w⁻¹ * m) = 2 * (w / r) * m := by rw [← hA]; ring
            _ ≤ 2 * (w / r) * (K * (2 * w⁻¹) / N) := by gcongr
            _ = 2 * (2 * K / N) / r := by field_simp


lemma s82p_measurable_psi_pole (K : ℝ) (N : ℕ) (a : Euc d) :
    Measurable (fun z : Euc d => s82p_psi K N (s82n_pole a z)) := by
  have := s82n_measurable_smallRadius a
  unfold s82p_psi s82n_pole
  fun_prop

/-- The capped single-anchor row. -/
theorem s82p_anchor (hd : 2 ≤ d) (M G c K : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ a : Euc d,
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_psi K N (s82n_pole a z))
          ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * jbracket a ^ M * s82n_logN N / N) := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have hK0 : 0 ≤ K := by linarith
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Mom := s82n_Mom d M G c with hMom
  have hMom0 : 0 ≤ Mom := s82n_Mom_nonneg (by omega) M G c hM hG hc
  refine ⟨4 ^ M * G * κ * (4 * K / s82n_critS d) + 4 * K * Mom, by positivity, ?_⟩
  intro ρ hρ hρG N hN a
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL1 : 1 ≤ s82n_logN N := by
    rw [s82n_logN_eq N hN1]; have := Real.log_nonneg hN1r; linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1r
  set B : ℝ := 2 * K / N with hB
  have hBpos : 0 < B := by positivity
  have hrow := s82n_row (by omega : 1 ≤ d) M G c 1 (s82p_psi K N 2) hM hG hc one_pos le_rfl
    (s82p_psi_nonneg K hK0 N (by norm_num)) ρ hρ hρG a
    (fun z => s82p_psi K N (s82n_pole a z)) (s82p_measurable_psi_pole K N a)
    (fun r => s82p_psi K N (1 + r ^ (-s82n_critS d))) (s82p_g (s82n_critS d) B)
    (fun r hr => s82p_psi_nonneg K hK0 N (by have := Real.rpow_nonneg hr (-s82n_critS d); linarith))
    (by unfold s82p_psi; fun_prop)
    (s82p_g_integrable _ B hs hBpos)
    (fun r hr => s82p_profile hd K hK0 N hN r hr.1 hr.2.le)
    (fun z hz => by
      show s82p_psi K N (1 + s82n_smallRadius a z ^ (-s82n_critS d)) ≤ _
      rw [s82n_smallRadius_near a z hz])
    (fun z hz => by
      show s82p_psi K N (1 + s82n_smallRadius a z ^ (-s82n_critS d)) ≤ _
      have : s82n_smallRadius a z = 1 := min_eq_left hz
      rw [this, Real.one_rpow]; norm_num)
  refine hrow.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := s82p_int_g (s82n_critS d) B (Real.log N) hs hBpos hlogN0 (fun hB1 => by
    rw [hB]
    have : 1 / (2 * K / (N : ℝ)) = N / (2 * K) := by field_simp
    rw [this]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith)
  have hint' : ∫ r in (0 : ℝ)..1, s82p_g (s82n_critS d) B r ≤ 4 * K / s82n_critS d *
      s82n_logN N / N := by
    refine hint.trans (le_of_eq ?_)
    rw [s82n_logN_eq N hN1, hB]; field_simp; ring
  have hK2 : s82p_psi K N 2 ≤ 4 * K / N := by
    unfold s82p_psi
    calc 2 * min 1 (K * 2 / N) ≤ 2 * (K * 2 / N) := by gcongr; exact min_le_right _ _
      _ = 4 * K / N := by ring
  have hJ : 0 ≤ jbracket a ^ M := Real.rpow_nonneg (s82n_jb_pos a).le _
  have hg0 : 0 ≤ ∫ r in (0 : ℝ)..1, s82p_g (s82n_critS d) B r :=
    intervalIntegral.integral_nonneg zero_le_one (fun r hr => s82p_g_nonneg _ B hBpos.le hr.1)
  have hpsi0 : 0 ≤ s82p_psi K N 2 := s82p_psi_nonneg K hK0 N (by norm_num)
  have e1 : 4 ^ M * G * (κ * ∫ r in (0 : ℝ)..1, s82p_g (s82n_critS d) B r) ≤
      4 ^ M * G * (κ * (4 * K / s82n_critS d * s82n_logN N / N)) := by gcongr
  have e2 : s82p_psi K N 2 * Mom ≤ 4 * K * s82n_logN N / N * Mom := by
    refine mul_le_mul_of_nonneg_right ?_ hMom0
    refine hK2.trans ?_
    have : 4 * K / (N : ℝ) = 4 * K * 1 / N := by ring
    calc 4 * K / (N : ℝ) = 4 * K * 1 / N := this
      _ ≤ 4 * K * s82n_logN N / N := by gcongr
  calc jbracket a ^ M * (4 ^ M * G * (κ * ∫ r in (0 : ℝ)..1, s82p_g (s82n_critS d) B r) +
        s82p_psi K N 2 * Mom)
      ≤ jbracket a ^ M * (4 ^ M * G * (κ * (4 * K / s82n_critS d * s82n_logN N / N)) +
        4 * K * s82n_logN N / N * Mom) := by gcongr
    _ = _ := by ring

end HRS.MS.S82P
