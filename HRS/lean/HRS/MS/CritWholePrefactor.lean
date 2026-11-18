import HRS.MS.CritWholeOmitted

/-!
# S8.1 XS (S81c), CR05: the pole prefactor

`d(P^{x,t})^{(1)}/dμ = e^{-tλ g(x-·)} · E_P[e^{-v_Y(·)}/Z_Y]` (disintegration along one coordinate, `s81c_core`) and
`|E_P[e^{-v_Y(y)}/Z_Y] - 1| ≤ C √δ_N` from the `L^1` bound of the omitted field (CR04) and `Z_Y ≥ e^{-β M_g}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- The integrand of the prefactor. -/
def s81c_W (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1)) (x : Euc d) (t : ℝ) (Y : EucConfig d (N - 1)) (y : Euc d) : ℝ :=
  Real.exp (-field D N i Y y) / condZ D N i x t Y

theorem s81c_field_ge (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (i : Fin (N - 1))
    (Y : EucConfig d (N - 1)) (y : Euc d) :
    -(D.beta * potentialBound d ((d : ℝ) / 2) M) ≤ field D N i Y y := by
  have hs0 := s81c_hs0 hd
  have h1 : 0 ≤ (D.beta / N) * ∑ j ∈ Finset.univ.erase i, critG d (y - Y j) :=
    mul_nonneg (div_nonneg hβ0 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have h2 : D.beta * convMeasure (critG d) (mu D) y ≤ D.beta * potentialBound d ((d : ℝ) / 2) M :=
    mul_le_mul_of_nonneg_left (s81c_conv_le hd D y) hβ0
  unfold field
  linarith

theorem s81c_W_bounds (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (i : Fin (m + 1)) (x : Euc d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (Y : EucConfig d (m + 1)) (y : Euc d) :
    0 ≤ s81c_W D (m + 2) i x t Y y ∧
      s81c_W D (m + 2) i x t Y y ≤ Real.exp (2 * (D.beta * potentialBound d ((d : ℝ) / 2) M)) := by
  set K := D.beta * potentialBound d ((d : ℝ) / 2) M with hK
  obtain ⟨hz1, hz2⟩ : Real.exp (-K) ≤ condZ D (m + 2) i x t Y ∧ condZ D (m + 2) i x t Y ≤ Real.exp K := by
    rw [s81c_condZ_eq D i x t Y]; exact s81c_Z_bounds hd D hβ0 x ht (Fin.removeNth i Y)
  have hZpos : 0 < condZ D (m + 2) i x t Y := lt_of_lt_of_le (Real.exp_pos _) hz1
  refine ⟨div_nonneg (Real.exp_pos _).le hZpos.le, ?_⟩
  unfold s81c_W
  rw [div_le_iff₀ hZpos]
  calc Real.exp (-field D (m + 2) i Y y) ≤ Real.exp K := Real.exp_le_exp.2 (by
        have := s81c_field_ge hd D hβ0 (m + 2) i Y y; linarith)
    _ = Real.exp (2 * K) * Real.exp (-K) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * K) * condZ D (m + 2) i x t Y :=
        mul_le_mul_of_nonneg_left hz1 (Real.exp_pos _).le

theorem s81c_condZ_meas (hd : 1 ≤ d) (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ) :
    Measurable (fun Y : EucConfig d (m + 1) => condZ D (m + 2) i x t Y) := by
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have : (fun Y : EucConfig d (m + 1) => condZ D (m + 2) i x t Y) =
      fun Y => s81c_Zr D (m + 2) x t (Fin.removeNth i Y) := funext (s81c_condZ_eq D i x t)
  rw [this]
  exact (s81c_meas_Zr hd D _ x t).comp hrem

theorem s81c_W_meas (hd : 1 ≤ d) (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ) :
    Measurable (fun p : EucConfig d (m + 1) × Euc d => s81c_W D (m + 2) i x t p.1 p.2) := by
  unfold s81c_W
  exact (Real.measurable_exp.comp (s81b_field_meas hd D (m + 2) i).neg).div
    ((s81c_condZ_meas hd D i x t).comp measurable_fst)

theorem s81c_prefactor_eq (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ) (y : Euc d) :
    prefactor D (m + 2) i x t y = ∫ Y, s81c_W D (m + 2) i x t Y y ∂(pole D (m + 2) x t) := rfl

theorem s81c_condMean_W (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ) (φ : Euc d → ℝ)
    (Y : EucConfig d (m + 1)) :
    condMean D (m + 2) i x t φ Y =
      ∫ y, φ y * poleFactor D (m + 2) x t y * s81c_W D (m + 2) i x t Y y ∂(mu D) := by
  unfold condMean s81c_W
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem s81c_marg_density (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (i : Fin (m + 1)) (x : Euc d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    firstMarginal (pole D (m + 2) x t) = (mu D).withDensity
      (fun y => ENNReal.ofReal (poleFactor D (m + 2) x t y * prefactor D (m + 2) i x t y)) := by
  haveI := s81c_prob D
  set K : ℝ := 2 * (D.beta * potentialBound d ((d : ℝ) / 2) M) with hK
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd D hβ0 _ x ht.1
  have hpf := s81c_poleFactor_meas hd D (m + 2) x t
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hpf1 := s81c_poleFactor_le_one hd D hβ0 (m + 2) x ht.1
  have hWm := s81c_W_meas hd D i x t
  have hWb := s81c_W_bounds hd D hβ0 i x ht
  have hfm : firstMarginal (pole D (m + 2) x t) = P.map (fun Y => Y i) := by
    rw [hP]; exact (s81c_marg_coord hd D hβ0 (by omega : 2 ≤ m + 2) x ht.1 i).symm
  have hprem : Measurable (prefactor D (m + 2) i x t) := by
    have := (hWm.stronglyMeasurable).integral_prod_left' (μ := P)
    rw [hP] at this
    exact this.measurable
  rw [hfm]
  refine Measure.ext fun B hB => ?_
  rw [withDensity_apply _ hB]
  set φ : Euc d → ℝ := B.indicator (fun _ => (1 : ℝ)) with hφ
  have hφm : Measurable φ := measurable_const.indicator hB
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => by by_cases h : y ∈ B <;> simp [hφ, h]
  have hφ1 : ∀ y, φ y ≤ 1 := fun y => by by_cases h : y ∈ B <;> simp [hφ, h]
  have hφi : Integrable (fun y => φ y * poleFactor D (m + 2) x t y) (mu D) :=
    Integrable.of_bound (C := 1) (hφm.mul hpf).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ0 y) (hpf0 y))]
      calc φ y * poleFactor D (m + 2) x t y ≤ 1 * 1 := mul_le_mul (hφ1 y) (hpf1 y) (hpf0 y) zero_le_one
        _ = 1 := one_mul 1)
  have hcore := s81c_core hd D hβ0 x ht i φ hφm hφ0 hφi (fun _ => 1) measurable_const P hP
  simp only [one_mul] at hcore
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  -- the left side
  have hL : (P.map (fun Y => Y i)) B = ∫⁻ Y, ENNReal.ofReal (φ (Y i)) ∂P := by
    rw [Measure.map_apply (measurable_pi_apply i) hB, ← lintegral_indicator_one ((measurable_pi_apply i) hB)]
    refine lintegral_congr fun Y => ?_
    by_cases h : Y i ∈ B
    · have h' : Y ∈ (fun Y : EucConfig d (m + 1) => Y i) ⁻¹' B := h
      simp [Set.indicator_of_mem h', hφ, h]
    · have h' : Y ∉ (fun Y : EucConfig d (m + 1) => Y i) ⁻¹' B := h
      simp [Set.indicator_of_notMem h', hφ, h]
  rw [hL, hcore]
  -- the inner function
  have hinner : ∀ Y : EucConfig d (m + 1), ENNReal.ofReal (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) /
      s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) =
      ∫⁻ y, ENNReal.ofReal (φ y * poleFactor D (m + 2) x t y * s81c_W D (m + 2) i x t Y y) ∂(mu D) := by
    intro Y
    have e := s81c_condMean_eq D i x t φ Y
    rw [← e, s81c_condMean_W]
    refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun y =>
      mul_nonneg (mul_nonneg (hφ0 y) (hpf0 y)) (hWb Y y).1)
    refine Integrable.of_bound (C := Real.exp K) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hφm.mul hpf).mul (Measurable.of_uncurry_left hWm) |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 y) (hpf0 y)) (hWb Y y).1)]
      calc φ y * poleFactor D (m + 2) x t y * s81c_W D (m + 2) i x t Y y ≤ 1 * 1 * Real.exp K :=
            mul_le_mul (mul_le_mul (hφ1 y) (hpf1 y) (hpf0 y) zero_le_one) (hWb Y y).2 (hWb Y y).1 (by norm_num)
        _ = Real.exp K := by ring
  simp_rw [hinner]
  have hjm : Measurable (Function.uncurry fun (Y : EucConfig d (m + 1)) (y : Euc d) =>
      ENNReal.ofReal (φ y * poleFactor D (m + 2) x t y * s81c_W D (m + 2) i x t Y y)) :=
    (((hφm.comp measurable_snd).mul (hpf.comp measurable_snd)).mul hWm).ennreal_ofReal
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun y => ?_
  have hWy : Measurable fun Y : EucConfig d (m + 1) => s81c_W D (m + 2) i x t Y y :=
    Measurable.of_uncurry_right hWm
  have hWi : Integrable (fun Y : EucConfig d (m + 1) => s81c_W D (m + 2) i x t Y y) P :=
    Integrable.of_bound (C := Real.exp K) hWy.aestronglyMeasurable (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hWb Y y).1]; exact (hWb Y y).2)
  have hpre : ENNReal.ofReal (prefactor D (m + 2) i x t y) = ∫⁻ Y, ENNReal.ofReal (s81c_W D (m + 2) i x t Y y) ∂P := by
    rw [s81c_prefactor_eq, ← hP]
    exact ofReal_integral_eq_lintegral_ofReal hWi (Filter.Eventually.of_forall fun Y => (hWb Y y).1)
  have hpre0 : 0 ≤ prefactor D (m + 2) i x t y := by
    rw [s81c_prefactor_eq, ← hP]; exact integral_nonneg fun Y => (hWb Y y).1
  by_cases hy : y ∈ B
  · have hφy : φ y = 1 := by simp [hφ, hy]
    rw [Set.indicator_of_mem hy, hφy, ENNReal.ofReal_mul (hpf0 y), hpre,
      ← lintegral_const_mul _ hWy.ennreal_ofReal]
    refine lintegral_congr fun Y => ?_
    rw [one_mul, ENNReal.ofReal_mul (hpf0 y)]
  · have hφy : φ y = 0 := by simp [hφ, hy]
    simp [Set.indicator_of_notMem hy, hφy]

theorem s81c_exp_sub_one_le {u K : ℝ} (hu : u ≤ K) (hK : 0 ≤ K) : |Real.exp u - 1| ≤ Real.exp K * |u| := by
  have hK1 : 1 ≤ Real.exp K := Real.one_le_exp hK
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp u])]
    have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
      have := Real.add_one_le_exp (-u)
      have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos u]
    calc Real.exp u - 1 ≤ u * Real.exp u := h1
      _ ≤ u * Real.exp K := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hu) h
      _ = _ := mul_comm _ _
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 h])]
    have := Real.add_one_le_exp u
    nlinarith

theorem s81c_one_sub_exp_le {u : ℝ} (hu : 0 ≤ u) : 1 - Real.exp (-u) ≤ u := by
  have := Real.add_one_le_exp (-u); linarith

theorem s81c_field_integrable (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (Y : EucConfig d (N - 1)) : Integrable (fun y => field D N i Y y) (mu D) := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hsd := s81c_hsd hd
  have hj : ∀ j : Fin (N - 1), Integrable (fun y => critG d (y - Y j)) (mu D) := fun j => by
    have h := (wr13a_potential_bound hd hs0 hsd D.prob D.bound (Y j)).1
    have e : (fun y => critG d (y - Y j)) = fun y => critG d (Y j - y) := funext fun y => wr13a_g_sub_swap _ _
    rw [e]; exact h
  unfold field
  refine Integrable.sub ((integrable_finset_sum _ fun j _ => hj j).const_mul _) ?_
  exact Integrable.const_mul (Integrable.of_bound (C := potentialBound d ((d : ℝ) / 2) M)
    (s81b_conv_meas hd D).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wr13a_conv_nonneg hs0 (mu D) y)]; exact s81c_conv_le hd D y)) _

theorem s81c_Z_dev (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (i : Fin (m + 1)) (x : Euc d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : D.beta * potentialBound d ((d : ℝ) / 2) M ≤ K) (Y : EucConfig d (m + 1)) :
    |condZ D (m + 2) i x t Y - 1| ≤ Real.exp K * ∫ y, |field D (m + 2) i Y y| ∂(mu D) +
      D.beta / ((m + 2 : ℕ) : ℝ) * potentialBound d ((d : ℝ) / 2) M := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hpf := s81c_poleFactor_meas hd D (m + 2) x t
  have hpf1 := s81c_poleFactor_le_one hd D hβ0 (m + 2) x ht.1
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hfi := s81c_field_integrable hd D (m + 2) i Y
  have hfm : Measurable fun y => field D (m + 2) i Y y :=
    Measurable.of_uncurry_left (s81b_field_meas hd D (m + 2) i)
  have hlam : 0 ≤ D.beta / ((m + 2 : ℕ) : ℝ) := by positivity
  have hgI := (wr13a_potential_bound hd hs0 (s81c_hsd hd) D.prob D.bound x).1
  have hF : ∀ y, |poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) - 1| ≤
      Real.exp K * |field D (m + 2) i Y y| + D.beta / ((m + 2 : ℕ) : ℝ) * critG d (x - y) := by
    intro y
    have hp0 : 0 < poleFactor D (m + 2) x t y := Real.exp_pos _
    have e : poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) - 1 =
        poleFactor D (m + 2) x t y * (Real.exp (-field D (m + 2) i Y y) - 1) + (poleFactor D (m + 2) x t y - 1) := by ring
    have h1 : |Real.exp (-field D (m + 2) i Y y) - 1| ≤ Real.exp K * |field D (m + 2) i Y y| := by
      have := s81c_exp_sub_one_le (u := -field D (m + 2) i Y y) (K := K)
        (by have := s81c_field_ge hd D hβ0 (m + 2) i Y y; linarith) hK0
      rwa [abs_neg] at this
    have h2 : |poleFactor D (m + 2) x t y - 1| ≤ D.beta / ((m + 2 : ℕ) : ℝ) * critG d (x - y) := by
      rw [abs_of_nonpos (by linarith [hpf1 y])]
      have hu : 0 ≤ (t * (D.beta / ((m + 2 : ℕ) : ℝ))) * critG d (x - y) :=
        mul_nonneg (mul_nonneg ht.1 hlam) (wr13a_g_nonneg hs0 _)
      have := s81c_one_sub_exp_le hu
      have e2 : poleFactor D (m + 2) x t y = Real.exp (-((t * (D.beta / ((m + 2 : ℕ) : ℝ))) * critG d (x - y))) := by
        unfold poleFactor; congr 1; ring
      rw [e2]
      have h3 : (t * (D.beta / ((m + 2 : ℕ) : ℝ))) * critG d (x - y) ≤ D.beta / ((m + 2 : ℕ) : ℝ) * critG d (x - y) := by
        have : t * (D.beta / ((m + 2 : ℕ) : ℝ)) ≤ D.beta / ((m + 2 : ℕ) : ℝ) := by nlinarith [ht.2]
        exact mul_le_mul_of_nonneg_right this (wr13a_g_nonneg hs0 _)
      linarith
    rw [e]
    calc _ ≤ |poleFactor D (m + 2) x t y * (Real.exp (-field D (m + 2) i Y y) - 1)| + |poleFactor D (m + 2) x t y - 1| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos hp0]
          have : poleFactor D (m + 2) x t y * |Real.exp (-field D (m + 2) i Y y) - 1| ≤ |Real.exp (-field D (m + 2) i Y y) - 1| :=
            mul_le_of_le_one_left (abs_nonneg _) (hpf1 y)
          linarith
  have hcz : condZ D (m + 2) i x t Y - 1 =
      ∫ y, (poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) - 1) ∂(mu D) := by
    have hbd : Integrable (fun y => poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y)) (mu D) := by
      refine Integrable.of_bound (C := Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M))
        (hpf.mul (Real.measurable_exp.comp hfm.neg)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpf0 y) (Real.exp_pos _).le)]
      calc _ ≤ 1 * Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) :=
            mul_le_mul (hpf1 y) (Real.exp_le_exp.2 (by have := s81c_field_ge hd D hβ0 (m + 2) i Y y; linarith))
              (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _
    unfold condZ
    rw [integral_sub hbd (integrable_const _)]
    simp
  rw [hcz]
  have hRHS : Integrable (fun y => Real.exp K * |field D (m + 2) i Y y| +
      D.beta / ((m + 2 : ℕ) : ℝ) * critG d (x - y)) (mu D) :=
    (hfi.abs.const_mul _).add (hgI.const_mul _)
  calc |∫ y, (poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) - 1) ∂(mu D)|
      ≤ ∫ y, |poleFactor D (m + 2) x t y * Real.exp (-field D (m + 2) i Y y) - 1| ∂(mu D) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, (Real.exp K * |field D (m + 2) i Y y| + D.beta / ((m + 2 : ℕ) : ℝ) * critG d (x - y)) ∂(mu D) := by
        refine integral_mono ?_ hRHS hF
        refine Integrable.abs ?_
        refine Integrable.sub ?_ (integrable_const _)
        refine Integrable.of_bound (C := Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M))
          (hpf.mul (Real.measurable_exp.comp hfm.neg)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpf0 y) (Real.exp_pos _).le)]
        calc _ ≤ 1 * Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) :=
              mul_le_mul (hpf1 y) (Real.exp_le_exp.2 (by have := s81c_field_ge hd D hβ0 (m + 2) i Y y; linarith))
                (Real.exp_pos _).le zero_le_one
          _ = _ := one_mul _
    _ = Real.exp K * ∫ y, |field D (m + 2) i Y y| ∂(mu D) +
          D.beta / ((m + 2 : ℕ) : ℝ) * ∫ y, critG d (x - y) ∂(mu D) := by
        rw [integral_add (hfi.abs.const_mul _) (hgI.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have : ∫ y, critG d (x - y) ∂(mu D) ≤ potentialBound d ((d : ℝ) / 2) M := s81c_conv_le hd D x
        have := mul_le_mul_of_nonneg_left this hlam
        linarith

theorem s81c_field_prod_int (hd : 1 ≤ d) (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1))
    (P : Measure (EucConfig d (m + 1))) [IsProbabilityMeasure P] {c : ℝ} (hc : 0 ≤ c)
    (hI : ∀ y, Integrable (fun Y => field D (m + 2) i Y y) P)
    (hB : ∀ y, ∫ Y, |field D (m + 2) i Y y| ∂P ≤ c) :
    Integrable (fun p : EucConfig d (m + 1) × Euc d => |field D (m + 2) i p.1 p.2|) (P.prod (mu D)) ∧
      ∫ p, |field D (m + 2) i p.1 p.2| ∂(P.prod (mu D)) ≤ c := by
  haveI := s81c_prob D
  have hm : Measurable fun p : EucConfig d (m + 1) × Euc d => |field D (m + 2) i p.1 p.2| :=
    (s81b_field_meas hd D (m + 2) i).abs
  refine Q34.integrable_of_lintegral_le hm (fun p => abs_nonneg _) hc ?_
  rw [lintegral_prod_symm _ hm.ennreal_ofReal.aemeasurable]
  calc ∫⁻ y, ∫⁻ Y, ENNReal.ofReal |field D (m + 2) i Y y| ∂P ∂(mu D) ≤ ∫⁻ _y, ENNReal.ofReal c ∂(mu D) := by
        refine lintegral_mono fun y => ?_
        have h := ofReal_integral_eq_lintegral_ofReal (hI y).abs (Filter.Eventually.of_forall fun Y => abs_nonneg _)
        exact (le_of_eq h.symm).trans (ENNReal.ofReal_le_ofReal (hB y))
    _ = ENNReal.ofReal c := by simp

set_option maxHeartbeats 800000 in
theorem s81c_prefactor_dev (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1), ∀ x : Euc d,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Euc d,
        |prefactor D N i x t y - 1| ≤ C * Real.sqrt (deltaN d ((d : ℝ) / 2) N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C4, hC40, hC4⟩ := s81c_omitted_field_L1 hd M βm βp hβm hβ
  set Mg : ℝ := potentialBound d ((d : ℝ) / 2) M with hMg
  have hβp : 0 < βp := hβm.trans_le hβ
  set K : ℝ := βp * |Mg| with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * Real.exp (2 * K) * C4 + Real.exp K * (βp * |Mg|), by positivity, fun D N hN i x t ht y => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hMg0 : 0 ≤ Mg := s81c_Mg_nonneg hd1 D
  have hDK : D.beta * Mg ≤ K := mul_le_mul hββp (le_abs_self _) hMg0 hβp.le
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1
  obtain ⟨hn1, hn2, -, -, -⟩ := s81c_num_facts hd1 hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδ
  set s : ℝ := Real.sqrt δ with hs
  have hδ0 : 0 ≤ δ := (inv_nonneg.2 (Nat.cast_nonneg _)).trans hn1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hδs : δ ≤ s := by
    have : s * s = δ := Real.mul_self_sqrt hδ0
    have : s ≤ 1 := Real.sqrt_le_one.2 hn2 |>.trans le_rfl
    nlinarith
  have hoy : ∀ y', Integrable (fun Y => field D (m + 2) i Y y') P ∧ ∫ Y, |field D (m + 2) i Y y'| ∂P ≤ C4 * s := by
    intro y'
    have h := hC4 D (m + 2) hN i x t ht y'
    rw [← hP] at h
    exact h
  obtain ⟨hprodI, hprodB⟩ := s81c_field_prod_int hd1 D i P (c := C4 * s) (by positivity)
    (fun y' => (hoy y').1) (fun y' => (hoy y').2)
  have hBint : Integrable (fun Y => ∫ y', |field D (m + 2) i Y y'| ∂(mu D)) P :=
    hprodI.integral_prod_left
  have hBB : ∫ Y, ∫ y', |field D (m + 2) i Y y'| ∂(mu D) ∂P ≤ C4 * s := by
    rw [← integral_prod (f := fun p : EucConfig d (m + 1) × Euc d => |field D (m + 2) i p.1 p.2|) hprodI]
    exact hprodB
  -- pointwise estimate of |W - 1|
  have hpt : ∀ Y : EucConfig d (m + 1), |s81c_W D (m + 2) i x t Y y - 1| ≤
      Real.exp K * (Real.exp K * |field D (m + 2) i Y y|) +
        Real.exp K * (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Mg) := by
    intro Y
    obtain ⟨hz1, hz2⟩ : Real.exp (-(D.beta * Mg)) ≤ condZ D (m + 2) i x t Y ∧ condZ D (m + 2) i x t Y ≤ Real.exp (D.beta * Mg) := by
      rw [s81c_condZ_eq D i x t Y]; exact s81c_Z_bounds hd1 D hβ0.le x ht (Fin.removeNth i Y)
    have hZpos : 0 < condZ D (m + 2) i x t Y := lt_of_lt_of_le (Real.exp_pos _) hz1
    have hZK : Real.exp (-K) ≤ condZ D (m + 2) i x t Y :=
      le_trans (Real.exp_le_exp.2 (by linarith)) hz1
    have h1 : |Real.exp (-field D (m + 2) i Y y) - 1| ≤ Real.exp K * |field D (m + 2) i Y y| := by
      have := s81c_exp_sub_one_le (u := -field D (m + 2) i Y y) (K := K)
        (by have := s81c_field_ge hd1 D hβ0.le (m + 2) i Y y; linarith) hK0
      rwa [abs_neg] at this
    have h2 := s81c_Z_dev hd1 D hβ0.le i x ht hK0 hDK Y
    have e : s81c_W D (m + 2) i x t Y y - 1 =
        (Real.exp (-field D (m + 2) i Y y) - condZ D (m + 2) i x t Y) / condZ D (m + 2) i x t Y := by
      unfold s81c_W; field_simp
    rw [e, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    have h3 : |Real.exp (-field D (m + 2) i Y y) - condZ D (m + 2) i x t Y| ≤
        Real.exp K * |field D (m + 2) i Y y| + (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Mg) := by
      have : Real.exp (-field D (m + 2) i Y y) - condZ D (m + 2) i x t Y =
          (Real.exp (-field D (m + 2) i Y y) - 1) - (condZ D (m + 2) i x t Y - 1) := by ring
      rw [this]
      calc _ ≤ |Real.exp (-field D (m + 2) i Y y) - 1| + |condZ D (m + 2) i x t Y - 1| := abs_sub _ _
        _ ≤ _ := add_le_add h1 h2
    have h4 : 1 ≤ Real.exp K * condZ D (m + 2) i x t Y := by
      calc (1 : ℝ) = Real.exp K * Real.exp (-K) := by rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hZK (Real.exp_pos _).le
    have hA : 0 ≤ Real.exp K * |field D (m + 2) i Y y| + (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Mg) := by
      have : 0 ≤ ∫ y', |field D (m + 2) i Y y'| ∂(mu D) := integral_nonneg fun _ => abs_nonneg _
      have : 0 ≤ D.beta / ((m + 2 : ℕ) : ℝ) * Mg := by positivity
      positivity
    calc _ ≤ Real.exp K * |field D (m + 2) i Y y| + (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Mg) := h3
      _ ≤ (Real.exp K * condZ D (m + 2) i x t Y) * (Real.exp K * |field D (m + 2) i Y y| +
          (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) + D.beta / ((m + 2 : ℕ) : ℝ) * Mg)) :=
        le_mul_of_one_le_left hA h4
      _ = _ := by ring
  have hWy : Measurable fun Y : EucConfig d (m + 1) => s81c_W D (m + 2) i x t Y y :=
    Measurable.of_uncurry_right (s81c_W_meas hd1 D i x t)
  have hWb := s81c_W_bounds hd1 D hβ0.le i x ht
  have hWi : Integrable (fun Y : EucConfig d (m + 1) => s81c_W D (m + 2) i x t Y y) P :=
    Integrable.of_bound (C := Real.exp (2 * (D.beta * Mg))) hWy.aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWb Y y).1]; exact (hWb Y y).2)
  have hpre : prefactor D (m + 2) i x t y - 1 = ∫ Y, (s81c_W D (m + 2) i x t Y y - 1) ∂P := by
    rw [integral_sub hWi (integrable_const _), s81c_prefactor_eq, ← hP]
    simp
  have hA1 := (hoy y).1.abs
  set lam : ℝ := D.beta / ((m + 2 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlams : lam ≤ βp * s := by
    have h1 : lam ≤ βp * δ := by
      rw [hlam, div_eq_mul_inv]
      exact mul_le_mul hββp hn1 (inv_nonneg.2 (Nat.cast_nonneg _)) hβp.le
    exact h1.trans (mul_le_mul_of_nonneg_left hδs hβp.le)
  have hRint : Integrable (fun Y : EucConfig d (m + 1) => Real.exp K * (Real.exp K * |field D (m + 2) i Y y|) +
      Real.exp K * (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) + lam * Mg)) P :=
    (hA1.const_mul _ |>.const_mul _).add (((hBint.const_mul _).add (integrable_const _)).const_mul _)
  rw [hpre]
  calc |∫ Y, (s81c_W D (m + 2) i x t Y y - 1) ∂P| ≤ ∫ Y, |s81c_W D (m + 2) i x t Y y - 1| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ Y, (Real.exp K * (Real.exp K * |field D (m + 2) i Y y|) +
          Real.exp K * (Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D) + lam * Mg)) ∂P :=
        integral_mono (hWi.sub (integrable_const _)).abs hRint hpt
    _ = Real.exp K * (Real.exp K * ∫ Y, |field D (m + 2) i Y y| ∂P) +
          Real.exp K * (Real.exp K * ∫ Y, ∫ y', |field D (m + 2) i Y y'| ∂(mu D) ∂P + lam * Mg) := by
        have hf1 : Integrable (fun Y : EucConfig d (m + 1) => Real.exp K * (Real.exp K * |field D (m + 2) i Y y|)) P :=
          hA1.const_mul _ |>.const_mul _
        have hf2 : Integrable (fun Y : EucConfig d (m + 1) => Real.exp K * (Real.exp K *
            ∫ y', |field D (m + 2) i Y y'| ∂(mu D) + lam * Mg)) P :=
          ((hBint.const_mul _).add (integrable_const _)).const_mul _
        have h := integral_add (μ := P) hf1 hf2
        refine h.trans ?_
        have e1 : ∫ Y : EucConfig d (m + 1), Real.exp K * (Real.exp K * |field D (m + 2) i Y y|) ∂P =
            Real.exp K * (Real.exp K * ∫ Y, |field D (m + 2) i Y y| ∂P) := by
          rw [integral_const_mul, integral_const_mul]
        have e2 : ∫ Y : EucConfig d (m + 1), Real.exp K * (Real.exp K *
            ∫ y', |field D (m + 2) i Y y'| ∂(mu D) + lam * Mg) ∂P =
            Real.exp K * (Real.exp K * ∫ Y, ∫ y', |field D (m + 2) i Y y'| ∂(mu D) ∂P + lam * Mg) := by
          have hBc : Integrable (fun Y : EucConfig d (m + 1) =>
              Real.exp K * ∫ y', |field D (m + 2) i Y y'| ∂(mu D)) P := hBint.const_mul _
          rw [integral_const_mul, integral_add hBc (integrable_const _), integral_const_mul]
          simp
        rw [e1, e2]
    _ ≤ Real.exp K * (Real.exp K * (C4 * s)) + Real.exp K * (Real.exp K * (C4 * s) + lam * Mg) := by
        have h1 := (hoy y).2
        gcongr
    _ ≤ _ := by
        have hlM : lam * Mg ≤ βp * |Mg| * s := by
          calc lam * Mg ≤ lam * |Mg| := mul_le_mul_of_nonneg_left (le_abs_self _) hlam0
            _ ≤ βp * s * |Mg| := mul_le_mul_of_nonneg_right hlams (abs_nonneg _)
            _ = _ := by ring
        have he : Real.exp K * Real.exp K = Real.exp (2 * K) := by rw [← Real.exp_add]; congr 1; ring
        have hE0 : 0 ≤ Real.exp K := (Real.exp_pos _).le
        nlinarith [mul_le_mul_of_nonneg_left hlM hE0, mul_nonneg hC40 hs0, mul_nonneg hE0 (mul_nonneg hC40 hs0)]

/-- CR05: the pole prefactor. -/
theorem s81c_pole_prefactor (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Measurable (prefactor D N i x t) ∧
        firstMarginal (pole D N x t) = (mu D).withDensity
          (fun y => ENNReal.ofReal (poleFactor D N x t y * prefactor D N i x t y)) ∧
        ∀ y, |prefactor D N i x t y - 1| ≤
          C * Real.sqrt (deltaN d ((d : ℝ) / 2) N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC0, hC⟩ := s81c_prefactor_dev hd M βm βp hβm hβ
  refine ⟨C, hC0, fun D N hN i x t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  refine ⟨?_, s81c_marg_density hd1 D hβ0.le i x ht, fun y => hC D (m + 2) hN i x t ht y⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1
  have := (s81c_W_meas hd1 D i x t).stronglyMeasurable.integral_prod_left' (μ := P)
  rw [hP] at this
  exact this.measurable

end HRS.Whole.S81b
