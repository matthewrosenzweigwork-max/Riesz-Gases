import HRS.MS.S104eC3E

/-!
# S104E route C, packet C3, file F: the abstract time-continuity estimate for weakly singular integrals

`s104c3_TC_core`: if `Ψ r = ∫_0^{t-r} K(h, r+h) dh` with `‖K(h,r+h)‖ ≤ C k(h)` and
`‖K(h,r+h) - K(h,r'+h)‖ ≤ ε' k(h)` for `|r-r'|` small (`k = 1 + h^{-(1+η)/2}`), then `Ψ` is uniformly continuous.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

theorem s104c3_k_antitone {η : ℝ} (hη0 : 0 < η) {h : ℝ} (hh : 0 < h) {a : ℝ} (ha : 0 ≤ a) :
    s104c3_k η (h + a) ≤ s104c3_k η h := by
  unfold s104c3_k
  have := Real.rpow_le_rpow_of_nonpos hh (by linarith : h ≤ h + a)
    (by linarith : -((1 + η) / 2) ≤ 0)
  linarith

theorem s104c3_k_prim_small {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) {θ : ℝ} (hθ : 0 < θ) :
    ∃ s : ℝ, 0 < s ∧ ∫ h in (0 : ℝ)..s, s104c3_k η h ≤ θ := by
  have hc := intervalIntegral.continuous_primitive (f := fun h => s104c3_k η h) (μ := volume)
    (fun a b => s104c3_k_int hη1 hη0 a b) 0
  obtain ⟨s, hs, hball⟩ := Metric.continuous_iff.1 hc 0 θ hθ
  refine ⟨s / 2, by linarith, ?_⟩
  have := hball (s / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  simp only [intervalIntegral.integral_same, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

theorem s104c3_int_k_shift {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∫ h in a..(a + s), s104c3_k η h ≤ ∫ h in (0 : ℝ)..s, s104c3_k η h := by
  have e := intervalIntegral.integral_comp_add_right (fun h => s104c3_k η h) (a := 0) (b := s) a
  simp only [zero_add] at e
  have e2 : ∫ h in a..(a + s), s104c3_k η h = ∫ h in (0 : ℝ)..s, s104c3_k η (h + a) := by
    rw [e, add_comm a s]
  rw [e2]
  refine intervalIntegral.integral_mono_on_of_le_Ioo hs ?_ (s104c3_k_int hη1 hη0 0 s) ?_
  · simpa using (s104c3_k_int hη1 hη0 a (s + a)).comp_add_right a
  · intro x hx
    exact s104c3_k_antitone hη0 hx.1 ha

theorem s104c3_TC_core {G Y : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) {t H : ℝ} (ht : 0 ≤ t) (htH : t ≤ H) (Kt : Y → ℝ → ℝ → G) {C : ℝ}
    (hC : 0 ≤ C)
    (hint : ∀ y : Y, ∀ r ∈ Icc 0 t, IntervalIntegrable (fun h => Kt y h (h + r)) volume 0 (t - r))
    (ha : ∀ y : Y, ∀ r ∈ Icc 0 t, ∀ h ∈ Ioc 0 (t - r), ‖Kt y h (h + r)‖ ≤ C * s104c3_k η h)
    (hb : ∀ ε' : ℝ, 0 < ε' → ∃ δ' : ℝ, 0 < δ' ∧ ∀ y : Y, ∀ r ∈ Icc 0 t, ∀ r' ∈ Icc 0 t, r ≤ r' → r' - r < δ' →
      ∀ h ∈ Ioc 0 (t - r'), ‖Kt y h (h + r) - Kt y h (h + r')‖ ≤ ε' * s104c3_k η h) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : Y, ∀ r ∈ Icc 0 t, ∀ r' ∈ Icc 0 t, r ≤ r' → r' - r < δ →
      ‖(∫ h in (0 : ℝ)..(t - r), Kt y h (h + r)) - ∫ h in (0 : ℝ)..(t - r'), Kt y h (h + r')‖ ≤ ε := by
  intro ε hε
  have hM : 0 ≤ ∫ h in (0 : ℝ)..H, s104c3_k η h :=
    intervalIntegral.integral_nonneg (by linarith) fun h hh => s104c3_k_nonneg η hh.1
  set M := ∫ h in (0 : ℝ)..H, s104c3_k η h with hMdef
  obtain ⟨s, hs, hsk⟩ := s104c3_k_prim_small hη1 hη0 (θ := ε / (2 * (C + 1))) (by positivity)
  obtain ⟨δ', hδ', hb'⟩ := hb (ε / (2 * (M + 1))) (by positivity)
  refine ⟨min s δ', lt_min hs hδ', fun y r hr r' hr' hrr hd => ?_⟩
  have hd1 : r' - r < s := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : r' - r < δ' := lt_of_lt_of_le hd (min_le_right _ _)
  have h0r' : 0 ≤ t - r' := by linarith [hr'.2]
  have hle : t - r' ≤ t - r := by linarith
  have hint_r := hint y r hr
  have hint_r' := hint y r' hr'
  have hA : IntervalIntegrable (fun h => Kt y h (h + r)) volume 0 (t - r') :=
    hint_r.mono_set (by rw [uIcc_of_le h0r', uIcc_of_le (h0r'.trans hle)]; exact Icc_subset_Icc le_rfl hle)
  have hB : IntervalIntegrable (fun h => Kt y h (h + r)) volume (t - r') (t - r) :=
    hint_r.mono_set (by
      rw [uIcc_of_le hle, uIcc_of_le (h0r'.trans hle)]; exact Icc_subset_Icc h0r' le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hdiff : (∫ h in (0 : ℝ)..(t - r), Kt y h (h + r)) - ∫ h in (0 : ℝ)..(t - r'), Kt y h (h + r') =
      (∫ h in (0 : ℝ)..(t - r'), (Kt y h (h + r) - Kt y h (h + r'))) + ∫ h in (t - r')..(t - r), Kt y h (h + r) := by
    rw [intervalIntegral.integral_sub hA hint_r', ← hsplit]; abel
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  have hkint := s104c3_k_int hη1 hη0
  -- first piece
  have h1 : ‖∫ h in (0 : ℝ)..(t - r'), (Kt y h (h + r) - Kt y h (h + r'))‖ ≤
      ε / (2 * (M + 1)) * M := by
    have := intervalIntegral.norm_integral_le_of_norm_le h0r'
      (ae_of_all _ fun h hh => hb' y r hr r' hr' hrr hd2 h hh) ((hkint 0 (t - r')).const_mul (ε / (2 * (M + 1))))
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.integral_mono_interval le_rfl h0r' (by linarith [hr'.2, hr.1]) ?_ (hkint 0 H)
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun h hh => s104c3_k_nonneg η hh.1.le)
  -- second piece
  have h2 : ‖∫ h in (t - r')..(t - r), Kt y h (h + r)‖ ≤ ε / (2 * (C + 1)) * C := by
    have := intervalIntegral.norm_integral_le_of_norm_le hle
      (ae_of_all _ fun h hh => ha y r hr h ⟨lt_of_le_of_lt h0r' hh.1, hh.2⟩)
      ((hkint (t - r') (t - r)).const_mul C)
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hsh := s104c3_int_k_shift hη1 hη0 h0r' (by linarith : 0 ≤ r' - r)
    have e : t - r' + (r' - r) = t - r := by ring
    rw [e] at hsh
    have hmono : ∫ h in (0 : ℝ)..(r' - r), s104c3_k η h ≤ ∫ h in (0 : ℝ)..s, s104c3_k η h := by
      refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hd1.le ?_ (hkint 0 s)
      exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun h hh => s104c3_k_nonneg η hh.1.le)
    have hfin : ∫ h in (t - r')..(t - r), s104c3_k η h ≤ ε / (2 * (C + 1)) := hsh.trans (hmono.trans hsk)
    calc C * ∫ h in (t - r')..(t - r), s104c3_k η h ≤ C * (ε / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hfin hC
      _ = _ := by ring
  have h3 : ε / (2 * (M + 1)) * M ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : ε / (2 * (C + 1)) * C ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end HRS.MS.S104e.C
