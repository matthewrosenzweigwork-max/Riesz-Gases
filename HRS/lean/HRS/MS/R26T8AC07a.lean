import HRS.MS.R26T8AC08a

/-!
# S8.2 observed-time layer, packet T8A.C07a: two-centre power integrals

For `‖e‖ = D > 0` and `0 ≤ p, p' < d`, `∫⁻_{‖w‖<R} ‖w‖^{-p} ‖w - e‖^{-p'} dw` is bounded by four radial pieces: the balls of radius `D/2`
around `0` and `e`, the shell `D/2 < ‖w‖ ≤ 2D` (volume), and the far region `‖w‖ > 2D` where `‖w - e‖ ≥ ‖w‖/2`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A

theorem r26t8a_c07a_two_center (d : ℕ) (hd : 1 ≤ d) {p p' : ℝ} (hp0 : 0 ≤ p) (hp : p < d)
    (hp0' : 0 ≤ p') (hp' : p' < d) {D R : ℝ} (hD : 0 < D) (e : EucC8 d) (he : ‖e‖ = D) :
    ∫⁻ w : EucC8 d, ENNReal.ofReal ((Set.Ioc 0 R).indicator
        (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p')) ≤
      ENNReal.ofReal ((D / 2) ^ (-p')) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - p)) +
      ENNReal.ofReal ((D / 2) ^ (-p)) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - p')) +
      ENNReal.ofReal ((D / 2) ^ (-(p + p'))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0)) +
      ENNReal.ofReal (2 ^ p') *
        ENNReal.ofReal (r26t8a_c08a_const d *
          ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - (p + p'))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hD2 : 0 < D / 2 := by positivity
  have hrad : ∀ (S : Set ℝ) (a : ℝ), MeasurableSet S →
      Measurable fun z : EucC8 d => ENNReal.ofReal (S.indicator (fun r => r ^ a) ‖z‖) := fun S a hS =>
    ENNReal.measurable_ofReal.comp (((measurable_id.pow_const a).indicator hS).comp measurable_norm)
  set Ia : ℝ → ℝ := (Set.Ioc 0 (D / 2)).indicator (fun r => r ^ (-p)) with hIa
  set Ib : ℝ → ℝ := (Set.Ioc 0 (D / 2)).indicator (fun r => r ^ (-p')) with hIb
  set Ic : ℝ → ℝ := (Set.Ioc 0 (2 * D)).indicator (fun r => r ^ (-(0 : ℝ))) with hIc
  set Id : ℝ → ℝ := (Set.Ioc (2 * D) (max (2 * D) R)).indicator (fun r => r ^ (-(p + p'))) with hId
  have hIam := hrad (Set.Ioc 0 (D / 2)) (-p) measurableSet_Ioc
  have hIbm := hrad (Set.Ioc 0 (D / 2)) (-p') measurableSet_Ioc
  have hIcm := hrad (Set.Ioc 0 (2 * D)) (-(0 : ℝ)) measurableSet_Ioc
  have hIdm := hrad (Set.Ioc (2 * D) (max (2 * D) R)) (-(p + p')) measurableSet_Ioc
  set F1 : EucC8 d → ℝ≥0∞ := fun w => ENNReal.ofReal ((D / 2) ^ (-p')) * ENNReal.ofReal (Ia ‖w‖) with hF1
  set F2 : EucC8 d → ℝ≥0∞ := fun w => ENNReal.ofReal ((D / 2) ^ (-p)) * ENNReal.ofReal (Ib ‖w - e‖) with hF2
  set F3 : EucC8 d → ℝ≥0∞ := fun w => ENNReal.ofReal ((D / 2) ^ (-(p + p'))) * ENNReal.ofReal (Ic ‖w‖) with hF3
  set F4 : EucC8 d → ℝ≥0∞ := fun w => ENNReal.ofReal (2 ^ p') * ENNReal.ofReal (Id ‖w‖) with hF4
  have hF1m : Measurable F1 := measurable_const.mul hIam
  have hIbe : Measurable fun w : EucC8 d => ENNReal.ofReal (Ib ‖w - e‖) :=
    hIbm.comp (measurable_id.sub_const e)
  have hF2m : Measurable F2 := measurable_const.mul hIbe
  have hF3m : Measurable F3 := measurable_const.mul hIcm
  have hF4m : Measurable F4 := measurable_const.mul hIdm
  have hne : ∀ᵐ w ∂(volume : Measure (EucC8 d)), w ≠ 0 ∧ w ≠ e := by
    have h0 : ∀ᵐ w ∂(volume : Measure (EucC8 d)), w ≠ 0 := by rw [ae_iff]; simp
    have h1 : ∀ᵐ w ∂(volume : Measure (EucC8 d)), w ≠ e := by rw [ae_iff]; simp
    filter_upwards [h0, h1] with w a b using ⟨a, b⟩
  have hpoint : ∀ᵐ w ∂(volume : Measure (EucC8 d)),
      ENNReal.ofReal ((Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p')) ≤
        F1 w + F2 w + F3 w + F4 w := by
    filter_upwards [hne] with w ⟨hw0, hwe⟩
    have ha : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hb : 0 < ‖w - e‖ := norm_pos_iff.2 (sub_ne_zero.2 hwe)
    have htri : D ≤ ‖w‖ + ‖w - e‖ := by
      rw [← he]
      calc ‖e‖ = ‖w - (w - e)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w - e‖ := norm_sub_le _ _
    have htri2 : ‖w‖ ≤ ‖w - e‖ + D := by
      rw [← he]
      calc ‖w‖ = ‖(w - e) + e‖ := by congr 1; abel
        _ ≤ ‖w - e‖ + ‖e‖ := norm_add_le _ _
    have hindle : (Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ ≤ ‖w‖ ^ (-p) :=
      indicator_le_self' (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have hind0 : 0 ≤ (Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have hbnn : 0 ≤ ‖w - e‖ ^ (-p') := Real.rpow_nonneg (norm_nonneg _) _
    have mono : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z :=
      fun hx hxy hz => Real.rpow_le_rpow_of_nonpos hx hxy hz
    by_cases h1 : ‖w‖ ≤ D / 2
    · have hb2 : D / 2 ≤ ‖w - e‖ := by linarith
      have h2 : ‖w - e‖ ^ (-p') ≤ (D / 2) ^ (-p') := mono hD2 hb2 (by linarith)
      have hIaw : Ia ‖w‖ = ‖w‖ ^ (-p) := indicator_of_mem (show ‖w‖ ∈ Set.Ioc 0 (D / 2) from ⟨ha, h1⟩) _
      calc ENNReal.ofReal ((Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p'))
          ≤ ENNReal.ofReal ((D / 2) ^ (-p')) * ENNReal.ofReal (Ia ‖w‖) := by
            rw [hIaw, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2.le _)]
            refine ENNReal.ofReal_le_ofReal ?_
            calc _ ≤ ‖w‖ ^ (-p) * ‖w - e‖ ^ (-p') := mul_le_mul_of_nonneg_right hindle hbnn
              _ ≤ ‖w‖ ^ (-p) * (D / 2) ^ (-p') :=
                  mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) _)
              _ = _ := mul_comm _ _
        _ = F1 w := rfl
        _ ≤ _ := (le_self_add.trans le_self_add).trans le_self_add
    · push_neg at h1
      by_cases h2 : ‖w - e‖ ≤ D / 2
      · have ha2 : D / 2 ≤ ‖w‖ := by linarith
        have h3 : ‖w‖ ^ (-p) ≤ (D / 2) ^ (-p) := mono hD2 ha2 (by linarith)
        have hIbw : Ib ‖w - e‖ = ‖w - e‖ ^ (-p') :=
          indicator_of_mem (show ‖w - e‖ ∈ Set.Ioc 0 (D / 2) from ⟨hb, h2⟩) _
        calc ENNReal.ofReal ((Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p'))
            ≤ ENNReal.ofReal ((D / 2) ^ (-p)) * ENNReal.ofReal (Ib ‖w - e‖) := by
              rw [hIbw, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2.le _)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc _ ≤ ‖w‖ ^ (-p) * ‖w - e‖ ^ (-p') := mul_le_mul_of_nonneg_right hindle hbnn
                _ ≤ (D / 2) ^ (-p) * ‖w - e‖ ^ (-p') := mul_le_mul_of_nonneg_right h3 hbnn
          _ = F2 w := rfl
          _ ≤ _ := ((le_add_self).trans le_self_add).trans le_self_add
      · push_neg at h2
        by_cases h3 : ‖w‖ ≤ 2 * D
        · have h4 : ‖w‖ ^ (-p) ≤ (D / 2) ^ (-p) := mono hD2 h1.le (by linarith)
          have h5 : ‖w - e‖ ^ (-p') ≤ (D / 2) ^ (-p') := mono hD2 h2.le (by linarith)
          have hIcw : Ic ‖w‖ = 1 := by
            have : Ic ‖w‖ = ‖w‖ ^ (-(0 : ℝ)) :=
              indicator_of_mem (show ‖w‖ ∈ Set.Ioc 0 (2 * D) from ⟨ha, h3⟩) _
            rw [this]; simp
          calc ENNReal.ofReal ((Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p'))
              ≤ ENNReal.ofReal ((D / 2) ^ (-(p + p'))) * ENNReal.ofReal (Ic ‖w‖) := by
                rw [hIcw, ENNReal.ofReal_one, mul_one]
                refine ENNReal.ofReal_le_ofReal ?_
                calc _ ≤ ‖w‖ ^ (-p) * ‖w - e‖ ^ (-p') := mul_le_mul_of_nonneg_right hindle hbnn
                  _ ≤ (D / 2) ^ (-p) * (D / 2) ^ (-p') :=
                      mul_le_mul h4 h5 hbnn (Real.rpow_nonneg hD2.le _)
                  _ = (D / 2) ^ (-(p + p')) := by
                      rw [← Real.rpow_add hD2]; congr 1; ring
            _ = F3 w := rfl
            _ ≤ _ := le_add_self.trans le_self_add
        · push_neg at h3
          have hb3 : ‖w‖ / 2 ≤ ‖w - e‖ := by linarith
          have h5 : ‖w - e‖ ^ (-p') ≤ (‖w‖ / 2) ^ (-p') := mono (by positivity) hb3 (by linarith)
          have h6 : (‖w‖ / 2) ^ (-p') = 2 ^ p' * ‖w‖ ^ (-p') := by
            rw [Real.div_rpow ha.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              div_inv_eq_mul, mul_comm]
          by_cases h7 : ‖w‖ ≤ R
          · have hIdw : Id ‖w‖ = ‖w‖ ^ (-(p + p')) :=
              indicator_of_mem (show ‖w‖ ∈ Set.Ioc (2 * D) (max (2 * D) R) from
                ⟨h3, h7.trans (le_max_right _ _)⟩) _
            have hball : (Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ = ‖w‖ ^ (-p) :=
              indicator_of_mem (show ‖w‖ ∈ Set.Ioc 0 R from ⟨ha, h7⟩) _
            calc ENNReal.ofReal ((Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p'))
                ≤ ENNReal.ofReal (2 ^ p') * ENNReal.ofReal (Id ‖w‖) := by
                  rw [hIdw, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hball]
                  refine ENNReal.ofReal_le_ofReal ?_
                  calc ‖w‖ ^ (-p) * ‖w - e‖ ^ (-p') ≤ ‖w‖ ^ (-p) * (2 ^ p' * ‖w‖ ^ (-p')) := by
                        rw [← h6]; exact mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg (norm_nonneg _) _)
                    _ = 2 ^ p' * ‖w‖ ^ (-(p + p')) := by
                        rw [show -(p + p') = -p + -p' by ring, Real.rpow_add ha]; ring
              _ = F4 w := rfl
              _ ≤ _ := le_add_self
          · push_neg at h7
            have hball : (Set.Ioc 0 R).indicator (fun r => r ^ (-p)) ‖w‖ = 0 :=
              indicator_of_notMem (fun h => absurd h.2 (not_le.2 h7)) _
            rw [hball, zero_mul, ENNReal.ofReal_zero]
            exact zero_le
  calc ∫⁻ w : EucC8 d, ENNReal.ofReal ((Set.Ioc 0 R).indicator
        (fun r => r ^ (-p)) ‖w‖ * ‖w - e‖ ^ (-p'))
      ≤ ∫⁻ w, (F1 w + F2 w + F3 w + F4 w) := lintegral_mono_ae hpoint
    _ = (∫⁻ w, F1 w) + (∫⁻ w, F2 w) + (∫⁻ w, F3 w) + (∫⁻ w, F4 w) := by
        rw [lintegral_add_right _ hF4m, lintegral_add_right _ hF3m, lintegral_add_right _ hF2m]
    _ = _ := by
        have e1 : ∫⁻ w, F1 w = ENNReal.ofReal ((D / 2) ^ (-p')) *
            ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - p)) := by
          simp only [hF1]
          rw [lintegral_const_mul _ hIam]
          congr 1
          exact r26t8a_c08a_radial d hd (p := p) (ε := 0) (δ := D / 2) le_rfl hD2.le (Or.inr hp)
        have e2 : ∫⁻ w, F2 w = ENNReal.ofReal ((D / 2) ^ (-p)) *
            ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - p')) := by
          simp only [hF2]
          rw [lintegral_const_mul _ hIbe]
          congr 1
          have := lintegral_sub_right_eq_self (μ := (volume : Measure (EucC8 d)))
            (fun z : EucC8 d => ENNReal.ofReal (Ib ‖z‖)) e
          rw [this]
          exact r26t8a_c08a_radial d hd (p := p') (ε := 0) (δ := D / 2) le_rfl hD2.le (Or.inr hp')
        have e3 : ∫⁻ w, F3 w = ENNReal.ofReal ((D / 2) ^ (-(p + p'))) *
            ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0)) := by
          simp only [hF3]
          rw [lintegral_const_mul _ hIcm]
          congr 1
          exact r26t8a_c08a_radial d hd (p := 0) (ε := 0) (δ := 2 * D) le_rfl (by linarith)
            (Or.inr (by exact_mod_cast hd))
        have e4 : ∫⁻ w, F4 w = ENNReal.ofReal (2 ^ p') * ENNReal.ofReal (r26t8a_c08a_const d *
            ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - (p + p'))) := by
          simp only [hF4]
          rw [lintegral_const_mul _ hIdm]
          congr 1
          exact r26t8a_c08a_radial d hd (p := p + p') (ε := 2 * D) (δ := max (2 * D) R)
            (by linarith) (le_max_left _ _) (Or.inl (by linarith))
        rw [e1, e2, e3, e4]

end HRS.MS.R26T8A
