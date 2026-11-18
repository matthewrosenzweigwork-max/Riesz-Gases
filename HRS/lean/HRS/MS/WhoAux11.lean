import HRS.MS.WhoAux4
import HRS.MS.UlocCb
import HRS.MS.UlocWeighted

/-!
# S54 part 11: the local Sobolev embedding in `E_{r,P}` (clause (c) of the frozen statement)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MP.RdInit

variable {d : ℕ}

theorem who_jb_ball {x y : Euc d} (hy : y ∈ Metric.ball x 2) : jbracket y ≤ 3 * jbracket x := by
  have hy' : ‖y‖ ≤ ‖x‖ + 2 := by
    have h1 := norm_le_norm_add_norm_sub' y x
    have h2 : ‖y - x‖ < 2 := by simpa [dist_eq_norm] using hy
    linarith
  unfold jbracket
  rw [show (3 : ℝ) * Real.sqrt (1 + ‖x‖ ^ 2) = Real.sqrt (9 * (1 + ‖x‖ ^ 2)) by
    rw [Real.sqrt_mul (by norm_num)]; congr 1; rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [norm_nonneg y, norm_nonneg x, sq_nonneg (‖x‖ - 2)]

/-- the local Sobolev embedding in the weighted spaces -/
theorem who_embed (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r α : ℕ) (hα : (d : ℝ) / 2 + α < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin α → Fin d) (x : Euc d) (f : Euc d → ℝ), ContDiff ℝ ∞ f →
      ENNReal.ofReal |partialDeriv i f x| ≤ ENNReal.ofReal (C * jbracket x ^ P) * weightedSobolevE r P f := by
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨M0, hM0⟩ := HRS.MS.Ul.ul3C_bdd_upto hχ.1 hχ.2.1 r
  set M : ℝ := max M0 0 with hMdef
  have hM : ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M := fun i hi x => (hM0 i hi x).trans (le_max_left _ _)
  obtain ⟨Ce, hCe0, hemb⟩ := HRS.MS.UlocCb.ucb_local_embedding (d := d) α (q := (r : ℝ)) (by linarith)
  set c1 : ℝ := Ce ^ 2 * mriKc d r M * 9 ^ P * (d : ℝ) ^ r with hc1
  have hc10 : 0 ≤ c1 := by
    have := mriKc_nonneg d r M
    positivity
  refine ⟨Real.sqrt c1 + 1, by positivity, fun i x f hf => ?_⟩
  have hM0' : 0 ≤ M := le_max_right _ _
  have hfα : ContDiff ℝ r f := hf.of_le (by exact_mod_cast le_top)
  by_cases hE : weightedSobolevE r P f = ⊤
  · rw [hE, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (by have := who_jb_pos x; positivity)).ne'
  obtain ⟨hmem, hS0, hSle⟩ := mri_cell_bound hχ hM0' r hM hfα x
  set S := HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) (fun y => χ (y - x) * f y) with hS
  obtain ⟨g, hge, hgc, hgb⟩ := hemb _ hmem
  have hvc : Continuous fun y => χ (y - x) * f y :=
    ((hχ.1.continuous.comp (continuous_id.sub continuous_const)).mul hf.continuous)
  have hgv : g = fun y => χ (y - x) * f y := (Continuous.ae_eq_iff_eq volume hgc.continuous hvc).1 hge
  have h1 : |partialDeriv i f x| ≤ Ce * Real.sqrt S := by
    calc |partialDeriv i f x| = |partialDeriv i (fun y => χ (y - x) * f y) x| := by
          rw [HRS.MS.UlocWeighted.uw_pd_eq hχ f i x x (Metric.mem_ball_self one_pos)]
      _ ≤ ‖iteratedFDeriv ℝ α (fun y => χ (y - x) * f y) x‖ := mri_abs_partialDeriv_le i _ x
      _ = ‖iteratedFDeriv ℝ α g x‖ := by rw [hgv]
      _ ≤ Ce * Real.sqrt S := hgb α le_rfl x
  have h2 : |partialDeriv i f x| ^ 2 ≤ Ce ^ 2 * (mriKc d r M * ∫ y in Metric.ball x 2, mriG r f y) := by
    calc |partialDeriv i f x| ^ 2 ≤ (Ce * Real.sqrt S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = Ce ^ 2 * S := by rw [mul_pow, Real.sq_sqrt hS0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
  have hMint : IntegrableOn (mriG r f) (Metric.ball x 2) volume :=
    ((mriG_continuous hfα).continuousOn.integrableOn_compact (isCompact_closedBall x 2)).mono_set
      Metric.ball_subset_closedBall
  have hI : ENNReal.ofReal (∫ y in Metric.ball x 2, mriG r f y) = ∫⁻ y in Metric.ball x 2, ENNReal.ofReal (mriG r f y) :=
    ofReal_integral_eq_lintegral_ofReal hMint (Filter.Eventually.of_forall fun y => mriG_nonneg r f y)
  have hjb := who_jb_pos x
  have hB : ∫⁻ y in Metric.ball x 2, ENNReal.ofReal (mriG r f y) ≤
      ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) * Nsq r P f := by
    have hmj : ∀ j, Measurable fun y : Euc d => ENNReal.ofReal (wt P y * ‖iteratedFDeriv ℝ j f y‖ ^ 2) := fun j =>
      ENNReal.measurable_ofReal.comp (((who_wt_meas P).mul
        (((hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.measurable).pow_const 2)))
    calc ∫⁻ y in Metric.ball x 2, ENNReal.ofReal (mriG r f y)
        ≤ ∫⁻ y in Metric.ball x 2, ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) *
            ∑ j ∈ Finset.range (r + 1), ENNReal.ofReal (wt P y * ‖iteratedFDeriv ℝ j f y‖ ^ 2) := by
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy => ?_
          have hwy : 1 ≤ (3 * jbracket x) ^ (2 * P) * wt P y := by
            have h1 := Real.rpow_le_rpow (who_jb_pos y).le (who_jb_ball hy) (by linarith : (0 : ℝ) ≤ 2 * P)
            unfold wt
            calc (1 : ℝ) = (3 * jbracket x) ^ (2 * P) * ((3 * jbracket x) ^ (2 * P))⁻¹ := by
                  rw [mul_inv_cancel₀]; exact (Real.rpow_pos_of_pos (by positivity) _).ne'
              _ ≤ (3 * jbracket x) ^ (2 * P) * (jbracket y ^ (2 * P))⁻¹ := by
                  gcongr
                  exact Real.rpow_pos_of_pos (who_jb_pos y) _
              _ = _ := by rw [neg_mul, Real.rpow_neg (who_jb_pos y).le]
          unfold mriG
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _), Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg ‖iteratedFDeriv ℝ j f y‖]
      _ ≤ ∫⁻ y, ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) *
            ∑ j ∈ Finset.range (r + 1), ENNReal.ofReal (wt P y * ‖iteratedFDeriv ℝ j f y‖ ^ 2) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) * Nsq r P f := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun j _ => hmj j)]
          rfl
  have hC : ENNReal.ofReal (|partialDeriv i f x| ^ 2) ≤ ENNReal.ofReal (c1 * jbracket x ^ (2 * P)) * Esq r P f := by
    calc ENNReal.ofReal (|partialDeriv i f x| ^ 2)
        ≤ ENNReal.ofReal (Ce ^ 2 * mriKc d r M * ∫ y in Metric.ball x 2, mriG r f y) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [h2])
      _ = ENNReal.ofReal (Ce ^ 2 * mriKc d r M) * ∫⁻ y in Metric.ball x 2, ENNReal.ofReal (mriG r f y) := by
          rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (mriKc_nonneg d r M)), hI]
      _ ≤ ENNReal.ofReal (Ce ^ 2 * mriKc d r M) * (ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) * Nsq r P f) :=
          mul_le_mul' le_rfl hB
      _ ≤ ENNReal.ofReal (Ce ^ 2 * mriKc d r M) * (ENNReal.ofReal ((3 * jbracket x) ^ (2 * P)) *
            (((d : ℝ≥0∞) ^ r) * Esq r P f)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl (who_Nsq_le hd hfα))
      _ = ENNReal.ofReal (c1 * jbracket x ^ (2 * P)) * Esq r P f := by
          have e1 : (3 * jbracket x) ^ (2 * P) = 9 ^ P * jbracket x ^ (2 * P) := by
            rw [Real.mul_rpow (by norm_num) hjb.le]
            congr 1
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
          have e2 : ENNReal.ofReal (c1 * jbracket x ^ (2 * P)) = ENNReal.ofReal (Ce ^ 2 * mriKc d r M) *
              (ENNReal.ofReal (9 ^ P * jbracket x ^ (2 * P)) * (d : ℝ≥0∞) ^ r) := by
            rw [hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by have := mriKc_nonneg d r M; positivity)]
            congr 1; ring
          rw [e1, e2]; ring
  rw [who_E_eq]
  have hA : ENNReal.ofReal |partialDeriv i f x| = (ENNReal.ofReal (|partialDeriv i f x| ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs : (c1 * jbracket x ^ (2 * P)) ^ (1 / 2 : ℝ) = Real.sqrt c1 * jbracket x ^ P := by
    rw [Real.mul_rpow hc10 (Real.rpow_nonneg hjb.le _), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hjb.le]
    congr 2; ring
  calc ENNReal.ofReal |partialDeriv i f x|
      = (ENNReal.ofReal (|partialDeriv i f x| ^ 2)) ^ (1 / 2 : ℝ) := hA
    _ ≤ (ENNReal.ofReal (c1 * jbracket x ^ (2 * P)) * Esq r P f) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hC (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt c1 * jbracket x ^ P) * (Esq r P f) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg hc10 (Real.rpow_nonneg hjb.le _)) (by norm_num), hs]
    _ ≤ ENNReal.ofReal ((Real.sqrt c1 + 1) * jbracket x ^ P) * (Esq r P f) ^ (1 / 2 : ℝ) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have := Real.rpow_nonneg hjb.le P
        nlinarith

end HRS.MS.Who
