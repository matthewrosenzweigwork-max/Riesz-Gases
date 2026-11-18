import HRS.MS.WhoAux11
import HRS.MS.R2InterpAux11

/-!
# S10.2 (worker S102), part 12: the local Sobolev embedding for `C^r` functions (Dirac masses are bounded on `E_{r,P}`)

Copy of `HRS.MS.Who.who_embed` (S5.4 clause (c)) with `ContDiff ℝ ∞ f` weakened to `ContDiff ℝ r f` (only `C^r` is used in the proof).
Consequence: `|f(x)| ≤ C ⟨x⟩^P ‖f‖_{E_{r,P}}` for every `C^r` function of finite weighted norm, i.e. point evaluations (and empirical measures)
are norm-continuous on the tests of `IsR2WeightedTest`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MP.RdInit HRS.MS.Who

variable {d : ℕ}

/-- the local Sobolev embedding in the weighted spaces -/
theorem s102_embed_Cr (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r α : ℕ) (hα : (d : ℝ) / 2 + α < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin α → Fin d) (x : Euc d) (f : Euc d → ℝ), ContDiff ℝ r f →
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
  have hfα : ContDiff ℝ r f := hf
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
    have hmj : ∀ j, j ≤ r → Measurable fun y : Euc d => ENNReal.ofReal (wt P y * ‖iteratedFDeriv ℝ j f y‖ ^ 2) := fun j hj =>
      ENNReal.measurable_ofReal.comp (((who_wt_meas P).mul
        (((hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).norm.measurable).pow_const 2)))
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
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun j hj => hmj j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))]
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


/-- Point evaluations are bounded on `E_{r,P}` for `C^r` functions (`d/2 < r`). -/
theorem s102_eval_bound (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r : ℕ) (hr : (d : ℝ) / 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Euc d) (f : Euc d → ℝ), ContDiff ℝ r f → weightedSobolevE r P f < ⊤ →
      |f x| ≤ C * jbracket x ^ P * (weightedSobolevE r P f).toReal := by
  obtain ⟨C, hC, h⟩ := s102_embed_Cr hd hP0 r 0 (by simpa using hr)
  refine ⟨C, hC, fun x f hf hE => ?_⟩
  have h1 := h (fun l => (⟨0, hd⟩ : Fin d)) x f hf
  have h2 : partialDeriv (fun l : Fin 0 => (⟨0, hd⟩ : Fin d)) f x = f x := by
    simp [partialDeriv]
  rw [h2] at h1
  have hjb : 0 ≤ C * jbracket x ^ P := mul_nonneg hC.le (Real.rpow_nonneg (who_jb_pos x).le P)
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne) h1
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hjb] at h3
  simpa [mul_assoc] using h3

/-- `ν ↦ (f ↦ ∫ f dν)` is admissible when `⟨x⟩^P` is `ν`-integrable. -/
theorem s102_Z_pair (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r : ℕ) (hr : (d : ℝ) / 2 < r)
    (ν : Measure (Euc d)) (hν : Integrable (fun x => jbracket x ^ P) ν) :
    S102Z r P (fun f => ∫ x, f x ∂ν) := by
  obtain ⟨C, hC, hb⟩ := s102_eval_bound hd hP0 r hr
  have hint : ∀ f, IsR2WeightedTest r P f → Integrable f ν := by
    intro f hf
    refine Integrable.mono' (hν.const_mul (C * (weightedSobolevE r P f).toReal))
      hf.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |f x| ≤ C * jbracket x ^ P * (weightedSobolevE r P f).toReal := hb x f hf.1 hf.2
      _ = C * (weightedSobolevE r P f).toReal * jbracket x ^ P := by ring
  refine ⟨fun f g hf hg => integral_add (hint f hf) (hint g hg), fun c f hf => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c f
  · refine ⟨C * ∫ x, jbracket x ^ P ∂ν, fun f hf => ?_⟩
    calc |∫ x, f x ∂ν| = ‖∫ x, f x ∂ν‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C * (weightedSobolevE r P f).toReal * jbracket x ^ P ∂ν := by
          refine norm_integral_le_of_norm_le (hν.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs]
          calc |f x| ≤ C * jbracket x ^ P * (weightedSobolevE r P f).toReal := hb x f hf.1 hf.2
            _ = C * (weightedSobolevE r P f).toReal * jbracket x ^ P := by ring
      _ = C * (∫ x, jbracket x ^ P ∂ν) * (weightedSobolevE r P f).toReal := by
          rw [integral_const_mul]; ring

theorem s102_Z_sub {r : ℕ} {P : ℝ} {z₁ z₂ : (Euc d → ℝ) → ℝ} (h₁ : S102Z r P z₁) (h₂ : S102Z r P z₂) :
    S102Z r P (fun f => z₁ f - z₂ f) := by
  obtain ⟨M₁, hM₁⟩ := h₁.bdd
  obtain ⟨M₂, hM₂⟩ := h₂.bdd
  refine ⟨fun f g hf hg => by rw [h₁.add f g hf hg, h₂.add f g hf hg]; ring,
    fun c f hf => by rw [h₁.smul c f hf, h₂.smul c f hf]; ring, ⟨|M₁| + |M₂|, fun f hf => ?_⟩⟩
  have := ENNReal.toReal_nonneg (a := weightedSobolevE r P f)
  calc |z₁ f - z₂ f| ≤ |z₁ f| + |z₂ f| := abs_sub _ _
    _ ≤ M₁ * (weightedSobolevE r P f).toReal + M₂ * (weightedSobolevE r P f).toReal := add_le_add (hM₁ f hf) (hM₂ f hf)
    _ ≤ (|M₁| + |M₂|) * (weightedSobolevE r P f).toReal := by
        nlinarith [le_abs_self M₁, le_abs_self M₂]

theorem s102_Z_smul {r : ℕ} {P : ℝ} {z : (Euc d → ℝ) → ℝ} (h : S102Z r P z) (a : ℝ) :
    S102Z r P (fun f => a * z f) := by
  obtain ⟨M, hM⟩ := h.bdd
  refine ⟨fun f g hf hg => by rw [h.add f g hf hg]; ring, fun c f hf => by rw [h.smul c f hf]; ring,
    ⟨|a| * |M|, fun f hf => ?_⟩⟩
  have := ENNReal.toReal_nonneg (a := weightedSobolevE r P f)
  calc |a * z f| = |a| * |z f| := abs_mul _ _
    _ ≤ |a| * (M * (weightedSobolevE r P f).toReal) := mul_le_mul_of_nonneg_left (hM f hf) (abs_nonneg _)
    _ ≤ |a| * (|M| * (weightedSobolevE r P f).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self M) this) (abs_nonneg _)
    _ = |a| * |M| * (weightedSobolevE r P f).toReal := by ring

theorem s102_integrable_empirical {N : ℕ} (hN : 0 < N) (X : EucConfig d N) (g : Euc d → ℝ) :
    Integrable g (HRS.Whole.empirical X) := by
  unfold HRS.Whole.empirical
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by exact_mod_cast hN.ne'))
  refine integrable_finsetSum_measure.2 fun i _ => ?_
  exact integrable_dirac (by simp)

/-- The empirical fluctuation field `√N(μ_N - μ)` (any centring measure `ν` with a finite `⟨x⟩^P`-moment) is admissible. -/
theorem s102_Z_fluct (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r : ℕ) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N)
    (X : EucConfig d N) (ν : Measure (Euc d)) (hν : Integrable (fun x => jbracket x ^ P) ν) (a : ℝ) :
    S102Z r P (fun f => a * (HRS.Whole.pair (HRS.Whole.empirical X) f - HRS.Whole.pair ν f)) :=
  s102_Z_smul (s102_Z_sub (s102_Z_pair hd hP0 r hr _ (s102_integrable_empirical hN X _))
    (s102_Z_pair hd hP0 r hr ν hν)) a

end HRS.MS.R2Interp

end
