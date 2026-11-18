import HRS.MS.SpecAux84

/-!
# S8L: the gradient `L²` bound for `|∇e|²` from a differentiated eigen-equation (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_gradL4`: abstract assembly.  Let `μ = ρ dx` be a probability measure with
`∇ρ = -ρ∇W`, `D²W ≥ -κ`, log-Sobolev constant `C` (`s8p_LSI`).  Let `e ∈ C³`, `N = |∇e|²` with `∫ N dμ = ω > 0` and suppose the
differentiated eigen-equation gives `⟨∇e, ∇(L_W e)⟩ ≤ λ N + λ √N hh` pointwise with `hh ≥ 0`, `∫ (hh/√ω)⁴ ≤ H4`.  Then
`∫ N² dμ ≤ (2ω)² exp((2C/3)(2(λ+κ) + λ√2 (3H4/2 + 9/4)))`, i.e. `‖∇e‖_{L⁴(μ)}⁴ ≤ (2ω)² exp(...)`.
Proof: `s = (N+ω)/(2ω)` is a subsolution (`s8p_bochner`), `s8p_en_of_sub` (energy inequality), `s8p_hibp`, `s8p_herbst`.
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V)

theorem s8p_Lw_affine {W f : V → ℝ} (hf : ContDiff ℝ 2 f) (c d : ℝ) (x : V) :
    s8p_Lw b W (fun x => c * f x + d) x = c * s8p_Lw b W f x := by
  have h1 : fderiv ℝ (fun x => c * f x + d) = fun x => c • fderiv ℝ f x := by
    funext y
    rw [fderiv_add_const, fderiv_const_mul ((hf.differentiable (by norm_num)) y)]
  have h2 : fderiv ℝ (fderiv ℝ (fun x => c * f x + d)) = fun x => c • fderiv ℝ (fderiv ℝ f) x := by
    rw [h1]
    funext y
    exact fderiv_const_smul ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y) c
  unfold s8p_Lw s8p_lap
  rw [h2, h1]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  simp only [mul_add, mul_neg, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring


set_option maxHeartbeats 1600000 in
/-- **Gradient L⁴ bound from the differentiated eigen-equation** (assembly of the Bochner inequality, the cut-off
energy inequality, the Gaussian log-Sobolev inequality and the Herbst argument). -/
theorem s8p_gradL4 {ρ W e hh : V → ℝ} {C κ ω lam H4 : ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hρ0 : ∀ x, 0 < ρ x) (hρd : ∀ x, fderiv ℝ ρ x = -(ρ x) • fderiv ℝ W x)
    (hW : ContDiff ℝ 2 W) (hκ0 : 0 ≤ κ) (hκ : ∀ x v, -(κ * ‖v‖ ^ 2) ≤ fderiv ℝ (fderiv ℝ W) x v v)
    (he : ContDiff ℝ 3 e) (hω : 0 < ω) (hlam : 0 ≤ lam)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))]
    (hLSI : s8p_LSI (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) C) (hC : 0 ≤ C)
    (hNint : Integrable (s8p_N b e) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hNone : ∫ x, s8p_N b e x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) = ω)
    (hh0 : ∀ x, 0 ≤ hh x) (hhm : Measurable hh)
    (hh4 : Integrable (fun x => (hh x / Real.sqrt ω) ^ 4) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hH4 : ∫ x, (hh x / Real.sqrt ω) ^ 4 ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ≤ H4)
    (hLe : ∀ x, ∑ i, s8p_g e (b i) x * fderiv ℝ (s8p_Lw b W e) x (b i) ≤
      lam * s8p_N b e x + lam * Real.sqrt (s8p_N b e x) * hh x) :
    Integrable (fun x => s8p_N b e x ^ 2) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ∧
      ∫ x, s8p_N b e x ^ 2 ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ≤
        (2 * ω) ^ 2 * Real.exp ((2 * C / 3) * (2 * (lam + κ) + (lam * Real.sqrt 2) * (3 * H4 / 2 + 9 / 4))) := by
  set μ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ
  have hρm : Measurable ρ := hρ.continuous.measurable
  set N := s8p_N b e with hNdef
  have hNcd : ContDiff ℝ 2 N := s8p_N_contDiff b he
  have hN0 : ∀ x, 0 ≤ N x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  set c : ℝ := 1 / (2 * ω) with hc
  have hc0 : 0 < c := by positivity
  set s : V → ℝ := fun x => c * N x + 1 / 2 with hs
  have hscd : ContDiff ℝ 2 s := (contDiff_const.mul hNcd).add contDiff_const
  have hs_eq : ∀ x, s x = (N x + ω) / (2 * ω) := fun x => by simp only [hs, hc]; field_simp
  have hge : ∀ x, 1 / 2 ≤ s x := fun x => by
    simp only [hs]; nlinarith [mul_nonneg hc0.le (hN0 x)]
  have hsint : Integrable s μ := (hNint.const_mul c).add (integrable_const _)
  have hsone : ∫ x, s x ∂μ = 1 := by
    simp only [hs]
    rw [integral_add (hNint.const_mul c) (integrable_const _), integral_const_mul, hNone]
    simp [hc]; field_simp; ring
  have hLs : ∀ x, s8p_Lw b W s x = c * s8p_Lw b W N x := fun x => s8p_Lw_affine b hNcd c (1 / 2) x
  have hsc : ∀ x, s x = c * (N x + ω) := fun x => by simp only [hs, hc]; field_simp
  have hfd : ∀ x, fderiv ℝ s x = c • fderiv ℝ N x := fun x => by
    simp only [hs]
    rw [fderiv_add_const, fderiv_const_mul ((hNcd.differentiable (by norm_num)) x)]
  set aa : ℝ := 2 * (lam + κ) with haa
  set bb : ℝ := lam * Real.sqrt 2 with hbb
  set h' : V → ℝ := fun x => hh x / Real.sqrt ω with hh'
  have hsub : ∀ x, s8p_Lw b W s x ≤ aa * s x + bb * h' x * Real.sqrt (s x) - ‖fderiv ℝ s x‖ ^ 2 / (2 * s x) := by
    intro x
    rw [hLs]
    have b1 := s8p_bochner b he hW hω hκ x
    have l1 := hLe x
    have hpos : 0 < s x := lt_of_lt_of_le (by norm_num) (hge x)
    have hNω : 0 < N x + ω := by have := hN0 x; linarith
    have e1 : ‖fderiv ℝ s x‖ ^ 2 / (2 * s x) = c * (‖fderiv ℝ N x‖ ^ 2 / (2 * (N x + ω))) := by
      rw [hfd, norm_smul, mul_pow, Real.norm_of_nonneg hc0.le, hsc x]
      field_simp
    have p1 : c * (2 * (lam * N x) + 2 * κ * N x) ≤ aa * s x := by
      have := mul_nonneg (add_nonneg hlam hκ0) (mul_nonneg hc0.le (hN0 x))
      have h2 : aa * s x = 2 * (lam + κ) * (c * N x + 1 / 2) := by simp only [haa, hs]
      rw [h2]
      nlinarith [add_nonneg hlam hκ0]
    have p2 : c * (2 * (lam * Real.sqrt (N x) * hh x)) ≤ bb * h' x * Real.sqrt (s x) := by
      have hsq : Real.sqrt (N x) ≤ Real.sqrt 2 * Real.sqrt ω * Real.sqrt (s x) := by
        rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
        apply Real.sqrt_le_sqrt
        rw [hsc x, hc]; field_simp; linarith [hω]
      have hsw : 0 < Real.sqrt ω := Real.sqrt_pos.2 hω
      have hωs : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω.le
      have h0 := hh0 x
      have eL : c * (2 * (lam * Real.sqrt (N x) * hh x)) =
          (lam * hh x * Real.sqrt (N x)) / (Real.sqrt ω * Real.sqrt ω) := by
        rw [hc, hωs]; field_simp
      have eR : bb * h' x * Real.sqrt (s x) = (lam * hh x * (Real.sqrt 2 * Real.sqrt (s x))) / Real.sqrt ω := by
        simp only [hbb, hh']; field_simp
      rw [eL, eR, div_le_div_iff₀ (mul_pos hsw hsw) hsw]
      have h1 : lam * hh x ≥ 0 := mul_nonneg hlam h0
      have := mul_le_mul_of_nonneg_left hsq h1
      nlinarith [this]
    have b2 : s8p_Lw b W (N) x ≤ 2 * (lam * N x + lam * Real.sqrt (N x) * hh x) + 2 * κ * N x -
        ‖fderiv ℝ N x‖ ^ 2 / (2 * (N x + ω)) := by
      have := b1; simp only [hNdef] at *; linarith
    have := mul_le_mul_of_nonneg_left b2 hc0.le
    rw [e1]
    nlinarith [this, p1, p2]
  have hh'0 : ∀ x, 0 ≤ h' x := fun x => div_nonneg (hh0 x) (Real.sqrt_nonneg _)
  have hh'm : Measurable h' := hhm.div_const _
  have hh'2 : Integrable (fun x => h' x ^ 2) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hh4) ((hh'm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply, hh']
    nlinarith [sq_nonneg ((hh x / Real.sqrt ω) ^ 2 - 1), sq_nonneg (hh x / Real.sqrt ω)]
  have hLsc : Continuous (s8p_Lw b W s) := by
    have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
    unfold s8p_Lw s8p_lap
    refine Continuous.add (Continuous.neg (continuous_finset_sum _ fun j _ => ?_))
      (continuous_finset_sum _ fun j _ => ?_)
    · exact (((hscd.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).clm_apply continuous_const
    · exact ((hW1.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((hscd.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hsub' : S8pSubsol μ s h' (1 / 2) aa bb H4 :=
    { cont := hscd
      s0_pos := by norm_num
      ge := hge
      int := hsint
      one := hsone
      a_nonneg := by simp only [haa]; positivity
      b_nonneg := by simp only [hbb]; positivity
      h_nonneg := hh'0
      h_meas := hh'm
      h4_int := hh4
      h4_le := hH4
      en := fun G hG hB hG0 hGd0 => by
        obtain ⟨B, hB'⟩ := hB
        exact s8p_en_of_sub hρm hρ0 hscd (by norm_num) hge hsint (by simp only [haa]; positivity)
          (by simp only [hbb]; positivity) hh'0 hh'm hh'2 hLsc hsub
          (fun Ψ hΨ hcs => s8p_hibp b hρ hρd (hW.of_le (by norm_num)) hscd hΨ hcs)
          hG hB' hG0 hGd0 }
  obtain ⟨hint2, hval⟩ := s8p_herbst hsub' hLSI hC
  have hNle : ∀ x, N x ^ 2 ≤ (2 * ω) ^ 2 * s x ^ 2 := fun x => by
    have h1 : N x ≤ 2 * ω * s x := by rw [hsc x, hc]; field_simp; linarith [hω]
    have h2 := hN0 x
    nlinarith
  refine ⟨?_, ?_⟩
  · exact Integrable.mono' (hint2.const_mul ((2 * ω) ^ 2)) (hNcd.continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        show ‖N x ^ 2‖ ≤ _
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hNle x)
  · have := integral_mono (Integrable.mono' (hint2.const_mul ((2 * ω) ^ 2)) (hNcd.continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        show ‖N x ^ 2‖ ≤ _
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hNle x))
      (hint2.const_mul ((2 * ω) ^ 2)) hNle
    rw [integral_const_mul] at this
    calc _ ≤ (2 * ω) ^ 2 * ∫ x, s x ^ 2 ∂μ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hval (by positivity)

end HRS.MS.Spec
