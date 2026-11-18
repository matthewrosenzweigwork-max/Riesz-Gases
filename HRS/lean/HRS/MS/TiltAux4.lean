import HRS.MS.TiltAux3

/-!
# S4.7 packet P4: the Gibbs integration by parts for `Q = canonicalGibbs g V₀ N γ`

`W = V₀ - (q/γ)|x|²/2 = -γ⁻¹(log ρ + q|x|²/2) - g * μ` is `C^∞` with `∇W = -γ⁻¹ Bd - ∇U` bounded, and
`exp(-γ H_{V₀}) = exp(-γ H_{a'}) exp(-γ ∑ W(x_i))`, `a' = q/γ`.  `s47_gibbs_ibp`: S4.5 `s45_gibbs_ibp` (confinement `a'`,
temperature `γ`) for the compactly supported tests `F e^{-γ ∑ W} Θ_R` and `R → ∞` (copy of `s46_gibbs_ibp`, whose
`s46_G`, `s46_Theta`, `s46_J_bound` are generic in the potential and are reused).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S46
open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- `W = V₀ - (q/γ)|x|²/2`. -/
def s47_W (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (q γ : ℝ) : Euc d → ℝ := fun x =>
  s47_V0 d s ρ γ x - confinement (q / γ) x

theorem s47_V0_eq (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (q γ : ℝ) (x : Euc d) :
    s47_V0 d s ρ γ x = confinement (q / γ) x + s47_W d s ρ q γ x := by
  unfold s47_W; ring

/-- `∇ log ρ = -q x + Bd`. -/
theorem s47_gradient_log {s : ℝ} {ρ : Euc d → ℝ} {q C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) (x : Euc d) :
    gradient (fun y => Real.log (ρ y)) x = -q • x + Bd x := by
  have hρd : DifferentiableAt ℝ ρ x := (hT.smooth.differentiable (by simp)) x
  have hne : ρ x ≠ 0 := (hT.pos x).ne'
  refine ext_inner_left ℝ fun v => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, (hρd.hasFDerivAt.log hne).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← HRS.MS.PoisKolm.kl_inner_gradient ρ x v, hT.grad_rho x, inner_smul_right]
  field_simp

theorem s47_W_smooth {s : ℝ} {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) : ContDiff ℝ ∞ (s47_W d s ρ q γ) := by
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (ρ y)) := hT.smooth.log (fun x => (hT.pos x).ne')
  have hconf : ContDiff ℝ ∞ (confinement (q / γ) : Euc d → ℝ) := by
    unfold confinement
    exact (contDiff_const.mul ((contDiff_norm_sq ℝ).of_le (by exact_mod_cast le_top))).div_const _
  have : s47_W d s ρ q γ = fun x => -γ⁻¹ * Real.log (ρ x) -
      convMeasure (rieszKernel d s) (withDensityReal ρ) x - confinement (q / γ) x := rfl
  rw [this]
  exact ((contDiff_const.mul hlog).sub hT.Usmooth).sub hconf

/-- `∇W = -γ⁻¹ Bd - ∇U`. -/
theorem s47_gradient_W {s : ℝ} {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) (hγ : 0 < γ) (x : Euc d) :
    gradient (s47_W d s ρ q γ) x = -γ⁻¹ • Bd x -
      gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x := by
  have hlogd : DifferentiableAt ℝ (fun y => Real.log (ρ y)) x :=
    ((hT.smooth.log (fun x => (hT.pos x).ne')).differentiable (by simp)) x
  have hUd : DifferentiableAt ℝ (convMeasure (rieszKernel d s) (withDensityReal ρ)) x :=
    (hT.Usmooth.differentiable (by simp)) x
  have hconf : HasFDerivAt (confinement (q / γ) : Euc d → ℝ) ((q / γ) • innerSL ℝ x) x :=
    HRS.MS.Tc1.tc1_hasFDeriv_conf (q / γ) x
  have hW : HasFDerivAt (s47_W d s ρ q γ)
      ((-γ⁻¹) • fderiv ℝ (fun y => Real.log (ρ y)) x - fderiv ℝ (convMeasure (rieszKernel d s)
        (withDensityReal ρ)) x - (q / γ) • innerSL ℝ x) x := by
    have h1 := ((hlogd.hasFDerivAt).const_mul (-γ⁻¹)).sub hUd.hasFDerivAt
    exact h1.sub hconf
  refine ext_inner_left ℝ fun v => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, hW.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [← HRS.MS.PoisKolm.kl_inner_gradient (fun y => Real.log (ρ y)) x v,
    ← HRS.MS.PoisKolm.kl_inner_gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x v,
    s47_gradient_log hT x]
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right, inner_neg_right]
  rw [real_inner_comm v x]
  have : γ ≠ 0 := hγ.ne'
  field_simp
  ring

theorem s47_W_grad_bound {s : ℝ} {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) (hγ : 0 < γ) (y : Euc d) :
    ‖fderiv ℝ (s47_W d s ρ q γ) y‖ ≤ γ⁻¹ * BB + BU := by
  rw [← S45.s45_norm_gradient, s47_gradient_W hT hγ y]
  calc ‖-γ⁻¹ • Bd y - gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y‖
      ≤ ‖-γ⁻¹ • Bd y‖ + ‖gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y‖ := norm_sub_le _ _
    _ ≤ γ⁻¹ * BB + BU := by
        refine add_le_add ?_ (hT.gradU_le y)
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hγ)]
        exact mul_le_mul_of_nonneg_left (hT.Bd_le y) (inv_nonneg.2 hγ.le)

/-- `γ ∇W = -(Bd + γ ∇U)`. -/
theorem s47_gamma_gradient_W {s : ℝ} {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) (hγ : 0 < γ) (y w : Euc d) :
    γ * ⟪gradient (s47_W d s ρ q γ) y, w⟫ =
      -(⟪Bd y, w⟫ + γ * ⟪gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y, w⟫) := by
  rw [s47_gradient_W hT hγ y]
  simp only [inner_sub_left, real_inner_smul_left, inner_neg_left]
  have : γ ≠ 0 := hγ.ne'
  field_simp
  ring

theorem s47_weight_factor {s : ℝ} {ρ : Euc d → ℝ} {q γ : ℝ} (hγ : 0 < γ) (X : EucConfig d N) :
    Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s47_V0 d s ρ γ) X) =
      Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement (q / γ)) X) *
        Real.exp (-γ * ∑ i, s47_W d s ρ q γ (X i)) := by
  rw [← Real.exp_add]
  congr 1
  have h3 : canonicalHamiltonian (rieszKernel d s) (s47_V0 d s ρ γ) X =
      canonicalHamiltonian (rieszKernel d s) (confinement (q / γ)) X + ∑ i, s47_W d s ρ q γ (X i) := by
    unfold canonicalHamiltonian
    simp_rw [s47_V0_eq d s ρ q γ, Finset.sum_add_distrib]
    ring
  rw [h3]
  ring

theorem s47_gibbs_ibp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ}
    {Bd : Euc d → Euc d} (hq : 0 < q) (hγ : 0 < γ) (hT : TRef d s ρ q C c BU BB Bd) (hN : 1 ≤ N)
    {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv)
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ} (hF : ContDiff ℝ 1 F) {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, (((∑ k, S45.s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
      F X * (∑ i, (q * ⟪X i, v (X i)⟫ - (⟪Bd (X i), v (X i)⟫ +
          γ * ⟪gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) (X i), v (X i)⟫)) +
        γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫))) *
      Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s47_V0 d s ρ γ) X) = 0 := by
  set U := s47_W d s ρ q γ with hUdef
  set a' : ℝ := q / γ with ha'def
  have ha' : 0 < a' := div_pos hq hγ
  have hU : ContDiff ℝ ∞ U := s47_W_smooth hT
  set BW : ℝ := γ⁻¹ * BB + BU with hBWdef
  have hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BW := fun y => s47_W_grad_bound hT hγ y
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  obtain ⟨K, hK0, hK⟩ := s46_J_bound hd hs0 ha' hγ hN (c := γ) hU hUb hv hBv hDv hF hBF hDF
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hcol : ∀ᵐ X : EucConfig d N ∂volume, ∀ i j, i ≠ j → X i ≠ X j := by
    have h0 := HRS.MP.SelfSimP4Impl.p4g_collision_null hd N
    have := (measure_eq_zero_iff_ae_notMem.1 h0)
    filter_upwards [this] with X hX i j hij hXij
    exact hX ⟨i, j, hij, hXij⟩
  -- the sequence
  set f : ℕ → EucConfig d N → ℝ := fun n X =>
    s46_J d s a' γ v (fun Y => s46_G γ U F Y * s46_Theta ((n : ℝ) + 1) Y) X with hfdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hGcd : ∀ n : ℕ, ContDiff ℝ 1 (fun Y => s46_G γ U F Y * s46_Theta ((n : ℝ) + 1) Y) := fun n =>
    (s46_G_contDiff hU hF).mul ((s46_Theta_contDiff (R := (n : ℝ) + 1)).of_le (by simp))
  have hGcs : ∀ n : ℕ, HasCompactSupport (fun Y : EucConfig d N =>
      s46_G γ U F Y * s46_Theta ((n : ℝ) + 1) Y) := fun n =>
    (s46_Theta_compact (hRpos n)).mul_left
  -- each term vanishes
  have hfn : ∀ n : ℕ, ∫ X, f n X = 0 := by
    intro n
    obtain ⟨BG, hBG⟩ := (hGcd n).continuous.bounded_above_of_compact_support (hGcs n)
    obtain ⟨DG, hDG⟩ := ((hGcd n).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hGcs n).fderiv (𝕜 := ℝ))
    have := S45.s45_gibbs_ibp (s := s) hd hs0 ha' hγ hN hv hBv hDv (hGcd n) (BF := BG) (DF := DG)
      (fun X => by simpa [Real.norm_eq_abs] using hBG X) hDG
    exact this
  -- pointwise limit
  have hlim : ∀ X : EucConfig d N, Tendsto (fun n => f n X) atTop (𝓝 (s46_J d s a' γ v (s46_G γ U F) X)) := by
    intro X
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨⌈s46_S X⌉₊, fun n hn => ?_⟩
    have hSn : s46_S X < ((n : ℝ) + 1) ^ 2 := by
      have h1 : s46_S X ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      linarith
    have hev : (fun Y : EucConfig d N => s46_G γ U F Y * s46_Theta ((n : ℝ) + 1) Y) =ᶠ[𝓝 X]
        s46_G γ U F := by
      have hc : ContinuousAt (s46_S : EucConfig d N → ℝ) X := s46_S_contDiff.continuous.continuousAt
      filter_upwards [hc.eventually_lt continuousAt_const hSn] with Y hY
      rw [s46_Theta_one (hRpos n) hY.le, mul_one]
    show s46_J d s a' γ v (s46_G γ U F) X = s46_J d s a' γ v (fun Y => s46_G γ U F Y *
      s46_Theta ((n : ℝ) + 1) Y) X
    unfold s46_J
    beta_reduce
    rw [hev.fderiv_eq, hev.eq_of_nhds]
  -- domination
  set L : ℝ := N * |γ| * BW with hL
  set K' : ℝ := K * Real.exp (N * |γ| * |U 0|) with hK'
  have hdomeq : ∀ X : EucConfig d N, K * (1 + ‖X‖) * Real.exp (N * |γ| * (|U 0| + BW * ‖X‖)) *
      Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) =
      K' * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) := by
    intro X
    have : Real.exp (N * |γ| * (|U 0| + BW * ‖X‖)) = Real.exp (N * |γ| * |U 0|) * Real.exp (L * ‖X‖) := by
      rw [← Real.exp_add]; congr 1; rw [hL]; ring
    rw [this, hK']; ring
  have hint : Integrable (fun X : EucConfig d N =>
      K' * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2))) :=
    s46_dom_integrable (by positivity) L K' (by positivity)
  -- measurability
  have hgm : Measurable (rieszKernel d s : Euc d → ℝ) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hVm : Measurable (confinement a' : Euc d → ℝ) := by unfold confinement; fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (f n) volume := by
    intro n
    have hG := hGcd n
    have h1 : Measurable fun X : EucConfig d N => ∑ k, S45.s45_div v (X k) :=
      Finset.measurable_sum _ fun k _ => (S45.s45_continuous_div hv).measurable.comp (measurable_pi_apply k)
    have h2 : Measurable fun X : EucConfig d N =>
        fderiv ℝ (fun Y => s46_G γ U F Y * s46_Theta ((n : ℝ) + 1) Y) X (fun k => v (X k)) :=
      ((hG.continuous_fderiv one_ne_zero).clm_apply
        (continuous_pi fun k => hv.continuous.comp (continuous_apply k))).measurable
    have h3 : Measurable fun X : EucConfig d N =>
        ∑ i, a' * ⟪X i, v (X i)⟫ :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul
        (((measurable_pi_apply i).inner (hv.continuous.measurable.comp (measurable_pi_apply i))))
    have hgr := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s
    have h4 : Measurable fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫ :=
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        (hgr.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).inner
          ((hv.continuous.measurable.comp (measurable_pi_apply i)).sub
            (hv.continuous.measurable.comp (measurable_pi_apply j)))
    have hw : Measurable fun X : EucConfig d N =>
        Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement a') X) :=
      Real.measurable_exp.comp (measurable_const.mul (S45.s45_measurable_ham hgm hVm))
    have hGm : Measurable fun X : EucConfig d N => s46_G γ U F X * s46_Theta ((n : ℝ) + 1) X :=
      hG.continuous.measurable
    show AEStronglyMeasurable (fun X => s46_J d s a' γ v (fun Y => s46_G γ U F Y *
      s46_Theta ((n : ℝ) + 1) Y) X) volume
    unfold s46_J
    exact (((h1.mul hGm).add h2).sub (measurable_const.mul (hGm.mul (h3.add (measurable_const.mul h4))))).mul
      hw |>.aestronglyMeasurable
  have hdom : ∀ n : ℕ, ∀ᵐ X ∂(volume : Measure (EucConfig d N)), ‖f n X‖ ≤
      K' * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) := by
    intro n
    filter_upwards [hcol] with X hX
    rw [Real.norm_eq_abs, ← hdomeq]
    exact hK _ (hR1 n) X hX
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun X : EucConfig d N => K' * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)))
    hmeas hint hdom (Filter.Eventually.of_forall hlim)
  have hzero : ∫ X, s46_J d s a' γ v (s46_G γ U F) X = 0 :=
    tendsto_nhds_unique hDCT (tendsto_const_nhds.congr (fun n => (hfn n).symm))
  rw [← hzero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  -- pointwise identity between the tilted and the Q-form integrands
  show _ = s46_J d s a' γ v (s46_G γ U F) X
  unfold s46_J
  beta_reduce
  rw [s47_weight_factor (s := s) (ρ := ρ) (q := q) hγ X, s46_fderiv_G_apply hU hFd]
  have hinner : ∀ y w : Euc d, fderiv ℝ U y w = ⟪gradient U y, w⟫ := fun y w => S45.s45_fderiv_eq_inner U y w
  simp_rw [hinner]
  have hsum : ∑ i, (q * ⟪X i, v (X i)⟫ - (⟪Bd (X i), v (X i)⟫ +
        γ * ⟪gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) (X i), v (X i)⟫)) =
      γ * ∑ i, a' * ⟪X i, v (X i)⟫ + γ * ∑ i, ⟪gradient U (X i), v (X i)⟫ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := s47_gamma_gradient_W hT hγ (X i) (v (X i))
    rw [h, ha'def]
    have : γ ≠ 0 := hγ.ne'
    field_simp
    ring
  rw [hsum]
  unfold s46_G
  ring


end S47

end
