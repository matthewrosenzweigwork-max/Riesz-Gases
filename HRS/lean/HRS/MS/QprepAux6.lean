import HRS.MS.QprepAux5

/-!
# S4.6 packet A6: the Gibbs integration by parts for `Q_{N,γ₀} = canonicalGibbs g V_Q N γ₀`

`s46_gibbs_ibp`: for a `C¹` vector field `v` with bounded `v, Dv` and a `C¹` functional `F` with bounded `F, dF`,
`∫ [ (∑ div v(x_k)) F + dF(v) - F (∑_i (β a ⟨x_i,v⟩ + (β-γ) ⟨∇U(x_i), v⟩) + (γ/N) ∑_{i<j} ⟨∇g, v_i-v_j⟩) ] e^{-γ H_{V_Q}} dX = 0`.
Proof: `s45_gibbs_ibp` (confinement `a' = βa/γ`, temperature `γ`) for `G̃_R = F e^{-cU} Θ_R` and `R → ∞` (dominated convergence, majorant
`s46_J_bound`; `G̃_R = G` near each `X` for `R² > S(X)`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

theorem s46_weight_factor {s a β γ : ℝ} (hγ : 0 < γ) (X : EucConfig d N) :
    Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s46_VQ d s a β γ) X) =
      Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (confinement (β * a / γ)) X) *
        Real.exp (-(β - γ) * ∑ i, convMeasure (rieszKernel d s) (thermalMeasure d s a β) (X i)) := by
  rw [← Real.exp_add]
  congr 1
  have h2 : ∀ x : Euc d, s46_VQ d s a β γ x = confinement (β * a / γ) x +
      (β / γ - 1) * convMeasure (rieszKernel d s) (thermalMeasure d s a β) x := by
    intro x; unfold s46_VQ confinement; ring
  have h3 : canonicalHamiltonian (rieszKernel d s) (s46_VQ d s a β γ) X =
      canonicalHamiltonian (rieszKernel d s) (confinement (β * a / γ)) X +
        (β / γ - 1) * ∑ i, convMeasure (rieszKernel d s) (thermalMeasure d s a β) (X i) := by
    unfold canonicalHamiltonian
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [h3]
  field_simp
  ring

theorem s46_gibbs_ibp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {a β γ Ct ct BU : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) (hT : S45.ThermalData d s a β Ct ct BU) (hN : 1 ≤ N)
    {v : Euc d → Euc d} (hv : ContDiff ℝ 1 v) {Bv Dv : ℝ} (hBv : ∀ x, ‖v x‖ ≤ Bv)
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ} (hF : ContDiff ℝ 1 F) {BF DF : ℝ}
    (hBF : ∀ X, |F X| ≤ BF) (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, (((∑ k, S45.s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
      F X * (∑ i, (β * a * ⟪X i, v (X i)⟫ +
          (β - γ) * ⟪gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) (X i),
            v (X i)⟫) +
        γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫))) *
      Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s46_VQ d s a β γ) X) = 0 := by
  set U := convMeasure (rieszKernel d s) (thermalMeasure d s a β) with hUdef
  set a' : ℝ := β * a / γ with ha'def
  have ha' : 0 < a' := by positivity
  set c : ℝ := β - γ with hcdef
  have hU : ContDiff ℝ ∞ U := hT.Usmooth
  have hUb : ∀ y, ‖fderiv ℝ U y‖ ≤ BU := fun y => by
    rw [← S45.s45_norm_gradient]; exact hT.gradU_le y
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  obtain ⟨K, hK0, hK⟩ := s46_J_bound hd hs0 ha' hγ hN (c := c) hU hUb hv hBv hDv hF hBF hDF
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hcol : ∀ᵐ X : EucConfig d N ∂volume, ∀ i j, i ≠ j → X i ≠ X j := by
    have h0 := HRS.MP.SelfSimP4Impl.p4g_collision_null hd N
    have := (measure_eq_zero_iff_ae_notMem.1 h0)
    filter_upwards [this] with X hX i j hij hXij
    exact hX ⟨i, j, hij, hXij⟩
  -- the sequence
  set f : ℕ → EucConfig d N → ℝ := fun n X =>
    s46_J d s a' γ v (fun Y => s46_G c U F Y * s46_Theta ((n : ℝ) + 1) Y) X with hfdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hGcd : ∀ n : ℕ, ContDiff ℝ 1 (fun Y => s46_G c U F Y * s46_Theta ((n : ℝ) + 1) Y) := fun n =>
    (s46_G_contDiff hU hF).mul ((s46_Theta_contDiff (R := (n : ℝ) + 1)).of_le (by simp))
  have hGcs : ∀ n : ℕ, HasCompactSupport (fun Y : EucConfig d N =>
      s46_G c U F Y * s46_Theta ((n : ℝ) + 1) Y) := fun n =>
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
  have hlim : ∀ X : EucConfig d N, Tendsto (fun n => f n X) atTop (𝓝 (s46_J d s a' γ v (s46_G c U F) X)) := by
    intro X
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨⌈s46_S X⌉₊, fun n hn => ?_⟩
    have hSn : s46_S X < ((n : ℝ) + 1) ^ 2 := by
      have h1 : s46_S X ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      linarith
    have hev : (fun Y : EucConfig d N => s46_G c U F Y * s46_Theta ((n : ℝ) + 1) Y) =ᶠ[𝓝 X]
        s46_G c U F := by
      have hc : ContinuousAt (s46_S : EucConfig d N → ℝ) X := s46_S_contDiff.continuous.continuousAt
      filter_upwards [hc.eventually_lt continuousAt_const hSn] with Y hY
      rw [s46_Theta_one (hRpos n) hY.le, mul_one]
    show s46_J d s a' γ v (s46_G c U F) X = s46_J d s a' γ v (fun Y => s46_G c U F Y *
      s46_Theta ((n : ℝ) + 1) Y) X
    unfold s46_J
    beta_reduce
    rw [hev.fderiv_eq, hev.eq_of_nhds]
  -- domination
  set L : ℝ := N * |c| * BU with hL
  set K' : ℝ := K * Real.exp (N * |c| * |U 0|) with hK'
  have hdomeq : ∀ X : EucConfig d N, K * (1 + ‖X‖) * Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) *
      Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) =
      K' * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-((γ * a' / 4) * ‖X‖ ^ 2)) := by
    intro X
    have : Real.exp (N * |c| * (|U 0| + BU * ‖X‖)) = Real.exp (N * |c| * |U 0|) * Real.exp (L * ‖X‖) := by
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
        fderiv ℝ (fun Y => s46_G c U F Y * s46_Theta ((n : ℝ) + 1) Y) X (fun k => v (X k)) :=
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
    have hGm : Measurable fun X : EucConfig d N => s46_G c U F X * s46_Theta ((n : ℝ) + 1) X :=
      hG.continuous.measurable
    show AEStronglyMeasurable (fun X => s46_J d s a' γ v (fun Y => s46_G c U F Y *
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
  have hzero : ∫ X, s46_J d s a' γ v (s46_G c U F) X = 0 :=
    tendsto_nhds_unique hDCT (tendsto_const_nhds.congr (fun n => (hfn n).symm))
  rw [← hzero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  -- pointwise identity between the tilted and the Q-form integrands
  show _ = s46_J d s a' γ v (s46_G c U F) X
  unfold s46_J
  beta_reduce
  rw [s46_weight_factor (s := s) (a := a) (β := β) hγ X, s46_fderiv_G_apply hU hFd]
  have hinner : ∀ y w : Euc d, fderiv ℝ U y w = ⟪gradient U y, w⟫ := fun y w => S45.s45_fderiv_eq_inner U y w
  simp_rw [hinner]
  have hsum : ∑ i, (β * a * ⟪X i, v (X i)⟫ + (β - γ) * ⟪gradient U (X i), v (X i)⟫) =
      γ * ∑ i, a' * ⟪X i, v (X i)⟫ + (β - γ) * ∑ i, ⟪gradient U (X i), v (X i)⟫ := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha'def]; field_simp
  rw [hsum]
  unfold s46_G
  ring

end S46

end
