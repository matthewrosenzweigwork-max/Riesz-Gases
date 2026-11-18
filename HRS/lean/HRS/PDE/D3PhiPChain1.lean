import HRS.PDE.D3PhiPFinal
import HRS.PDE.TorusFPLpGlue5
import HRS.PDE.MovEFinal

/-!
# D3PHIP chain, part 1: `d3phi_lp_bound` from the PROVED packets A, C1 and `movT_lp_lsc_proof`

Verbatim copies of the proof terms of `TorusFPLpGlue4.d3phi_lp_classical_bound` and `TorusFPLpGlue5.d3phi_lp_bound_proof`,
with the sorried packets replaced by `d3phi_identity_classical_proof`, `d3phi_approx_Lp_proof`, `movT_lp_lsc_proof`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS
variable {n : ℕ}

theorem d3pp_lp_classical_bound (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ x, ENNReal.ofReal (Real.exp (c * |d3phi_src κ U ψ ψt r x| / L r))
      ∂(d3phi_q κ U ψ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p : ℝ → ℝ} (hp : D3phiPath c L p T) :
    ∀ t ∈ Set.Icc 0 T,
      d3phi_Y κ U ψ w p t ^ (1 / p t) ≤
        d3phi_Y κ U ψ w p 0 ^ (1 / p 0) * Real.exp (d3phi_gain c Cs L p t) := by
  have hT0 : 0 ≤ T := hT.le
  have hA := d3phi_identity_classical_proof hn hκ hU hT hw hψ hp.ac hp.gt_one
  have hTm : T ∈ Set.Icc 0 T := ⟨hT0, le_rfl⟩
  obtain ⟨hDi, hSi, hLi', -⟩ := hA T hTm
  set Dir : ℝ → ℝ := fun r => d3phi_dir κ U ψ w p r with hDirdef
  set Fp : ℝ → ℝ := fun r => (p r - 1) * d3phi_Sh κ U ψ ψt w p r + deriv p r * d3phi_Ylog κ U ψ w p r
    with hFpdef
  set g : ℝ → ℝ := fun r => Fp r - Dir r with hgdef
  set Y : ℝ → ℝ := fun r => d3phi_Y κ U ψ w p r with hYdef
  have hgi : IntegrableOn g (Set.Icc 0 T) := (hSi.add hLi').sub hDi
  have hgI : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).2 hgi
  -- Step 2: Y t = Y 0 + ∫_0^t g
  have hYint : ∀ t ∈ Set.Icc 0 T, Y t = Y 0 + ∫ r in (0 : ℝ)..t, g r := by
    intro t ht
    obtain ⟨hD, hS, hL2, hid⟩ := hA t ht
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    have : ∫ r in Set.Icc 0 t, g r = (∫ r in Set.Icc 0 t, Fp r) - ∫ r in Set.Icc 0 t, Dir r :=
      integral_sub (hS.add hL2) hD
    rw [this]
    have hid' : Y t + ∫ r in Set.Icc 0 t, Dir r = Y 0 + ∫ r in Set.Icc 0 t, Fp r := hid
    linarith
  -- positivity of Y and a uniform lower bound
  have hYpos : ∀ t ∈ Set.Icc 0 T, 0 < Y t := by
    intro t ht
    obtain ⟨hq, hhc, hhpos, -⟩ := d3phi_slice_facts hκ hU hw hψ ht
    haveI := hq
    exact d3phi_Y_pos _ hhc hhpos (p t)
  set I : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, g r with hIdef
  have hIac : AbsolutelyContinuousOnInterval I 0 T :=
    hgI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hT0])
  have hYI : ∀ t ∈ Set.Icc 0 T, Y 0 + I t = Y t := fun t ht => (hYint t ht).symm
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc 0 T, m ≤ Y t := by
    have hcont : ContinuousOn (fun t => Y 0 + I t) (Set.Icc 0 T) :=
      continuousOn_const.add (by simpa [Set.uIcc_of_le hT0] using hIac.continuousOn)
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT0) hcont
    refine ⟨Y 0 + I t0, by rw [hYI t0 ht0]; exact hYpos t0 ht0, fun t ht => ?_⟩
    have := hmin ht
    simp only [Set.mem_setOf_eq] at this
    rw [hYI t ht] at this
    exact this
  -- the gain integrand
  have hpc : ContinuousOn p (Set.Icc 0 T) := by
    simpa [Set.uIcc_of_le hT0] using hp.ac.continuousOn
  have hp0 : ∀ r ∈ Set.Icc 0 T, 0 < p r := fun r hr => by linarith [hp.gt_one r hr]
  set G : ℝ → ℝ := fun r => (Cs / c) * L r * ((p r - 1) / p r) with hGdef
  have hGi : IntegrableOn G (Set.Icc 0 T) := by
    have hk : ContinuousOn (fun r => (Cs / c) * ((p r - 1) / p r)) (Set.Icc 0 T) :=
      continuousOn_const.mul ((hpc.sub continuousOn_const).div hpc fun r hr => (hp0 r hr).ne')
    exact (hLi.mul_continuousOn hk isCompact_Icc).congr_fun (fun r _ => by simp only [hGdef]; ring)
      measurableSet_Icc
  have hGI : IntervalIntegrable G volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).2 hGi
  set Jt : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, G r with hJtdef
  have hJac : AbsolutelyContinuousOnInterval Jt 0 T :=
    hGI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hT0])
  -- Φ
  set Φ : ℝ → ℝ := fun t => Real.log (Y 0 + I t) * (p t)⁻¹ - Jt t with hΦdef
  have hlogac : AbsolutelyContinuousOnInterval (fun t => Real.log (Y 0 + I t)) 0 T := by
    have := (d3phi_log_lipschitzOn (Y0 := Y 0) hm0).comp_absolutelyContinuousOnInterval
      (g := I) ?_ hIac
    · exact this
    · intro t ht
      rw [Set.uIcc_of_le hT0] at ht
      have := hm t ht
      rw [← hYI t ht] at this
      simp only [Set.mem_Ici]
      linarith
  have hinvac : AbsolutelyContinuousOnInterval (fun t => (p t)⁻¹) 0 T := by
    have := d3phi_inv_lipschitzOn.comp_absolutelyContinuousOnInterval (g := p) ?_ hp.ac
    · exact this
    · intro t ht
      rw [Set.uIcc_of_le hT0] at ht
      exact (hp.gt_one t ht).le
  have hΦac : AbsolutelyContinuousOnInterval Φ 0 T := (hlogac.fun_mul hinvac).fun_sub hJac
  -- a.e. derivative of Φ is ≤ 0
  have hne0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ T := by simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Icc 0 T → deriv Φ x ≤ 0 := by
    filter_upwards [hgI.ae_hasDerivAt_integral, hGI.ae_hasDerivAt_integral, hp.ode, hne0, hneT]
      with x hxg hxG hxode hx0 hxT hxmem
    have hxIoo : x ∈ Set.Ioo 0 T := ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hx0), lt_of_le_of_ne hxmem.2 hxT⟩
    have hxu : x ∈ Set.uIcc 0 T := by rw [Set.uIcc_of_le hT0]; exact hxmem
    have hIx : HasDerivAt I (g x) x := hxg hxu 0 (by simp [hT0])
    have hJx : HasDerivAt Jt (G x) x := hxG hxu 0 (by simp [hT0])
    have hpx : HasDerivAt p (-(1 / c) * L x * p x * (p x - 1)) x := hxode hxIoo
    have hYx : 0 < Y 0 + I x := by rw [hYI x hxmem]; exact hYpos x hxmem
    have hlogx : HasDerivAt (fun t => Real.log (Y 0 + I t)) (g x / (Y 0 + I x)) x :=
      (hIx.const_add (Y 0)).log hYx.ne'
    have hinvx : HasDerivAt (fun t => (p t)⁻¹) (-(-(1 / c) * L x * p x * (p x - 1)) / (p x) ^ 2) x :=
      hpx.inv (hp0 x hxmem).ne'
    have hΦx := (hlogx.mul hinvx).sub hJx
    have hΦx' : HasDerivAt Φ _ x := hΦx
    rw [hΦx'.deriv]
    -- facts at x
    obtain ⟨hq, hhc, hhpos, hSc⟩ := d3phi_slice_facts hκ hU hw hψ hxmem
    haveI := hq
    have hLx : 0 < L x := hℓ.trans_le (hL x hxmem)
    have hDirx : 0 ≤ Dir x := by
      show 0 ≤ d3phi_dir κ U ψ w p x
      unfold d3phi_dir
      refine mul_nonneg (mul_nonneg (div_nonneg (by linarith [hp.gt_one x hxmem]) (hp0 x hxmem).le) hκ.le)
        (integral_nonneg fun y => sq_nonneg _)
    have hSh : d3phi_Sh κ U ψ ψt w p x ≤ (L x / c) * (p x * d3phi_Ylog κ U ψ w p x
        - Y x * Real.log (Y x) + Cs * Y x) := by
      have hexp' : ∫⁻ y, ENNReal.ofReal (Real.exp ((c / L x) * |d3phi_src κ U ψ ψt x y|))
          ∂(d3phi_q κ U ψ x) ≤ ENNReal.ofReal (Real.exp Cs) := by
        refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hexp x hxmem)
        rw [show c / L x * |d3phi_src κ U ψ ψt x y| = c * |d3phi_src κ U ψ ψt x y| / L x by ring]
      have := d3phi_Sh_bound (d3phi_q κ U ψ x) hhc hhpos hSc (p := p x) (div_pos hc hLx) hexp'
      have e : 1 / (c / L x) = L x / c := by field_simp
      rw [e] at this
      exact this
    have halg := d3phi_alg (hp.gt_one x hxmem) (hYpos x hxmem) hc hLx hDirx
      (p' := deriv p x) (by rw [hpx.deriv]) hSh
    have hderiv : deriv p x = -(1 / c) * L x * p x * (p x - 1) := hpx.deriv
    have hgx : g x = (p x - 1) * d3phi_Sh κ U ψ ψt w p x + deriv p x * d3phi_Ylog κ U ψ w p x - Dir x := rfl
    have hY' : Y 0 + I x = Y x := hYI x hxmem
    rw [hY', ← hderiv]
    have e : g x / Y x * (p x)⁻¹ + Real.log (Y x) * (-deriv p x / p x ^ 2) - G x =
        ((p x - 1) * d3phi_Sh κ U ψ ψt w p x + deriv p x * d3phi_Ylog κ U ψ w p x - Dir x) / (p x * Y x)
          - deriv p x * Real.log (Y x) / p x ^ 2 - (Cs / c) * L x * ((p x - 1) / p x) := by
      rw [hgx]
      simp only [hGdef]
      have := (hp0 x hxmem).ne'
      have := (hYpos x hxmem).ne'
      field_simp
      ring
    rw [e]
    exact halg
  intro t ht
  have hsub : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hT0, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  have hΦt := hΦac.mono hsub
  have hFTC := hΦt.integral_deriv_eq_sub
  have hint : ∫ x in (0 : ℝ)..t, deriv Φ x ≤ 0 := by
    calc ∫ x in (0 : ℝ)..t, deriv Φ x ≤ ∫ x in (0 : ℝ)..t, (0 : ℝ) :=
          intervalIntegral.integral_mono_ae_restrict ht.1 hΦt.intervalIntegrable_deriv
            intervalIntegrable_const
            ((ae_restrict_iff' measurableSet_Icc).2
              (hae.mono fun x hx hxm => hx ⟨hxm.1, hxm.2.trans ht.2⟩))
      _ = 0 := by simp
  have hle : Φ t ≤ Φ 0 := by linarith
  have hY0 : 0 < Y 0 := hYpos 0 ⟨le_rfl, hT0⟩
  have hYt : 0 < Y t := hYpos t ht
  have hΦ0 : Φ 0 = Real.log (Y 0) * (p 0)⁻¹ := by
    simp [hΦdef, hIdef, hJtdef]
  have hΦt' : Φ t = Real.log (Y t) * (p t)⁻¹ - d3phi_gain c Cs L p t := by
    simp only [hΦdef, hJtdef, hGdef, d3phi_gain]
    rw [hYI t ht]
  rw [hΦ0, hΦt'] at hle
  show Y t ^ (1 / p t) ≤ Y 0 ^ (1 / p 0) * Real.exp (d3phi_gain c Cs L p t)
  rw [Real.rpow_def_of_pos hYt, Real.rpow_def_of_pos hY0, ← Real.exp_add, one_div, one_div]
  exact Real.exp_le_exp.2 (by linarith)


theorem d3phi_lp_bound_proof' (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ x, ENNReal.ofReal (Real.exp (c * |d3phi_src κ U ψ ψt r x| / L r))
      ∂(d3phi_q κ U ψ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p : ℝ → ℝ} (hp : D3phiPath c L p T)
    (hac : μ 0 ≪ d3phi_q κ U ψ 0)
    (hfin : eLpNorm ((μ 0).rnDeriv (d3phi_q κ U ψ 0)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      μ t ≪ d3phi_q κ U ψ t ∧
      eLpNorm ((μ t).rnDeriv (d3phi_q κ U ψ t)) (ENNReal.ofReal (p t)) (d3phi_q κ U ψ t) ≤
        eLpNorm ((μ 0).rnDeriv (d3phi_q κ U ψ 0)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) *
          ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) := by
  intro t ht
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have h0m : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hq : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (d3phi_q κ U ψ r) := fun r hr =>
    d3phi_q_isProb hκ hU hψ hr
  haveI := hq 0 h0m
  have hZ0 := d3phi_Z_pos hκ hU hψ h0m
  have hψ0c : Continuous (ψ 0) := d3phi_slice_cont hψ h0m
  set Z0 := d3phi_Z κ U ψ 0 with hZ0def
  set ρ : Torus n → ℝ := fun x => Z0 * Real.exp (-ψ 0 x) with hρdef
  have hρc : Continuous ρ := continuous_const.mul (Real.continuous_exp.comp hψ0c.neg)
  have hρpos : ∀ x, 0 < ρ x := fun x => mul_pos hZ0 (Real.exp_pos _)
  have hp0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < p r := fun r hr => by linarith [hp.gt_one r hr]
  -- smooth positive approximants
  obtain ⟨g, hgs, hgpos, hgmass, hgnarrow, hgnorm⟩ :=
    d3phi_approx_Lp_proof (d3phi_q κ U ψ 0) hρc hρpos hac (hp.gt_one 0 h0m) hfin
  choose w hw hw0 using fun k => d3_classical_exists_proof hn hκ hU hT (hgs k) (hgpos k)
  set μk : ℕ → ℝ → Measure (Torus n) := fun k s =>
    (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w k s x) with hμkdef
  have hμk : ∀ k, D1WeakSolution κ (d1_gradDrift U) T (μk k) := fun k =>
    d3_classical_isWeak_proof hn hκ hU (hw k)
  -- the initial data of the approximants
  have hgc : ∀ k, Continuous (g k) := fun k => d1c_continuous_of_isSmooth (hgs k)
  have hconvq : ∀ k (φ : Torus n → ℝ), ∫ x, g k x * ρ x * φ x ∂(d3phi_q κ U ψ 0) =
      ∫ x, g k x * φ x ∂(d1_gibbsMeasure κ U) := by
    intro k φ
    rw [d3phi_integral_q hκ hU hψ h0m]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hρdef, Real.exp_neg]
    have hzz : d3phi_Z κ U ψ 0 = Z0 := rfl
    rw [hzz]
    have := (Real.exp_pos (ψ 0 x)).ne'
    have := hZ0.ne'
    field_simp
  have hmassk : ∀ k, ∫ x, g k x ∂(d1_gibbsMeasure κ U) = 1 := fun k => by
    have := hconvq k (fun _ => 1)
    simp only [mul_one] at this
    rw [← this]; exact hgmass k
  have hprob0 : ∀ k, IsProbabilityMeasure (μk k 0) := fun k => ⟨by
    simp only [hμkdef, hw0 k]
    rw [d3a_mass_eq (hgc k) (fun x => (hgpos k x).le), hmassk k]; simp⟩
  haveI := hprob0
  have h0conv : ∀ φ : Torus n → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(μk k 0)) atTop (𝓝 (∫ x, φ x ∂(μ 0))) := by
    intro φ hφ
    refine (hgnarrow φ hφ).congr fun k => ?_
    rw [hconvq k φ]
    simp only [hμkdef, hw0 k]
    rw [d3a_integral_withDensity (hgc k).measurable (fun x => (hgpos k x).le)]
  have hstab := d3b_stability hn hκ hU hμ hμk h0conv
  have hlev := fun k => d3pp_lp_classical_bound hn hκ hU hT (hw k) hψ hc hℓ hL hLi hexp hp
  have hnorm_k : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T,
      eLpNorm ((μk k s).rnDeriv (d3phi_q κ U ψ s)) (ENNReal.ofReal (p s)) (d3phi_q κ U ψ s) =
        ENNReal.ofReal (d3phi_Y κ U ψ (w k) p s ^ (1 / p s)) := fun k s hs =>
    d3phi_eLpNorm_rnDeriv_classical hκ hU (hw k) hψ hs (hp0 s hs)
  have hnorm0 : ∀ k, eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal (p 0))
      (d3phi_q κ U ψ 0) = ENNReal.ofReal (d3phi_Y κ U ψ (w k) p 0 ^ (1 / p 0)) := by
    intro k
    have hpos : ∀ x, 0 < g k x * ρ x := fun x => mul_pos (hgpos k x) (hρpos x)
    rw [d3phi_eLpNorm_ofReal (d3phi_q κ U ψ 0) (h := fun x => g k x * ρ x) ((hgc k).mul hρc) hpos (hp0 0 h0m)]
    have : (fun x => (g k x * ρ x) ^ p 0) = fun x => d3phi_h κ U ψ (w k) 0 x ^ p 0 := by
      funext x
      unfold d3phi_h
      rw [hw0 k]
      simp only [hρdef]
      rw [show d3phi_Z κ U ψ 0 = Z0 from rfl]
      congr 1
      ring
    unfold d3phi_Y
    rw [this]
  set a := eLpNorm ((μ 0).rnDeriv (d3phi_q κ U ψ 0)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) with ha
  set E := ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) with hE
  have hY0nn : ∀ k, 0 ≤ d3phi_Y κ U ψ (w k) p 0 ^ (1 / p 0) := fun k => by
    obtain ⟨hq', hhc, hhpos, -⟩ := d3phi_slice_facts hκ hU (hw k) hψ h0m
    haveI := hq'
    exact Real.rpow_nonneg (d3phi_Y_pos _ hhc hhpos (p 0)).le _
  have hbound : ∀ k, eLpNorm ((μk k t).rnDeriv (d3phi_q κ U ψ t)) (ENNReal.ofReal (p t))
      (d3phi_q κ U ψ t) ≤
      eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) * E := by
    intro k
    rw [hnorm_k k t ht, hnorm0 k, hE, ← ENNReal.ofReal_mul (hY0nn k)]
    exact ENNReal.ofReal_le_ofReal (hlev k t ht)
  have hlimE : Tendsto (fun k => eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x))
      (ENNReal.ofReal (p 0)) (d3phi_q κ U ψ 0) * E) atTop (𝓝 (a * E)) :=
    ENNReal.Tendsto.mul_const hgnorm (Or.inr ENNReal.ofReal_ne_top)
  have hliminf : liminf (fun k => eLpNorm ((μk k t).rnDeriv (d3phi_q κ U ψ t))
      (ENNReal.ofReal (p t)) (d3phi_q κ U ψ t)) atTop ≤ a * E := by
    calc _ ≤ liminf (fun k => eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal (p 0))
          (d3phi_q κ U ψ 0) * E) atTop := liminf_le_liminf (Eventually.of_forall hbound)
      _ = a * E := hlimE.liminf_eq
  have hlt : liminf (fun k => eLpNorm ((μk k t).rnDeriv (d3phi_q κ U ψ t))
      (ENNReal.ofReal (p t)) (d3phi_q κ U ψ t)) atTop < ⊤ :=
    lt_of_le_of_lt hliminf (ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top)
  haveI := hq t ht
  haveI : ∀ k, IsProbabilityMeasure (μk k t) := fun k => d1_isProbabilityMeasure (hμk k) ht
  haveI : IsProbabilityMeasure (μ t) := d1_isProbabilityMeasure hμ ht
  have hacn : ∀ k, μk k t ≪ d3phi_q κ U ψ t := fun k => by
    simp only [hμkdef]
    rw [d3phi_withDensity_eq hκ hU (hw k) hψ ht]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨hacT, hle⟩ := movT_lp_lsc_proof (ν := μ t) (Q := d3phi_q κ U ψ t) (νn := fun k => μk k t)
    (Qn := fun _ => d3phi_q κ U ψ t) (hν := fun φ hφ => hstab t ht φ hφ)
    (hQ := fun φ _ => tendsto_const_nhds) (Eventually.of_forall hacn) (hp.gt_one t ht) hlt
  exact ⟨hacT, hle.trans hliminf⟩

example := (@d3phi_lp_bound_proof' : type_of% @HRS.d3phi_lp_bound)


end HRS
