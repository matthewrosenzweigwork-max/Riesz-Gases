import HRS.PDE.TorusFPLpSpec
import HRS.PDE.TorusFPEntropyMeasure

/-!
# D3PHI glue, part 4: the classical log-norm bound from the identity (packet A)

`d3phi_lp_classical_bound`: for a classical positive solution `w`, a tilt `ψ`, an exponent path `p` (`D3phiPath c L p T`) and the
exponential source bound `E_{q^r}[e^{c|S^r|/L(r)}] ≤ e^{Cs}`:
`(∫ h_t^{p(t)} dq^t)^{1/p(t)} ≤ (∫ h_0^{p(0)} dq^0)^{1/p(0)} exp(∫_0^t (Cs/c) L (p-1)/p)` (TeX L6681-6695).
Route: the entropy inequality `d3phi_dv` (Young + exponential bound, the Donsker-Varadhan step) turns packet A's source term into
`(p-1) Y (L/c)(H_p + Cs)`; with `p' = -(L/c) p (p-1)` the coefficient of `H_p` cancels exactly (`d3phi_alg`), the Dirichlet
form is dropped, and `Φ = (log Y)/p - ∫_0^t (Cs/c) L (p-1)/p` is absolutely continuous with `Φ' ≤ 0` a.e., so `Φ(t) ≤ Φ(0)`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS
variable {n : ℕ}

/-- Young's inequality `a b ≤ a log a - a + e^b` (`a > 0`). -/
theorem d3phi_young {a b : ℝ} (ha : 0 < a) : a * b ≤ a * Real.log a - a + Real.exp b := by
  have h := Real.add_one_le_exp (b - Real.log a)
  have h2 : Real.exp (b - Real.log a) = Real.exp b / a := by
    rw [Real.exp_sub, Real.exp_log ha]
  rw [h2, le_div_iff₀ ha] at h
  nlinarith

/-- The entropy (Donsker-Varadhan) step: `∫ f (c'S) dq ≤ ∫ f log f dq + Cs` for a probability density `f` of a probability
measure `q` when `E_q e^{c'|S|} ≤ e^{Cs}`. -/
theorem d3phi_dv (q : Measure (Torus n)) [IsProbabilityMeasure q] {f S : Torus n → ℝ}
    (hfc : Continuous f) (hf : ∀ x, 0 < f x) (hmass : ∫ x, f x ∂q = 1) (hSc : Continuous S)
    {c' Cs : ℝ} (hc' : 0 ≤ c')
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (c' * |S x|)) ∂q ≤ ENNReal.ofReal (Real.exp Cs)) :
    ∫ x, f x * (c' * S x) ∂q ≤ ∫ x, f x * Real.log (f x) ∂q + Cs := by
  have hflog : Continuous fun x => f x * Real.log (f x) :=
    hfc.mul (Real.continuousOn_log.comp_continuous hfc fun x => (hf x).ne')
  have hI1 : Integrable (fun x => f x * (c' * S x)) q := d3a_hint q (hfc.mul (continuous_const.mul hSc))
  have hI2 : Integrable (fun x => f x * Real.log (f x)) q := d3a_hint q hflog
  have hI3 : Integrable f q := d3a_hint q hfc
  have hEc : Continuous fun x => Real.exp (c' * S x - Cs) :=
    Real.continuous_exp.comp ((continuous_const.mul hSc).sub continuous_const)
  have hI4 : Integrable (fun x => Real.exp (c' * S x - Cs)) q := d3a_hint q hEc
  have hExpc : Continuous fun x => Real.exp (c' * |S x|) :=
    Real.continuous_exp.comp (continuous_const.mul hSc.abs)
  have hI5 : Integrable (fun x => Real.exp (c' * |S x|)) q := d3a_hint q hExpc
  -- ∫ e^{c'|S|} ≤ e^{Cs}
  have h5 : ∫ x, Real.exp (c' * |S x|) ∂q ≤ Real.exp Cs := by
    have := ofReal_integral_eq_lintegral_ofReal hI5 (ae_of_all _ fun x => (Real.exp_pos _).le)
    rw [← this] at hexp
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hexp
  have h6 : ∫ x, Real.exp (c' * S x - Cs) ∂q ≤ 1 := by
    have hpt : ∀ x, Real.exp (c' * S x - Cs) ≤ Real.exp (c' * |S x|) * Real.exp (-Cs) := fun x => by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : c' * S x ≤ c' * |S x| := mul_le_mul_of_nonneg_left (le_abs_self _) hc'
      linarith
    calc ∫ x, Real.exp (c' * S x - Cs) ∂q ≤ ∫ x, Real.exp (c' * |S x|) * Real.exp (-Cs) ∂q :=
          integral_mono hI4 (hI5.mul_const _) hpt
      _ = (∫ x, Real.exp (c' * |S x|) ∂q) * Real.exp (-Cs) := integral_mul_const _ _
      _ ≤ Real.exp Cs * Real.exp (-Cs) := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpt : ∀ x, f x * (c' * S x) - Cs * f x ≤ f x * Real.log (f x) - f x + Real.exp (c' * S x - Cs) := by
    intro x
    have := d3phi_young (hf x) (b := c' * S x - Cs)
    nlinarith
  have hint : ∫ x, (f x * (c' * S x) - Cs * f x) ∂q ≤
      ∫ x, (f x * Real.log (f x) - f x + Real.exp (c' * S x - Cs)) ∂q :=
    integral_mono (hI1.sub (hI3.const_mul Cs)) (((hI2.sub hI3).add hI4 :)) hpt
  have e1 : ∫ x, (f x * (c' * S x) - Cs * f x) ∂q = ∫ x, f x * (c' * S x) ∂q - Cs * ∫ x, f x ∂q := by
    rw [integral_sub hI1 (hI3.const_mul Cs), integral_const_mul]
  have e2 : ∫ x, (f x * Real.log (f x) - f x + Real.exp (c' * S x - Cs)) ∂q =
      ∫ x, f x * Real.log (f x) ∂q - ∫ x, f x ∂q + ∫ x, Real.exp (c' * S x - Cs) ∂q := by
    have hI23 : Integrable (fun x => f x * Real.log (f x) - f x) q := hI2.sub hI3
    have h := integral_add hI23 hI4
    have h2 : ∫ x, (f x * Real.log (f x) - f x) ∂q =
        ∫ x, f x * Real.log (f x) ∂q - ∫ x, f x ∂q := integral_sub hI2 hI3
    rw [h2] at h
    exact h
  rw [e1, e2, hmass] at hint
  linarith

/-- The algebra of the cancellation: with `p' = -(L/c) p (p-1)`, the `Φ'`-expression is `≤ 0`. -/
theorem d3phi_alg {p Y Ylog Sh Dir L c Cs p' : ℝ} (hp : 1 < p) (hY : 0 < Y) (hc : 0 < c) (hL : 0 < L)
    (hDir : 0 ≤ Dir) (hp' : p' = -(1 / c) * L * p * (p - 1))
    (hSh : Sh ≤ (L / c) * (p * Ylog - Y * Real.log Y + Cs * Y)) :
    ((p - 1) * Sh + p' * Ylog - Dir) / (p * Y) - p' * Real.log Y / p ^ 2
      - (Cs / c) * L * ((p - 1) / p) ≤ 0 := by
  have hp0 : 0 < p := by linarith
  have h1 : (p - 1) * Sh ≤ (p - 1) * ((L / c) * (p * Ylog - Y * Real.log Y + Cs * Y)) :=
    mul_le_mul_of_nonneg_left hSh (by linarith)
  have h2 : ((p - 1) * Sh + p' * Ylog - Dir) / (p * Y) ≤
      ((p - 1) * ((L / c) * (p * Ylog - Y * Real.log Y + Cs * Y)) + p' * Ylog) / (p * Y) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h3 : ((p - 1) * ((L / c) * (p * Ylog - Y * Real.log Y + Cs * Y)) + p' * Ylog) / (p * Y)
      - p' * Real.log Y / p ^ 2 - (Cs / c) * L * ((p - 1) / p) = 0 := by
    rw [hp']
    field_simp
    ring
  linarith


/-- Positivity of `Y = ∫ h^p dq` for a continuous positive `h` and a probability measure `q`. -/
theorem d3phi_Y_pos (q : Measure (Torus n)) [IsProbabilityMeasure q] {h : Torus n → ℝ}
    (hhc : Continuous h) (hh : ∀ x, 0 < h x) (p : ℝ) : 0 < ∫ x, h x ^ p ∂q := by
  have hc : Continuous fun x => h x ^ p := hhc.rpow_const fun x => Or.inl (hh x).ne'
  have hi : Integrable (fun x => h x ^ p) q := d3a_hint q hc
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.rpow_pos_of_pos (hh x) p).le) hi]
  have : Function.support (fun x => h x ^ p) = Set.univ := by
    ext x; simp [(Real.rpow_pos_of_pos (hh x) p).ne']
  rw [this]
  simp

/-- Entropy bound for the source term of `P:eq:variable-p`: `∫ S h^p dq ≤ (1/c') (p ∫h^p log h - Y log Y + Cs Y)`
whenever `E_q e^{c'|S|} ≤ e^{Cs}` (TeX `E_p[S] ≤ C₀ L H_p + C₁ L`, L6683). -/
theorem d3phi_Sh_bound (q : Measure (Torus n)) [IsProbabilityMeasure q] {h S : Torus n → ℝ}
    (hhc : Continuous h) (hh : ∀ x, 0 < h x) (hSc : Continuous S) {p : ℝ} {c' Cs : ℝ} (hc' : 0 < c')
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (c' * |S x|)) ∂q ≤ ENNReal.ofReal (Real.exp Cs)) :
    ∫ x, S x * h x ^ p ∂q ≤ (1 / c') * (p * ∫ x, h x ^ p * Real.log (h x) ∂q
      - (∫ x, h x ^ p ∂q) * Real.log (∫ x, h x ^ p ∂q) + Cs * ∫ x, h x ^ p ∂q) := by
  set Y : ℝ := ∫ x, h x ^ p ∂q with hY
  have hYpos : 0 < Y := d3phi_Y_pos q hhc hh p
  have hpc : Continuous fun x => h x ^ p := hhc.rpow_const fun x => Or.inl (hh x).ne'
  have hI1 : Integrable (fun x => h x ^ p) q := d3a_hint q hpc
  have hIlog : Integrable (fun x => h x ^ p * Real.log (h x)) q :=
    d3a_hint q (hpc.mul (Real.continuousOn_log.comp_continuous hhc fun x => (hh x).ne'))
  have hIS : Integrable (fun x => S x * h x ^ p) q := d3a_hint q (hSc.mul hpc)
  set f : Torus n → ℝ := fun x => h x ^ p / Y with hf
  have hfc : Continuous f := hpc.div_const Y
  have hfpos : ∀ x, 0 < f x := fun x => div_pos (Real.rpow_pos_of_pos (hh x) p) hYpos
  have hmass : ∫ x, f x ∂q = 1 := by
    rw [hf]; simp only; rw [integral_div, ← hY]; exact div_self hYpos.ne'
  have key := d3phi_dv q hfc hfpos hmass hSc hc'.le hexp
  -- evaluate both sides
  have e1 : ∫ x, f x * (c' * S x) ∂q = c' / Y * ∫ x, S x * h x ^ p ∂q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf]; field_simp
  have e2 : ∫ x, f x * Real.log (f x) ∂q = (p * ∫ x, h x ^ p * Real.log (h x) ∂q - Y * Real.log Y) / Y := by
    have hpt : ∀ x, f x * Real.log (f x) =
        (p / Y) * (h x ^ p * Real.log (h x)) - (Real.log Y / Y) * h x ^ p := by
      intro x
      simp only [hf]
      rw [Real.log_div (Real.rpow_pos_of_pos (hh x) p).ne' hYpos.ne', Real.log_rpow (hh x)]
      field_simp
    simp_rw [hpt]
    rw [integral_sub (hIlog.const_mul _) (hI1.const_mul _), integral_const_mul, integral_const_mul, ← hY]
    field_simp
  rw [e1, e2] at key
  have hcY : 0 < c' / Y := div_pos hc' hYpos
  have : c' / Y * ∫ x, S x * h x ^ p ∂q ≤ (p * ∫ x, h x ^ p * Real.log (h x) ∂q - Y * Real.log Y) / Y + Cs := key
  calc ∫ x, S x * h x ^ p ∂q = (Y / c') * (c' / Y * ∫ x, S x * h x ^ p ∂q) := by field_simp
    _ ≤ (Y / c') * ((p * ∫ x, h x ^ p * Real.log (h x) ∂q - Y * Real.log Y) / Y + Cs) :=
        mul_le_mul_of_nonneg_left this (div_pos hYpos hc').le
    _ = (1 / c') * (p * ∫ x, h x ^ p * Real.log (h x) ∂q - Y * Real.log Y + Cs * Y) := by
        field_simp


theorem d3phi_slice_cont {T : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test T f ft) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) : Continuous (f r) :=
  hf.continuous_f.comp (continuous_const.prodMk continuous_id : Continuous fun x : Torus n =>
    ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), x))

/-- The slice facts at a fixed time `r ∈ [0,T]`: `q^r` is a probability measure, `h_r` is continuous and positive, the source
`S^r` is continuous. -/
theorem d3phi_slice_facts {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (d3phi_q κ U ψ r) ∧ Continuous (d3phi_h κ U ψ w r) ∧
      (∀ x, 0 < d3phi_h κ U ψ w r x) ∧ Continuous (d3phi_src κ U ψ ψt r) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hψc : Continuous (ψ r) := d3phi_slice_cont hψ hr
  have hwc : Continuous (w r) := d3phi_slice_cont hw.c12 hr
  have hexpc : Integrable (fun x => Real.exp (ψ r x)) (d1_gibbsMeasure κ U) :=
    d3a_hint _ (Real.continuous_exp.comp hψc)
  have hZ : 0 < d3phi_Z κ U ψ r := integral_exp_pos hexpc
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold d3phi_q
    rw [d3b_tilt_eq hκ hU hψc]
    exact isProbabilityMeasure_tilted hexpc
  · unfold d3phi_h
    exact (hwc.mul continuous_const).mul (Real.continuous_exp.comp hψc.neg)
  · intro x
    unfold d3phi_h
    exact mul_pos (mul_pos (hw.pos r hr x) hZ) (Real.exp_pos _)
  · unfold d3phi_src
    exact (((d3b_source_cont (κ := κ) hU hψ).comp (continuous_const.prodMk continuous_id :
      Continuous fun x : Torus n => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), x)))).add continuous_const


theorem d3phi_log_lipschitzOn {Y0 m : ℝ} (hm : 0 < m) :
    LipschitzOnWith (1 / m).toNNReal (fun a : ℝ => Real.log (Y0 + a)) (Set.Ici (m - Y0)) := by
  refine (convex_Ici (m - Y0)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun a => (Y0 + a)⁻¹) (fun a ha => ?_) fun a ha => ?_
  · have hpos : 0 < Y0 + a := by simp only [Set.mem_Ici] at ha; linarith
    have h1 : HasDerivAt (fun a : ℝ => Y0 + a) 1 a := (hasDerivAt_id a).const_add Y0
    have := h1.log hpos.ne'
    simp only [one_div] at this ⊢
    simpa [div_eq_inv_mul] using this.hasDerivWithinAt
  · have hpos : m ≤ Y0 + a := by simp only [Set.mem_Ici] at ha; linarith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity),
      abs_of_pos (inv_pos.2 (by linarith))]
    rw [one_div]
    exact inv_anti₀ hm hpos

theorem d3phi_inv_lipschitzOn : LipschitzOnWith 1 (fun a : ℝ => a⁻¹) (Set.Ici 1) := by
  refine (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun a => -(a ^ 2)⁻¹) (fun a ha => ?_) fun a ha => ?_
  · have hpos : 0 < a := by simp only [Set.mem_Ici] at ha; linarith
    exact (hasDerivAt_inv hpos.ne').hasDerivWithinAt
  · have h1 : (1 : ℝ) ≤ a := ha
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one, abs_neg,
      abs_of_pos (inv_pos.2 (by positivity))]
    exact inv_le_one_of_one_le₀ (by nlinarith)

theorem d3phi_lp_classical_bound (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
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
  have hA := d3phi_identity_classical hn hκ hU hT hw hψ hp.ac hp.gt_one
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

end HRS
