import HRS.PDE.TorusFPLpGlue4
import HRS.PDE.MovSpec2

/-!
# D3PHI glue, part 5: `d3phi_lp_bound` from packets A and C1 (relocated proof `d3phi_lp_bound_proof`)

Route: smooth positive densities `g_k` (packet C1) → classical solutions `w^k` (`d3_classical_exists_proof`, weak by
`d3_classical_isWeak_proof`) → `d3phi_lp_classical_bound` (from packet A) at each `k` → narrow stability of the weak solutions
(`d3b_stability`) → joint lower semicontinuity of the `L^p` norm along the constant reference `q^t` (`movT_lp_lsc`).
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS
variable {n : ℕ}

/-- `q^r = P.withDensity (e^{ψ^r}/Z̃_r)`. -/
theorem d3phi_q_eq {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {ψ : ℝ → Torus n → ℝ} {r : ℝ} (hψc : Continuous (ψ r)) :
    d3phi_q κ U ψ r = (d1_gibbsMeasure κ U).withDensity
      fun x => ENNReal.ofReal (Real.exp (ψ r x) / d3phi_Z κ U ψ r) := by
  unfold d3phi_q
  rw [d3b_tilt_eq hκ hU hψc]
  rfl

/-- `P·w_r = q^r · h_r` for a positive classical `w`. -/
theorem d3phi_withDensity_eq {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) {ψ ψt : ℝ → Torus n → ℝ}
    (hψ : IsC12Test T ψ ψt) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    (d1_gibbsMeasure κ U).withDensity (fun x => ENNReal.ofReal (w r x)) =
      (d3phi_q κ U ψ r).withDensity fun x => ENNReal.ofReal (d3phi_h κ U ψ w r x) := by
  have hψc : Continuous (ψ r) := d3phi_slice_cont hψ hr
  have hwc : Continuous (w r) := d3phi_slice_cont hw.c12 hr
  obtain ⟨-, hhc, hhpos, -⟩ := d3phi_slice_facts hκ hU hw hψ hr
  have hZ : 0 < d3phi_Z κ U ψ r := by
    haveI := d3a_gibbs_isProb (κ := κ) hU
    exact integral_exp_pos (d3a_hint _ (Real.continuous_exp.comp hψc))
  have hm1 : Measurable fun x => ENNReal.ofReal (Real.exp (ψ r x) / d3phi_Z κ U ψ r) :=
    Measurable.ennreal_ofReal (((Real.continuous_exp.comp hψc).div_const _).measurable)
  have hm2 : Measurable fun x => ENNReal.ofReal (d3phi_h κ U ψ w r x) :=
    Measurable.ennreal_ofReal hhc.measurable
  rw [d3phi_q_eq hκ hU hψc, ← withDensity_mul (d1_gibbsMeasure κ U) hm1 hm2]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
  congr 1
  unfold d3phi_h
  rw [Real.exp_neg]
  have := (Real.exp_pos (ψ r x)).ne'
  have := hZ.ne'
  field_simp


theorem d3phi_eLpNorm_ofReal (q : Measure (Torus n)) [IsProbabilityMeasure q] {h : Torus n → ℝ}
    (hhc : Continuous h) (hh : ∀ x, 0 < h x) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => ENNReal.ofReal (h x)) (ENNReal.ofReal p) q =
      ENNReal.ofReal ((∫ x, h x ^ p ∂q) ^ (1 / p)) := by
  have hpc : Continuous fun x => h x ^ p := hhc.rpow_const fun x => Or.inl (hh x).ne'
  have hm : AEStronglyMeasurable (fun x => ENNReal.ofReal (h x)) q :=
    (ENNReal.measurable_ofReal.comp hhc.measurable).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hp.le]
  have h1 : ∫⁻ x, ‖ENNReal.ofReal (h x)‖ₑ ^ p ∂q = ENNReal.ofReal (∫ x, h x ^ p ∂q) := by
    rw [ofReal_integral_eq_lintegral_ofReal (d3a_hint q hpc)
      (ae_of_all _ fun x => (Real.rpow_pos_of_pos (hh x) p).le)]
    refine lintegral_congr fun x => ?_
    rw [enorm_eq_self, ENNReal.ofReal_rpow_of_pos (hh x)]
  rw [h1, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (Real.rpow_pos_of_pos (hh x) p).le)
    (by positivity)]

/-- The `L^p(q^r)` norm of the density of `μ_r = P·w_r` w.r.t. `q^r` is `Y(r)^{1/p(r)}`. -/
theorem d3phi_eLpNorm_rnDeriv_classical {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) {ψ ψt : ℝ → Torus n → ℝ}
    (hψ : IsC12Test T ψ ψt) {r : ℝ} (hr : r ∈ Set.Icc 0 T) {p : ℝ → ℝ} (hp : 0 < p r) :
    eLpNorm (((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)).rnDeriv
        (d3phi_q κ U ψ r)) (ENNReal.ofReal (p r)) (d3phi_q κ U ψ r) =
      ENNReal.ofReal (d3phi_Y κ U ψ w p r ^ (1 / p r)) := by
  obtain ⟨hq, hhc, hhpos, -⟩ := d3phi_slice_facts hκ hU hw hψ hr
  haveI := hq
  rw [d3phi_withDensity_eq hκ hU hw hψ hr]
  have hae := Measure.rnDeriv_withDensity (d3phi_q κ U ψ r)
    (Measurable.ennreal_ofReal hhc.measurable)
  rw [eLpNorm_congr_ae hae, d3phi_eLpNorm_ofReal _ hhc hhpos hp]
  rfl


theorem d3phi_q_isProb {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (d3phi_q κ U ψ r) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hψc : Continuous (ψ r) := d3phi_slice_cont hψ hr
  unfold d3phi_q
  rw [d3b_tilt_eq hκ hU hψc]
  exact isProbabilityMeasure_tilted (d3a_hint _ (Real.continuous_exp.comp hψc))

theorem d3phi_Z_pos {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    0 < d3phi_Z κ U ψ r := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  exact integral_exp_pos (d3a_hint _ (Real.continuous_exp.comp (d3phi_slice_cont hψ hr)))

theorem d3phi_integral_q {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) {r : ℝ} (hr : r ∈ Set.Icc 0 T)
    (F : Torus n → ℝ) :
    ∫ x, F x ∂(d3phi_q κ U ψ r) =
      ∫ x, (Real.exp (ψ r x) / d3phi_Z κ U ψ r) * F x ∂(d1_gibbsMeasure κ U) := by
  have hψc : Continuous (ψ r) := d3phi_slice_cont hψ hr
  have hZ := d3phi_Z_pos hκ hU hψ hr
  rw [d3phi_q_eq hκ hU hψc]
  exact d3a_integral_withDensity (((Real.continuous_exp.comp hψc).div_const _).measurable)
    (fun x => div_nonneg (Real.exp_pos _).le hZ.le) F


theorem d3phi_lp_bound_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
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
    d3phi_approx_Lp (d3phi_q κ U ψ 0) hρc hρpos hac (hp.gt_one 0 h0m) hfin
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
  have hlev := fun k => d3phi_lp_classical_bound hn hκ hU hT (hw k) hψ hc hℓ hL hLi hexp hp
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
  obtain ⟨hacT, hle⟩ := movT_lp_lsc (ν := μ t) (Q := d3phi_q κ U ψ t) (νn := fun k => μk k t)
    (Qn := fun _ => d3phi_q κ U ψ t) (hν := fun φ hφ => hstab t ht φ hφ)
    (hQ := fun φ _ => tendsto_const_nhds) (Eventually.of_forall hacn) (hp.gt_one t ht) hlt
  exact ⟨hacT, hle.trans hliminf⟩

example := (@d3phi_lp_bound_proof : type_of% @d3phi_lp_bound)

end HRS
