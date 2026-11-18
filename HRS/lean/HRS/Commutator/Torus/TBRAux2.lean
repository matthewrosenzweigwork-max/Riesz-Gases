import HRS.Commutator.Torus.TBRAux1

/-!
# Torus helpers for the density approximation (packet T-APPROX, file 2 of 2)

Truncations `T_m σ = σ 1_{|σ| ≤ m}`, the bounded mass-one approximants `ρ_m = T_m σ / c_m`, dominated
convergence for the pair functionals `pairT` (fibre and product integrals), and the convergence of
`‖ρ_m‖_p → ‖σ‖_p` for `p < ∞` (via the integral formula) and `p = ∞` (essential bound).
Names carry the prefix `tbr_`; the namespace is `HRS.Commutator.TorusNote`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Truncation `T_m σ(x) = σ(x)` if `|σ(x)| ≤ m`, else `0`. -/
def tbrTrunc (σ : Torus d → ℝ) (m : ℕ) (x : Torus d) : ℝ :=
  if |σ x| ≤ (m : ℝ) then σ x else 0

/-- Mass `c_m = ∫ T_m σ`. -/
def tbrCc (σ : Torus d → ℝ) (m : ℕ) : ℝ := ∫ x, tbrTrunc σ m x

/-- The bounded mass-one approximant `ρ_m = T_m σ / c_m` (the constant `1` if `c_m = 0`). -/
def tbrRho (σ : Torus d → ℝ) (m : ℕ) (x : Torus d) : ℝ :=
  if tbrCc σ m = 0 then 1 else tbrTrunc σ m x / tbrCc σ m

theorem tbr_trunc_measurable {σ : Torus d → ℝ} (hσ : Measurable σ) (m : ℕ) :
    Measurable (tbrTrunc σ m) :=
  Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hσ) measurable_const) hσ
    measurable_const

theorem tbr_trunc_abs_le (σ : Torus d → ℝ) (m : ℕ) (x : Torus d) :
    |tbrTrunc σ m x| ≤ |σ x| := by
  unfold tbrTrunc
  split_ifs with h
  · exact le_rfl
  · simp

theorem tbr_trunc_le (σ : Torus d → ℝ) (m : ℕ) (x : Torus d) :
    |tbrTrunc σ m x| ≤ m := by
  unfold tbrTrunc
  split_ifs with h
  · exact h
  · simp

theorem tbr_trunc_eventually (σ : Torus d → ℝ) (x : Torus d) :
    ∀ᶠ m : ℕ in atTop, tbrTrunc σ m x = σ x := by
  obtain ⟨n, hn⟩ := exists_nat_ge |σ x|
  filter_upwards [eventually_ge_atTop n] with m hm
  unfold tbrTrunc
  rw [if_pos]
  exact le_trans hn (by exact_mod_cast hm)

theorem tbr_trunc_tendsto_pt (σ : Torus d → ℝ) (x : Torus d) :
    Tendsto (fun m : ℕ => tbrTrunc σ m x) atTop (𝓝 (σ x)) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [tbr_trunc_eventually σ x] with m hm
    exact hm.symm)

theorem tbr_cc_tendsto {σ : Torus d → ℝ} (hσ : Measurable σ) (hσI : Integrable σ) :
    Tendsto (tbrCc σ) atTop (𝓝 (∫ x, σ x)) := by
  unfold tbrCc
  refine tendsto_integral_of_dominated_convergence (fun x => ‖σ x‖)
    (fun m => (tbr_trunc_measurable hσ m).aestronglyMeasurable) hσI.norm
    (fun m => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => tbr_trunc_tendsto_pt σ x)
  simp only [Real.norm_eq_abs]
  exact tbr_trunc_abs_le σ m x

theorem tbr_rho_measurable {σ : Torus d → ℝ} (hσ : Measurable σ) (m : ℕ) :
    Measurable (tbrRho σ m) := by
  unfold tbrRho
  by_cases hc : tbrCc σ m = 0
  · simp only [if_pos hc]
    exact measurable_const
  · simp only [if_neg hc]
    exact (tbr_trunc_measurable hσ m).div_const _

theorem tbr_rho_bdd (σ : Torus d → ℝ) (m : ℕ) : ∃ B : ℝ, ∀ x, |tbrRho σ m x| ≤ B := by
  refine ⟨(m : ℝ) / |tbrCc σ m| + 1, fun x => ?_⟩
  unfold tbrRho
  by_cases hc : tbrCc σ m = 0
  · simp [hc]
  · rw [if_neg hc, abs_div]
    have h1 := tbr_trunc_le σ m x
    have h2 : 0 ≤ (m : ℝ) / |tbrCc σ m| := div_nonneg (Nat.cast_nonneg m) (abs_nonneg _)
    have h3 : |tbrTrunc σ m x| / |tbrCc σ m| ≤ (m : ℝ) / |tbrCc σ m| :=
      div_le_div_of_nonneg_right h1 (abs_nonneg _)
    linarith

theorem tbr_rho_mass (σ : Torus d → ℝ) (m : ℕ) : ∫ x, tbrRho σ m x = 1 := by
  unfold tbrRho
  by_cases hc : tbrCc σ m = 0
  · simp [hc]
  · simp only [if_neg hc]
    rw [integral_div]
    exact div_self hc

theorem tbr_rho_tendsto {σ : Torus d → ℝ} (hσ : Measurable σ) (hσI : Integrable σ)
    (hmass : ∫ x, σ x = 1) (x : Torus d) :
    Tendsto (fun m => tbrRho σ m x) atTop (𝓝 (σ x)) := by
  have hcc : Tendsto (tbrCc σ) atTop (𝓝 1) := by
    have := tbr_cc_tendsto hσ hσI
    rwa [hmass] at this
  have hq := (tbr_trunc_tendsto_pt σ x).div hcc one_ne_zero
  rw [div_one] at hq
  refine Tendsto.congr' ?_ hq
  filter_upwards [hcc.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with m hm
  have hc : tbrCc σ m ≠ 0 := by
    intro h
    rw [h] at hm
    norm_num at hm
  unfold tbrRho
  rw [if_neg hc]
  rfl

theorem tbr_rho_bound_ev {σ : Torus d → ℝ} (hσ : Measurable σ) (hσI : Integrable σ)
    (hmass : ∫ x, σ x = 1) :
    ∀ᶠ m : ℕ in atTop, ∀ x, |tbrRho σ m x| ≤ 2 * ‖σ x‖ := by
  have hcc : Tendsto (tbrCc σ) atTop (𝓝 1) := by
    have := tbr_cc_tendsto hσ hσI
    rwa [hmass] at this
  filter_upwards [hcc.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with m hm x
  have hc : tbrCc σ m ≠ 0 := by
    intro h
    rw [h] at hm
    norm_num at hm
  have hpos : (1 / 2 : ℝ) ≤ |tbrCc σ m| := hm.le.trans (le_abs_self _)
  unfold tbrRho
  rw [if_neg hc, abs_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hpos)]
  have h1 := tbr_trunc_abs_le σ m x
  have hn : |σ x| = ‖σ x‖ := (Real.norm_eq_abs _).symm
  nlinarith [mul_nonneg (norm_nonneg (σ x)) (sub_nonneg.2 hpos)]

/-! ### The pair functional: congruence and dominated convergence -/

theorem tbr_pairT_congr (K : Torus d → Torus d → ℝ) {N : ℕ} (X : Config d N)
    {ρ σ : Torus d → ℝ} (h : ρ =ᵐ[volume] σ) : pairT K X ρ = pairT K X σ := by
  unfold pairT
  have h2 : ∀ i, ∫ y, K (X i) y * ρ y = ∫ y, K (X i) y * σ y := fun i =>
    integral_congr_ae (h.mono fun y hy => by simp only [hy])
  have h3 : ∫ x, ∫ y, K x y * ρ x * ρ y = ∫ x, ∫ y, K x y * σ x * σ y := by
    refine integral_congr_ae (h.mono fun x hx => ?_)
    refine integral_congr_ae (h.mono fun y hy => ?_)
    simp only [hx, hy]
  simp only [h2, h3]

theorem tbr_norm_mul_le {a b c : ℝ} (hb : |b| ≤ 2 * ‖c‖) : ‖a * b‖ ≤ 2 * ‖a * ‖c‖‖ := by
  rw [norm_mul, norm_mul, norm_norm, Real.norm_eq_abs b]
  calc ‖a‖ * |b| ≤ ‖a‖ * (2 * ‖c‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 2 * (‖a‖ * ‖c‖) := by ring

theorem tbr_norm_mul2_le {K b1 b2 c1 c2 : ℝ} (h1 : |b1| ≤ 2 * ‖c1‖) (h2 : |b2| ≤ 2 * ‖c2‖) :
    ‖K * b1 * b2‖ ≤ 4 * ‖K * ‖c1‖ * ‖c2‖‖ := by
  simp only [norm_mul, norm_norm]
  rw [Real.norm_eq_abs b1, Real.norm_eq_abs b2]
  calc ‖K‖ * |b1| * |b2| ≤ ‖K‖ * (2 * ‖c1‖) * (2 * ‖c2‖) := by
        gcongr
    _ = 4 * (‖K‖ * ‖c1‖ * ‖c2‖) := by ring

/-- Dominated convergence for `pairT`: fibre integrals and the double integral. -/
theorem tbr_pairT_tendsto {K : Torus d → Torus d → ℝ} {N : ℕ} (X : Config d N)
    {σ : Torus d → ℝ} {ρm : ℕ → Torus d → ℝ} (hσ : Measurable σ) (hρm : ∀ m, Measurable (ρm m))
    (hKm : Measurable (fun z : Torus d × Torus d => K z.1 z.2))
    (hKσ : PairIntegrableT K X (fun y => ‖σ y‖))
    (hbd : ∀ᶠ m in atTop, ∀ x, |ρm m x| ≤ 2 * ‖σ x‖)
    (hlim : ∀ x, Tendsto (fun m => ρm m x) atTop (𝓝 (σ x))) :
    Tendsto (fun m => pairT K X (ρm m)) atTop (𝓝 (pairT K X σ)) := by
  have hS : Tendsto (fun m => ∑ i, ∫ y, K (X i) y * ρm m y) atTop
      (𝓝 (∑ i, ∫ y, K (X i) y * σ y)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    have hKx : Measurable (fun y => K (X i) y) := hKm.comp (measurable_const.prodMk measurable_id)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => 2 * ‖K (X i) y * ‖σ y‖‖)
      (Filter.Eventually.of_forall fun m => (hKx.aestronglyMeasurable.mul
        (hρm m).aestronglyMeasurable))
      ?_ ((hKσ.1 i).norm.const_mul 2)
      (Filter.Eventually.of_forall fun y => (hlim y).const_mul (K (X i) y))
    filter_upwards [hbd] with m hm
    exact Filter.Eventually.of_forall fun y => tbr_norm_mul_le (hm y)
  have hD : Tendsto (fun m => ∫ x, ∫ y, K x y * ρm m x * ρm m y) atTop
      (𝓝 (∫ x, ∫ y, K x y * σ x * σ y)) := by
    have hgI := hKσ.2.norm
    have hfinf : Integrable (fun z : Torus d × Torus d => K z.1 z.2 * σ z.1 * σ z.2)
        ((volume : Measure (Torus d)).prod volume) := by
      refine Integrable.mono' hgI ?_ (Filter.Eventually.of_forall fun z => le_of_eq ?_)
      · exact ((hKm.aestronglyMeasurable.mul (hσ.comp measurable_fst).aestronglyMeasurable).mul
          (hσ.comp measurable_snd).aestronglyMeasurable)
      · simp only [norm_mul, norm_norm]
    have hint : ∀ m, (∀ x, |ρm m x| ≤ 2 * ‖σ x‖) →
        Integrable (fun z : Torus d × Torus d => K z.1 z.2 * ρm m z.1 * ρm m z.2)
          ((volume : Measure (Torus d)).prod volume) := fun m hm =>
      Integrable.mono' (hKσ.2.norm.const_mul 4)
        ((hKm.mul ((hρm m).comp measurable_fst)).mul ((hρm m).comp measurable_snd)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => tbr_norm_mul2_le (hm z.1) (hm z.2))
    have hPl := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Torus d)).prod volume)
      (F := fun m (z : Torus d × Torus d) => K z.1 z.2 * ρm m z.1 * ρm m z.2)
      (f := fun z : Torus d × Torus d => K z.1 z.2 * σ z.1 * σ z.2)
      (fun z : Torus d × Torus d => 4 * ‖K z.1 z.2 * ‖σ z.1‖ * ‖σ z.2‖‖) (l := atTop)
      (hbd.mono fun m _ => ((hKm.mul ((hρm m).comp measurable_fst)).mul
        ((hρm m).comp measurable_snd)).aestronglyMeasurable)
      (hbd.mono fun m hm => Filter.Eventually.of_forall fun z => tbr_norm_mul2_le (hm z.1) (hm z.2))
      (hKσ.2.norm.const_mul 4)
      (Filter.Eventually.of_forall fun z => ((hlim z.1).const_mul (K z.1 z.2)).mul (hlim z.2))
    have e0 : ∫ x, ∫ y, K x y * σ x * σ y =
        ∫ z : Torus d × Torus d, K z.1 z.2 * σ z.1 * σ z.2 ∂((volume : Measure (Torus d)).prod volume) :=
      (integral_prod (fun z : Torus d × Torus d => K z.1 z.2 * σ z.1 * σ z.2) hfinf).symm
    rw [e0]
    refine Tendsto.congr' ?_ hPl
    filter_upwards [hbd] with m hm
    exact integral_prod (fun z : Torus d × Torus d => K z.1 z.2 * ρm m z.1 * ρm m z.2) (hint m hm)
  unfold pairT
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hS)).add hD

/-! ### Norms of the approximants -/

theorem tbr_normT_eq_rpow {f : Torus d → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hf : MemLp f p volume) :
    normT p f = (∫ x, ‖f x‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  unfold normT
  rw [hf.eLpNorm_eq_integral_rpow_norm hp0 hpt, ENNReal.toReal_ofReal]
  exact Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _

/-- `‖ρ_m‖_p → ‖σ‖_p` for `0 < p < ∞`. -/
theorem tbr_normT_tendsto_fin {σ : Torus d → ℝ} {ρm : ℕ → Torus d → ℝ} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hσp : MemLp σ p volume) (hρm : ∀ m, Measurable (ρm m))
    (hρb : ∀ m, ∃ B : ℝ, ∀ x, |ρm m x| ≤ B)
    (hbd : ∀ᶠ m in atTop, ∀ x, |ρm m x| ≤ 2 * ‖σ x‖)
    (hlim : ∀ x, Tendsto (fun m => ρm m x) atTop (𝓝 (σ x))) :
    Tendsto (fun m => normT p (ρm m)) atTop (𝓝 (normT p σ)) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hMem : ∀ m, MemLp (ρm m) p volume := fun m => by
    obtain ⟨B, hB⟩ := hρb m
    exact MemLp.of_bound (hρm m).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hB x)
  have hform : (fun m => normT p (ρm m)) =
      fun m => (∫ x, ‖ρm m x‖ ^ p.toReal) ^ p.toReal⁻¹ :=
    funext fun m => tbr_normT_eq_rpow hp0 hpt (hMem m)
  rw [hform, tbr_normT_eq_rpow hp0 hpt hσp]
  refine Tendsto.rpow_const ?_ (Or.inr (inv_nonneg.2 hr.le))
  have hgI : Integrable (fun x => (2 : ℝ) ^ p.toReal * ‖σ x‖ ^ p.toReal) :=
    (hσp.integrable_norm_rpow hp0 hpt).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => (2 : ℝ) ^ p.toReal * ‖σ x‖ ^ p.toReal)
    (Filter.Eventually.of_forall fun m => ((hρm m).norm.pow_const _).aestronglyMeasurable)
    ?_ hgI (Filter.Eventually.of_forall fun x => ((hlim x).norm.rpow_const (Or.inr hr.le)))
  filter_upwards [hbd] with m hm
  refine Filter.Eventually.of_forall fun x => ?_
  have hnn : 0 ≤ ‖ρm m x‖ ^ p.toReal := Real.rpow_nonneg (norm_nonneg _) _
  rw [Real.norm_of_nonneg hnn]
  calc ‖ρm m x‖ ^ p.toReal ≤ (2 * ‖σ x‖) ^ p.toReal :=
        Real.rpow_le_rpow (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hm x) hr.le
    _ = (2 : ℝ) ^ p.toReal * ‖σ x‖ ^ p.toReal := Real.mul_rpow (by norm_num) (norm_nonneg _)

theorem tbr_ae_norm_le_normT_top {σ : Torus d → ℝ} (hσtop : MemLp σ ⊤ volume) :
    ∀ᵐ x ∂(volume : Measure (Torus d)), ‖σ x‖ ≤ normT ⊤ σ := by
  have hfin : eLpNorm σ ⊤ volume < ⊤ := hσtop.eLpNorm_lt_top
  have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), ‖σ x‖ₑ ≤ eLpNorm σ ⊤ volume := by
    rw [eLpNorm_exponent_top hσtop.aestronglyMeasurable]
    exact ae_le_eLpNormEssSup
  filter_upwards [hae] with x hx
  unfold normT
  rw [← toReal_enorm (σ x)]
  exact ENNReal.toReal_mono hfin.ne hx

/-- `‖ρ_m‖_∞ → ‖σ‖_∞` for a mass-one `σ ∈ L^∞ ∩ L^1`. -/
theorem tbr_normT_tendsto_top {σ : Torus d → ℝ} (hσ : Measurable σ) (hσI : Integrable σ)
    (hmass : ∫ x, σ x = 1) (hσtop : MemLp σ ⊤ volume) :
    Tendsto (fun m => normT ⊤ (tbrRho σ m)) atTop (𝓝 (normT ⊤ σ)) := by
  have hcc : Tendsto (tbrCc σ) atTop (𝓝 1) := by
    have := tbr_cc_tendsto hσ hσI
    rwa [hmass] at this
  have hae := tbr_ae_norm_le_normT_top hσtop
  have hev : ∀ᶠ m : ℕ in atTop, (normT ⊤ σ ≤ (m : ℝ)) ∧ (1 / 2 : ℝ) < tbrCc σ m := by
    refine Filter.Eventually.and ?_ (hcc.eventually (lt_mem_nhds (by norm_num)))
    obtain ⟨n, hn⟩ := exists_nat_ge (normT ⊤ σ)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact le_trans hn (by exact_mod_cast hm)
  have hlimM : Tendsto (fun m : ℕ => |(tbrCc σ m)⁻¹| * normT ⊤ σ) atTop
      (𝓝 (|(1 : ℝ)⁻¹| * normT ⊤ σ)) :=
    ((hcc.inv₀ one_ne_zero).abs).mul_const _
  rw [show |(1 : ℝ)⁻¹| * normT ⊤ σ = normT ⊤ σ by simp] at hlimM
  refine Tendsto.congr' ?_ hlimM
  filter_upwards [hev] with m hm
  obtain ⟨hmM, hc⟩ := hm
  have hc0 : tbrCc σ m ≠ 0 := by
    intro h
    rw [h] at hc
    norm_num at hc
  have hae2 : tbrRho σ m =ᵐ[volume] (tbrCc σ m)⁻¹ • σ := by
    filter_upwards [hae] with x hx
    have hle : |σ x| ≤ (m : ℝ) := by
      rw [← Real.norm_eq_abs]
      exact le_trans hx hmM
    have htr : tbrTrunc σ m x = σ x := by
      unfold tbrTrunc
      rw [if_pos hle]
    unfold tbrRho
    rw [if_neg hc0, htr, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  calc |(tbrCc σ m)⁻¹| * normT ⊤ σ = normT ⊤ ((tbrCc σ m)⁻¹ • σ) := by
        unfold normT
        rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]
    _ = normT ⊤ (tbrRho σ m) := by
        unfold normT
        rw [eLpNorm_congr_ae hae2.symm]

/-- Joint measurability of the commutator kernel (as in `AbsConv`). -/
theorem tbr_commKernel_measurable {s L : ℝ} {v : Torus d → Euc d} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) (hsd : s < (d : ℝ)) :
    Measurable (fun z : Torus d × Torus d => commKernel (periodicRieszGrad d s) v z.1 z.2) := by
  have hvc : Continuous v := IsLipschitzVF.continuous hL hv
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
  · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)

end HRS.Commutator.TorusNote
