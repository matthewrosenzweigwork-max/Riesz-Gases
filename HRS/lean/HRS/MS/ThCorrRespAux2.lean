import HRS.MS.ThCorrRespAux1
import HRS.MS.ThmLogAux2
import HRS.MS.WrKernAux1

/-!
# TC-2 (response operator, `s = 0`), part 2: the shifted logarithmic kernel `K̃ = t67K d` on `L²(μ)`

Namespace `HRS.MS.TcR`; helper lemmas carry the prefix `tc2_`.  No existing file is edited.

Let `ρ` be a probability density with `ρ ≤ M₀ exp (-c ‖x‖²)` (`0 < c`) and `μ = HRS.Whole.withDensityReal ρ`.  Then:

* `tc2_l_memLp`: `l = t67l = log (1 + ‖x‖²) ∈ L²(μ)`;
* `tc2_bound`: Schur bound for `K̃` from `t67K_le` (`K̃ ≤ k₁(x-y) + l(y)`, `k₁ = 1_{B(0,1)} (-log ‖·‖) + C₀`)
  and `wr13c_schur_W` for the part `k₁` (rank-one remainder through Cauchy-Schwarz and `l ∈ L²(μ)`);
  hence `TcKer μ K̃ Mg` (`tc2_tcker_log`);
* `tc2_pos_log`: `TcPos μ K̃` (conditional positivity on `L²_0(μ)`), from `t67_k2` applied to `u = ρ f`
  (the absolute integrability `habs` comes from the pair integrability of `TcKer`);
* `tc2_kop_log`: for measurable `f ∈ L²_0(μ)`, `Kop (rieszKernel d 0) μ f =ᵐ[μ] T̃ f - μ(T̃ f)`, where
  `T̃ f x = ∫ K̃(x,y) f(y) dμ(y)` (the `l(x)` term dies by `μ(f) = 0`, the `l(y)` term is the constant `½ ∫ l f dμ`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.MS.TcR

open HRS.Whole HRS.Whole.Q34 HRS.MS.Thm

variable {d : ℕ}

section Conv

variable {ρ : Euc d → ℝ}

theorem tc2_integral_nu (hρ : HRS.Whole.IsProbDensity ρ) (g : Euc d → ℝ) :
    ∫ x, g x ∂(HRS.Whole.withDensityReal ρ) = ∫ x, ρ x * g x := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg x)]

theorem tc2_integrable_nu (hρ : HRS.Whole.IsProbDensity ρ) (g : Euc d → ℝ) :
    Integrable g (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun x => ρ x * g x) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg x)]

theorem tc2_M0_nonneg (hρ : HRS.Whole.IsProbDensity ρ) {M₀ c : ℝ}
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) : 0 ≤ M₀ := by
  have := hg 0
  simp at this
  exact (hρ.nonneg 0).trans this

theorem tc2_le_M0 (hρ : HRS.Whole.IsProbDensity ρ) {M₀ c : ℝ} (hc : 0 < c)
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) (x : Euc d) : ρ x ≤ M₀ := by
  have hM0 := tc2_M0_nonneg hρ hg
  have h1 : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
  calc ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hg x
    _ ≤ M₀ * 1 := mul_le_mul_of_nonneg_left h1 hM0
    _ = M₀ := mul_one _

/-- `l(x) = log (1 + ‖x‖²)` is in `L²(μ)` for a Gaussian-bounded density. -/
theorem tc2_l_memLp (hρ : HRS.Whole.IsProbDensity ρ) {M₀ c : ℝ} (hc : 0 < c)
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) :
    MemLp (t67l : Euc d → ℝ) 2 (HRS.Whole.withDensityReal ρ) := by
  have hM0 := tc2_M0_nonneg hρ hg
  refine (memLp_two_iff_integrable_sq t67l_measurable.aestronglyMeasurable).2 ?_
  rw [tc2_integrable_nu hρ]
  have h1 := (t012_integrable_exp_neg_sq (d := d) (b := c / 2) (by positivity)).const_mul
    (8 * M₀ / c ^ 2)
  refine Integrable.mono' h1 (hρ.measurable.mul (t67l_measurable.pow_const 2)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hl0 := t67l_nonneg (d := d) x
  have hl1 := t67l_le_sq (d := d) x
  have h4 : t67l x ^ 2 ≤ (‖x‖ ^ 2) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
  have hx0 : 0 ≤ c / 2 * ‖x‖ ^ 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx0
  have hexp : (‖x‖ ^ 2) ^ 2 ≤ 8 / c ^ 2 * Real.exp (c / 2 * ‖x‖ ^ 2) := by
    have hc2 : 0 < c ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith [Real.exp_pos (c / 2 * ‖x‖ ^ 2), sq_nonneg (‖x‖ ^ 2)]
  have hprod : Real.exp (-c * ‖x‖ ^ 2) * Real.exp (c / 2 * ‖x‖ ^ 2) =
      Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (sq_nonneg _))]
  calc ρ x * t67l x ^ 2 ≤ (M₀ * Real.exp (-c * ‖x‖ ^ 2)) * ((‖x‖ ^ 2) ^ 2) :=
        mul_le_mul (hg x) h4 (sq_nonneg _) (mul_nonneg hM0 (Real.exp_pos _).le)
    _ ≤ (M₀ * Real.exp (-c * ‖x‖ ^ 2)) * (8 / c ^ 2 * Real.exp (c / 2 * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hM0 (Real.exp_pos _).le)
    _ = 8 * M₀ / c ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
        rw [← hprod]; ring

end Conv

section Kernel

/-- `C₀ = ½ log 3 + ½ log 2`. -/
def tc2_C0 : ℝ := (1 / 2) * Real.log 3 + (1 / 2) * Real.log 2

theorem tc2_C0_nonneg : 0 ≤ tc2_C0 := by
  unfold tc2_C0
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The singular part of the majorant: `k₁(z) = 1_{B(0,1)}(z) (-log ‖z‖) + C₀`. -/
def tc2_k1 (d : ℕ) (z : Euc d) : ℝ :=
  (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z + tc2_C0

theorem tc2_k1_nonneg (z : Euc d) : 0 ≤ tc2_k1 d z :=
  add_nonneg (t67_ind_nonneg z) tc2_C0_nonneg

theorem tc2_k1_measurable : Measurable (tc2_k1 d) :=
  ((t67_g_measurable (d := d)).indicator Metric.isOpen_ball.measurableSet).add measurable_const

theorem tc2_K_le (x y : Euc d) : t67K d x y ≤ tc2_k1 d (x - y) + t67l y := by
  have := t67K_le x y
  unfold tc2_k1 tc2_C0
  linarith

theorem tc2_k1_le_W (z : Euc d) : |tc2_k1 d z| ≤ (1 + tc2_C0) * (1 + rieszWeight 0 z) := by
  rw [abs_of_nonneg (tc2_k1_nonneg z)]
  have hW : rieszWeight 0 z = max (-Real.log ‖z‖) 0 := by simp [rieszWeight]
  have hW0 : 0 ≤ rieszWeight 0 z := by rw [hW]; exact le_max_right _ _
  have hC := tc2_C0_nonneg
  by_cases hb : z ∈ Metric.ball (0 : Euc d) 1
  · have hlt : ‖z‖ < 1 := by simpa using hb
    have hlog : -Real.log ‖z‖ ≥ 0 := by
      have := Real.log_nonpos (norm_nonneg z) hlt.le
      linarith
    have hW' : rieszWeight 0 z = -Real.log ‖z‖ := by rw [hW]; exact max_eq_left hlog
    unfold tc2_k1
    rw [Set.indicator_of_mem hb, t67_g, hW']
    nlinarith [mul_nonneg hC hlog]
  · unfold tc2_k1
    rw [Set.indicator_of_notMem hb]
    nlinarith [mul_nonneg hC hW0]

/-- Schur test for the majorant `k₁`. -/
theorem tc2_schur_k1 (hd : 1 ≤ d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ F : Euc d → ℝ≥0∞, Measurable F →
        ∫⁻ x, (∫⁻ y, ENNReal.ofReal (tc2_k1 d (x - y)) * F y ∂(HRS.Whole.withDensityReal ρ)) ^ 2
            ∂(HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal C ^ 2 * ∫⁻ y, F y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Wr.wr13c_schur_W hd (s := 0) (le_refl 0) hd0 M
  have hB : 0 ≤ 1 + tc2_C0 := by have := tc2_C0_nonneg; linarith
  refine ⟨C * (1 + tc2_C0), mul_nonneg hC0 hB, fun ρ hρ hM F hF => ?_⟩
  have habs : ∀ z : Euc d, |tc2_k1 d z| = tc2_k1 d z := fun z => abs_of_nonneg (tc2_k1_nonneg z)
  have := hC ρ hρ hM (1 + tc2_C0) hB (fun x y => tc2_k1 d (x - y))
    (tc2_k1_measurable.comp (measurable_fst.sub measurable_snd))
    (fun x y _ => tc2_k1_le_W (x - y)) F hF
  simpa only [habs] using this

/-- Cauchy-Schwarz in `lintegral` form. -/
theorem tc2_cs_sq {α : Type*} [MeasurableSpace α] (m : Measure α) (f g : α → ℝ≥0∞)
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    (∫⁻ a, f a * g a ∂m) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂m) * ∫⁻ a, g a ^ 2 ∂m := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m (p := 2) (q := 2)
    (by exact Real.HolderConjugate.two_two) hf hg
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 := pow_le_pow_left' h 2
  rw [mul_pow, hsq, hsq] at h2
  simpa [ENNReal.rpow_two] using h2

theorem tc2_lintegral_sq_abs {ν : Measure (Euc d)} {u : Euc d → ℝ} (hu2 : MemLp u 2 ν) :
    ∫⁻ y, ENNReal.ofReal |u y| ^ 2 ∂ν = ENNReal.ofReal (∫ x, u x ^ 2 ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hu2.integrable_sq)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The Schur bound for `K̃` on `L²(μ)`. -/
theorem tc2_bound (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M₀ c : ℝ} (hc : 0 < c)
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ Mg : ℝ, 0 ≤ Mg ∧ ∀ u : Euc d → ℝ, Measurable u → MemLp u 2 (HRS.Whole.withDensityReal ρ) →
      ∫⁻ x, tc2_Nu (HRS.Whole.withDensityReal ρ) (t67K d) u x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (Mg ^ 2 * ∫ x, u x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hM : ∀ x, ρ x ≤ M₀ := tc2_le_M0 hρ hc hg
  obtain ⟨Cs, hCs0, hCs⟩ := tc2_schur_k1 hd M₀
  have hl2 := tc2_l_memLp hρ hc hg
  set L := ∫ x, t67l x ^ 2 ∂ν with hL
  have hL0 : 0 ≤ L := integral_nonneg fun x => sq_nonneg _
  refine ⟨Real.sqrt (2 * (Cs ^ 2 + L)), Real.sqrt_nonneg _, fun u hu hu2 => ?_⟩
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |u y| with hF
  have hFm : Measurable F := hu.abs.ennreal_ofReal
  set I := ∫ x, u x ^ 2 ∂ν with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hF2 : ∫⁻ y, F y ^ 2 ∂ν = ENNReal.ofReal I := tc2_lintegral_sq_abs hu2
  have hlf : ∫⁻ y, ENNReal.ofReal |t67l y| ^ 2 ∂ν = ENNReal.ofReal L :=
    tc2_lintegral_sq_abs hl2
  set c1 : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal |t67l y| * F y ∂ν with hc1
  have hc1sq : c1 ^ 2 ≤ ENNReal.ofReal L * ENNReal.ofReal I := by
    rw [← hlf, ← hF2]
    exact tc2_cs_sq ν (fun y => ENNReal.ofReal |t67l y|) F
      t67l_measurable.abs.ennreal_ofReal.aemeasurable hFm.aemeasurable
  set A : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (tc2_k1 d (x - y)) * F y ∂ν with hA
  have hpt : ∀ x, tc2_Nu ν (t67K d) u x ≤ A x + c1 := by
    intro x
    have hm1 : Measurable (fun y : Euc d => ENNReal.ofReal (tc2_k1 d (x - y)) * F y) :=
      (tc2_k1_measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal.mul hFm
    calc tc2_Nu ν (t67K d) u x = ∫⁻ y, ENNReal.ofReal (t67K d x y) * F y ∂ν := rfl
      _ ≤ ∫⁻ y, (ENNReal.ofReal (tc2_k1 d (x - y)) * F y +
            ENNReal.ofReal |t67l y| * F y) ∂ν := by
          refine lintegral_mono fun y => ?_
          rw [← add_mul]
          refine mul_le_mul' ?_ le_rfl
          rw [abs_of_nonneg (t67l_nonneg y), ← ENNReal.ofReal_add (tc2_k1_nonneg _)
            (t67l_nonneg y)]
          exact ENNReal.ofReal_le_ofReal (tc2_K_le x y)
      _ = A x + c1 := lintegral_add_left hm1 _
  have hAsq : ∫⁻ x, A x ^ 2 ∂ν ≤ ENNReal.ofReal Cs ^ 2 * ENNReal.ofReal I := by
    rw [← hF2]; exact hCs ρ hρ hM F hFm
  calc ∫⁻ x, tc2_Nu ν (t67K d) u x ^ 2 ∂ν ≤ ∫⁻ x, 2 * (A x ^ 2 + c1 ^ 2) ∂ν :=
        lintegral_mono fun x => (pow_le_pow_left' (hpt x) 2).trans (add_sq_le _ _)
    _ = 2 * (∫⁻ x, A x ^ 2 ∂ν + c1 ^ 2) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ 2 * (ENNReal.ofReal Cs ^ 2 * ENNReal.ofReal I + ENNReal.ofReal L * ENNReal.ofReal I) :=
        mul_le_mul' le_rfl (add_le_add hAsq hc1sq)
    _ = ENNReal.ofReal (Real.sqrt (2 * (Cs ^ 2 + L)) ^ 2 * I) := by
        rw [Real.sq_sqrt (by positivity)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_pow hCs0,
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hL0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

theorem tc2_tcker_log (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M₀ c : ℝ} (hc : 0 < c)
    (hg : ∀ x, ρ x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ Mg : ℝ, TcKer (HRS.Whole.withDensityReal ρ) (t67K d) Mg := by
  obtain ⟨Mg, hMg0, hb⟩ := tc2_bound hd hρ hc hg
  exact ⟨Mg, ⟨t67K_measurable, t67K_nonneg, t67K_symm, hMg0, hb⟩⟩

end Kernel

section PosKop

variable {ρ : Euc d → ℝ}

/-- Conditional positivity of `K̃` on `L²_0(μ)`, from `t67_k2` applied to `u = ρ f`. -/
theorem tc2_pos_log (hd : 1 ≤ d) (hρ : HRS.Whole.IsProbDensity ρ) {Mg : ℝ}
    (hk : TcKer (HRS.Whole.withDensityReal ρ) (t67K d) Mg) :
    TcPos (HRS.Whole.withDensityReal ρ) (t67K d) := by
  haveI := isProbabilityMeasure_nu hρ
  intro u hu hu2 hmean
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hu1 : Integrable u ν := hu2.integrable (by norm_num)
  have hfi : Integrable (fun x => ρ x * u x) := (tc2_integrable_nu hρ u).1 hu1
  have hmass : ∫ x, ρ x * u x = 0 := by rw [← tc2_integral_nu hρ u]; exact hmean
  have hI := tc2_pair_integrable hk hu hu hu2 hu2
  have habs : Integrable (fun p : Euc d × Euc d =>
      |t67K d p.1 p.2 * (ρ p.1 * u p.1) * (ρ p.2 * u p.2)|)
      ((volume : Measure (Euc d)).prod volume) := by
    have h1 : Integrable (fun p : Euc d × Euc d => |t67K d p.1 p.2 * u p.2 * u p.1|)
        (ν.prod ν) := hI.abs
    have hprod : ν.prod ν = ((volume : Measure (Euc d)).prod volume).withDensity
        (fun z => ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2)) := by
      rw [hν]
      unfold HRS.Whole.withDensityReal
      exact prod_withDensity hρ.measurable.ennreal_ofReal hρ.measurable.ennreal_ofReal
    have hmeasw : Measurable (fun z : Euc d × Euc d =>
        ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2)) :=
      (hρ.measurable.comp measurable_fst).ennreal_ofReal.mul
        (hρ.measurable.comp measurable_snd).ennreal_ofReal
    rw [hprod, integrable_withDensity_iff_integrable_smul' hmeasw
      (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (ae_of_all _ fun p => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ.nonneg _)]
    rw [show t67K d p.1 p.2 * (ρ p.1 * u p.1) * (ρ p.2 * u p.2) =
      (ρ p.1 * ρ p.2) * (t67K d p.1 p.2 * u p.2 * u p.1) by ring,
      abs_mul (ρ p.1 * ρ p.2) (t67K d p.1 p.2 * u p.2 * u p.1),
      abs_of_nonneg (mul_nonneg (hρ.nonneg _) (hρ.nonneg _))]
  have hnn := t67_k2 hd hfi habs hmass
  have hid : ∫ x, tc2_T ν (t67K d) u x * u x ∂ν =
      pairE (t67K d) (fun x => ρ x * u x) (fun x => ρ x * u x) := by
    rw [tc2_integral_nu hρ]
    unfold pairE
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e : ∀ y, t67K d x y * (ρ x * u x) * (ρ y * u y) =
        (ρ x * u x) * (ρ y * (t67K d x y * u y)) := fun y => by ring
    simp_rw [e]
    rw [integral_const_mul]
    unfold tc2_T
    rw [tc2_integral_nu hρ (fun y => t67K d x y * u y)]
    ring
  rw [hid]
  exact hnn

/-- For `f ∈ L²_0(μ)` measurable, `Kop g μ f` is the centered potential of `K̃` (`g = -log ‖·‖`). -/
theorem tc2_kop_log (hρ : HRS.Whole.IsProbDensity ρ) {Mg : ℝ}
    (hk : TcKer (HRS.Whole.withDensityReal ρ) (t67K d) Mg)
    (hl2 : MemLp (t67l : Euc d → ℝ) 2 (HRS.Whole.withDensityReal ρ)) {f : Euc d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 (HRS.Whole.withDensityReal ρ))
    (hmean : ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0) :
    HRS.Whole.Kop (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) f =ᵐ[HRS.Whole.withDensityReal ρ]
      fun x => tc2_T (HRS.Whole.withDensityReal ρ) (t67K d) f x -
        ∫ y, tc2_T (HRS.Whole.withDensityReal ρ) (t67K d) f y ∂(HRS.Whole.withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hf1 : Integrable f ν := hf2.integrable (by norm_num)
  have hlf : Integrable (fun y => t67l y * f y) ν := hl2.integrable_mul hf2
  set c1 : ℝ := (1 / 2) * ∫ y, t67l y * f y ∂ν with hc1
  have hG : ∀ᵐ x ∂ν, ∫ y, rieszKernel d 0 (x - y) * f y ∂ν = tc2_T ν (t67K d) f x - c1 := by
    filter_upwards [tc2_T_ae_integrable hk hf hf2] with x hx
    have e : ∀ y, rieszKernel d 0 (x - y) * f y =
        (t67K d x y * f y - ((1 / 2) * t67l x + (1 / 2) * Real.log 2) * f y) -
          (1 / 2) * (t67l y * f y) := fun y => by unfold t67K; ring
    have i1 : Integrable (fun y => t67K d x y * f y -
        ((1 / 2) * t67l x + (1 / 2) * Real.log 2) * f y) ν :=
      hx.sub (hf1.const_mul ((1 / 2) * t67l x + (1 / 2) * Real.log 2))
    have i2 : Integrable (fun y => (1 / 2 : ℝ) * (t67l y * f y)) ν := hlf.const_mul _
    simp_rw [e]
    rw [integral_sub i1 i2, integral_sub hx (hf1.const_mul _), integral_const_mul,
      integral_const_mul, hmean]
    unfold tc2_T
    ring
  have hT1 : Integrable (tc2_T ν (t67K d) f) ν :=
    (tc2_T_memLp hk hf hf2).1.integrable (by norm_num)
  have hint : ∫ x, (∫ y, rieszKernel d 0 (x - y) * f y ∂ν) ∂ν =
      ∫ x, tc2_T ν (t67K d) f x ∂ν - c1 := by
    rw [integral_congr_ae hG, integral_sub hT1 (integrable_const _), integral_const]
    simp
  filter_upwards [hG] with x hx
  simp only [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair]
  rw [hx, hint]
  ring

end PosKop

end HRS.MS.TcR

end
