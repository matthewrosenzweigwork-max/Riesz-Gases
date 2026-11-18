import HRS.Kernel.GradOp

/-!
# Fourier coefficients of the heat regularisations of `∇g` and of their convolutions

Auxiliary file of `HRS/Kernel/GradConv.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem coeffOf_eq_integral (φ : Torus d → ℝ) (k : Lattice d) :
    coeffOf φ k = ∫ x, Torus.mode (-k) x * (φ x : ℂ) := by
  unfold coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  rw [Torus.volume_eq_pi_haar]
  simp only [smul_eq_mul]
  rfl

theorem sinMode_eq (l : Lattice d) (z : Torus d) :
    ((Torus.sinMode l z : ℝ) : ℂ) = (Torus.mode l z - Torus.mode (-l) z) / (2 * Complex.I) := by
  rw [Torus.mode_neg]
  unfold Torus.sinMode
  rw [Complex.sub_conj]
  field_simp
  push_cast
  ring

/-- The coefficient of the `i`-th component of the heat regularisation. -/
def heatCoef (s ε : ℝ) (d : ℕ) (i : Fin d) (l : Lattice d) : ℝ :=
  -(rieszCoeff d s l * Real.exp (-ε * Lattice.enorm l ^ 2) * 2 * Real.pi) * ((l i : ℤ) : ℝ)

theorem heatRieszGrad_component (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (z : Torus d) (i : Fin d) :
    heatRieszGrad d s ε z i = ∑' l : Lattice d, heatCoef s ε d i l * Torus.sinMode l z := by
  rw [HRS.KernelAux.heatRieszGrad_apply hsd hε z i]
  refine tsum_congr fun l => ?_
  unfold heatCoef
  ring

theorem summable_heatCoef (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    Summable fun l : Lattice d => |heatCoef s ε d i l| := by
  refine Summable.of_nonneg_of_le (fun l => abs_nonneg _) (fun l => ?_)
    ((HRS.KernelAux.summable_pow_gauss_lattice d hε 1).mul_left (|rieszConst d s| * 2 * Real.pi))
  unfold heatCoef
  rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos Real.pi_pos]
  have h1 := HRS.KernelAux.abs_rieszCoeff_le d s hsd l
  have h2 := HRS.KernelAux.abs_coord_le_enorm l i
  have : 0 ≤ Lattice.enorm l := norm_nonneg _
  rw [pow_one, abs_two]
  calc |rieszCoeff d s l| * Real.exp (-ε * Lattice.enorm l ^ 2) * 2 * Real.pi *
        |((l i : ℤ) : ℝ)| ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm l ^ 2) * 2 * Real.pi *
        Lattice.enorm l := by gcongr
    _ = _ := by ring

theorem heatCoef_neg (i : Fin d) (l : Lattice d) (ε : ℝ) :
    heatCoef s ε d i (-l) = - heatCoef s ε d i l := by
  unfold heatCoef
  rw [HRS.rieszCoeff_neg, HRS.enorm_neg]
  simp


theorem integral_mode_sin (k l : Lattice d) :
    ∫ z : Torus d, Torus.mode (-k) z * ((Torus.sinMode l z : ℝ) : ℂ) =
      ((if l = k then 1 else 0) - (if l = -k then 1 else 0)) / (2 * Complex.I) := by
  have e : ∀ z : Torus d, Torus.mode (-k) z * ((Torus.sinMode l z : ℝ) : ℂ) =
      (Torus.mode (-k) z * Torus.mode l z - Torus.mode (-k) z * Torus.mode (-l) z) / (2 * Complex.I) := by
    intro z; rw [sinMode_eq]; ring
  simp_rw [e]
  rw [integral_div, integral_sub (Torus.integrable_mode_mul _ _) (Torus.integrable_mode_mul _ _),
    Torus.integral_mode_mul, Torus.integral_mode_mul]
  congr 2
  · have : (-k + l = 0) ↔ (l = k) := by rw [neg_add_eq_zero]; exact eq_comm
    simp only [this]
  · have : (-k + -l = 0) ↔ (l = -k) := by
      constructor
      · intro h; have := neg_eq_zero.mp (by rw [← neg_add] at h; exact h : -(k + l) = 0)
        exact eq_neg_of_add_eq_zero_right this
      · intro h; rw [h]; simp
    simp only [this]


theorem integral_mode_heat_component (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) (i : Fin d) :
    ∫ z : Torus d, Torus.mode (-k) z * ((heatRieszGrad d s ε z i : ℝ) : ℂ) =
      (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
        ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
  set F : Lattice d → Torus d → ℂ := fun l z =>
    Torus.mode (-k) z * ((heatCoef s ε d i l * Torus.sinMode l z : ℝ) : ℂ) with hF
  have hpt : ∀ z : Torus d, Torus.mode (-k) z * ((heatRieszGrad d s ε z i : ℝ) : ℂ) = ∑' l, F l z := by
    intro z
    rw [heatRieszGrad_component hsd hε z i, Complex.ofReal_tsum, ← tsum_mul_left]
  simp_rw [hpt]
  have hcont : ∀ l, Continuous (F l) := fun l => by
    have := Torus.continuous_mode (d := d) (-k)
    have h2 := Torus.continuous_sinMode (d := d) l
    simp only [hF]
    fun_prop
  have hint : ∀ l, Integrable (F l) := fun l =>
    (hcont l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ l z, ‖F l z‖ ≤ |heatCoef s ε d i l| := by
    intro l z
    simp only [hF, norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have := Torus.norm_sinMode_le l z
    rw [Real.norm_eq_abs] at this
    calc |heatCoef s ε d i l| * |Torus.sinMode l z| ≤ |heatCoef s ε d i l| * 1 := by gcongr
      _ = _ := mul_one _
  have hsum : Summable fun l => ∫ z, ‖F l z‖ := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun z => norm_nonneg _) (fun l => ?_)
      (summable_heatCoef hsd hε i)
    calc ∫ z, ‖F l z‖ ≤ ∫ _z : Torus d, |heatCoef s ε d i l| :=
          integral_mono (hint l).norm (integrable_const _) (hnorm l)
      _ = |heatCoef s ε d i l| := by simp
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hl : ∀ l, ∫ z, F l z = ((heatCoef s ε d i l : ℝ) : ℂ) *
      (((if l = k then 1 else 0) - (if l = -k then 1 else 0)) / (2 * Complex.I)) := by
    intro l
    have : ∀ z, F l z = ((heatCoef s ε d i l : ℝ) : ℂ) *
        (Torus.mode (-k) z * ((Torus.sinMode l z : ℝ) : ℂ)) := by
      intro z; simp only [hF]; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, integral_mode_sin]
  simp_rw [hl]
  have h1 : HasSum (fun l : Lattice d => ((heatCoef s ε d i l : ℝ) : ℂ) *
      (((if l = k then 1 else 0) - (if l = -k then 1 else 0)) / (2 * Complex.I)))
      ((((heatCoef s ε d i k : ℝ) : ℂ) - ((heatCoef s ε d i (-k) : ℝ) : ℂ)) / (2 * Complex.I)) := by
    have e1 : HasSum (fun l : Lattice d => ((heatCoef s ε d i l : ℝ) : ℂ) *
        (if l = k then 1 else 0) / (2 * Complex.I))
        (((heatCoef s ε d i k : ℝ) : ℂ) / (2 * Complex.I)) := by
      convert hasSum_ite_eq k (((heatCoef s ε d i k : ℝ) : ℂ) / (2 * Complex.I)) using 1
      funext l
      by_cases h : l = k
      · subst h; simp
      · simp [h]
    have e2 : HasSum (fun l : Lattice d => ((heatCoef s ε d i l : ℝ) : ℂ) *
        (if l = -k then 1 else 0) / (2 * Complex.I))
        (((heatCoef s ε d i (-k) : ℝ) : ℂ) / (2 * Complex.I)) := by
      convert hasSum_ite_eq (-k) (((heatCoef s ε d i (-k) : ℝ) : ℂ) / (2 * Complex.I)) using 1
      funext l
      by_cases h : l = -k
      · subst h; simp
      · simp [h]
    convert e1.sub e2 using 1
    · funext l
      ring
    · ring
  rw [h1.tsum_eq, heatCoef_neg]
  unfold heatCoef
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring


theorem mode_add_arg (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x + y) = Torus.mode k x * Torus.mode k y := by
  obtain ⟨a, rfl, -⟩ := exists_mk_box x
  obtain ⟨b, rfl, -⟩ := exists_mk_box y
  rw [← mk_add, Torus.mode_mk, Torus.mode_mk, Torus.mode_mk, ← Complex.exp_add]
  congr 1
  have : Lattice.dot k (a + b) = Lattice.dot k a + Lattice.dot k b := by
    simp [Lattice.dot, mul_add, Finset.sum_add_distrib]
  rw [this]
  push_cast
  ring

/-- Fourier coefficient of a plain convolution with a continuous kernel. -/
theorem coeff_plain_conv {h g : Torus d → ℝ} (hh : Continuous h) (hg : Continuous g) (k : Lattice d) :
    ∫ x, Torus.mode (-k) x * ((∫ y, h y * g (x - y) : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) * (∫ z, Torus.mode (-k) z * (g z : ℂ)) := by
  have hmode : Continuous (Torus.mode (-k) : Torus d → ℂ) := Torus.continuous_mode _
  have e1 : ∀ x : Torus d, Torus.mode (-k) x * ((∫ y, h y * g (x - y) : ℝ) : ℂ) =
      ∫ y, Torus.mode (-k) x * ((h y * g (x - y) : ℝ) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal]
  simp_rw [e1]
  have hcont : Continuous (fun p : Torus d × Torus d => Torus.mode (-k) p.1 * ((h p.2 * g (p.1 - p.2) : ℝ) : ℂ)) := by
    have : Continuous fun p : Torus d × Torus d => g (p.1 - p.2) :=
      hg.comp (continuous_fst.sub continuous_snd)
    have h2 : Continuous fun p : Torus d × Torus d => (h p.2 * g (p.1 - p.2) : ℝ) :=
      (hh.comp continuous_snd).mul this
    exact (hmode.comp continuous_fst).mul (Complex.continuous_ofReal.comp h2)
  have hint : Integrable (Function.uncurry fun x y : Torus d => Torus.mode (-k) x * ((h y * g (x - y) : ℝ) : ℂ))
      (volume.prod volume) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hint]
  have e2 : ∀ y : Torus d, ∫ x, Torus.mode (-k) x * ((h y * g (x - y) : ℝ) : ℂ) =
      Torus.mode (-k) y * (h y : ℂ) * ∫ z, Torus.mode (-k) z * (g z : ℂ) := by
    intro y
    rw [← integral_add_right_eq_self (fun x : Torus d => Torus.mode (-k) x * ((h y * g (x - y) : ℝ) : ℂ)) y]
    simp only [add_sub_cancel_right, mode_add_arg]
    have : ∀ z : Torus d, Torus.mode (-k) z * Torus.mode (-k) y * ((h y * g z : ℝ) : ℂ) =
        (Torus.mode (-k) y * (h y : ℂ)) * (Torus.mode (-k) z * (g z : ℂ)) := by
      intro z; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul]
  simp_rw [e2]
  rw [integral_mul_const]


theorem continuous_heatRieszGrad_apply (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    Continuous fun z : Torus d => heatRieszGrad d s ε z i :=
  (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp (continuous_heatRieszGrad hsd hε)

theorem convGradConv_heat_apply {C : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (hG : GoodKernel d s C (heatRieszGrad d s ε)) {h : Torus d → ℝ} (hh : Continuous h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) (x : Torus d) (i : Fin d) :
    convGradConv (heatRieszGrad d s ε) h x i = ∫ y, h y * heatRieszGrad d s ε (x - y) i := by
  have hGc := continuous_heatRieszGrad hsd hε
  have hGi : Integrable (heatRieszGrad d s ε : Torus d → Euc d) :=
    hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hG.eq_plain_of_integrable hGi hh.measurable hB x]
  have hint : Integrable (fun y : Torus d => h y • heatRieszGrad d s ε (x - y)) :=
    (hh.smul (hGc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
  simpa using this.symm

/-- The Fourier coefficients of the convolution with the heat regularisation. -/
theorem coeff_convGradConv_heat {C : ℝ} (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (hG : GoodKernel d s C (heatRieszGrad d s ε)) {h : Torus d → ℝ} (hh : Continuous h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
          ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ)) := by
  simp_rw [convGradConv_heat_apply hsd hε hG hh hB]
  rw [coeff_plain_conv hh (continuous_heatRieszGrad_apply hsd hε i), integral_mode_heat_component hsd hε]


theorem goodKernel_heat (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → GoodKernel d s C (heatRieszGrad d s ε) := by
  obtain ⟨C, hC⟩ := heatRieszGrad_bound hd hs0 hsd
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  refine ⟨by omega, hs0, hsd, le_max_right _ _, (continuous_heatRieszGrad hsd hε).measurable,
    heatRieszGrad_neg ε, fun z hz => (hC ε hε z hz).trans ?_⟩
  have : 0 ≤ tdist z 0 ^ (-s - 1) + 1 := by
    have := Real.rpow_nonneg (tdist_nonneg z 0) (-s - 1)
    linarith
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) this

/-- The cancellation convolutions with the heat regularisations converge pointwise. -/
theorem tendsto_convGradConv_heat {C : ℝ} (hsd : s < d)
    (hGε : ∀ ε : ℝ, 0 < ε → GoodKernel d s C (heatRieszGrad d s ε)) {h : Torus d → ℝ} (hh : Continuous h) {B L : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (x : Torus d) :
    Tendsto (fun ε => convGradConv (heatRieszGrad d s ε) h x) (𝓝[>] 0)
      (𝓝 (convGradConv (periodicRieszGrad d s) h x)) := by
  simp_rw [convGradConv_eq_integral_kern]
  refine tendsto_integral_filter_of_dominated_convergence (dom s C L B d) ?_ ?_ (integrable_dom (hGε 1 one_pos) L B) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (measurable_kern (hGε ε hε) hh.measurable x).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact kern_bound_ae (hGε ε hε) hB hL hL0 hB0 x
  · refine Eventually.of_forall fun z => ?_
    unfold kern
    split_ifs
    · exact ((heat_tendsto hsd z).const_smul _)
    · exact ((heat_tendsto hsd z).const_smul _)


/-- The Fourier coefficients of `∇g * h` (cancellation convention) for a Lipschitz function `h`. -/
theorem coeff_convGradConv_lip (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hcont : Continuous h) {B L : ℝ} (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hGε⟩ := goodKernel_heat hd hs0 hsd
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- the left side converges
  have hLHS : Tendsto (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) l
      (𝓝 (∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hc := (hGε ε hε).continuous_op hcont hB hL hL0 hB0
      have : Continuous fun x : Torus d => Torus.mode (-k) x *
          ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ) :=
        (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hc))
      exact this.aestronglyMeasurable
    · refine ⟨L * opM1 d s C + B * opM2 s C, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans ?_ ((hGε ε hε).bound_op h B L hcont.measurable hB hL hL0 hB0 x)
      have := PiLp.norm_apply_le (convGradConv (heatRieszGrad d s ε) h x) i
      simpa using this
    · refine Eventually.of_forall fun x => ?_
      have := tendsto_convGradConv_heat hsd hGε hcont hB hL hL0 hB0 x
      have h2 := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp this
      exact (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h2))
  set R : ℝ → ℂ := fun ε => (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
    ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
      ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ)) with hR
  have hRc : Continuous R := by
    simp only [hR]
    fun_prop
  have hRHS : Tendsto R l (𝓝 ((∫ y, Torus.mode (-k) y * (h y : ℂ)) *
      ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)))) := by
    have := (hRc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hR] using this
  have hEq : (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) =ᶠ[l] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact coeff_convGradConv_heat hsd hε (hGε ε hε) hcont hB k i
  exact tendsto_nhds_unique (hLHS.congr' hEq) hRHS

/-- The Fourier coefficients of `∇g * h` (cancellation convention) for a `C¹` function `h`. -/
theorem coeff_convGradConv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hh : Torus.IsCk 1 h) (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) := by
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh
  exact coeff_convGradConv_lip hd hs0 hsd (isCk_continuous hh) hB hL hL0 hB0 k i

end HRS.KernelGrad
