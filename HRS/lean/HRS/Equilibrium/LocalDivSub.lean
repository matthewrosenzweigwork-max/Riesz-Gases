import HRS.Equilibrium.LocalDivAsym
open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

theorem integrable_mu_iff {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {g : Torus d → ℝ} :
    Integrable g (withDensityReal ρ) ↔ Integrable (fun y => ρ y * g y) (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.density.measurable)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.density.nonneg y)]

theorem integrable_torus_of_cube {G : Torus d → ℝ} (hG : Measurable G) (x : Torus d)
    (h : IntegrableOn (fun w : Euc d => G (x + Torus.mk w)) (cube d)) :
    Integrable G (volume : Measure (Torus d)) := by
  have hG' : Measurable fun z : Torus d => G (x + z) := hG.comp (measurable_const_add x)
  have h1 : Integrable (fun z : Torus d => G (x + z)) (volume : Measure (Torus d)) := by
    have hmp := mk_measurePreserving (d := d)
    rw [← hmp.map_eq]
    rw [integrable_map_measure hG'.aestronglyMeasurable hmp.measurable.aemeasurable]
    exact h
  have := h1.comp_add_left (-x)
  simpa using this


theorem measurable_slice {h : Torus d → Torus d → ℝ}
    (hm : Measurable fun p : Torus d × Torus d => h p.1 p.2) (x : Torus d) :
    Measurable fun y => h x y := by
  have e : (fun y => h x y) = (fun p : Torus d × Torus d => h p.1 p.2) ∘ (fun y : Torus d => (x, y)) :=
    rfl
  rw [e]
  exact hm.comp (Measurable.prodMk measurable_const measurable_id)

theorem kernel_int {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {Rm : ℝ} (hRm : ∀ y, ρ y ≤ Rm)
    {h : Torus d → Torus d → ℝ} (hm : Measurable fun p : Torus d × Torus d => h p.1 p.2)
    {g : ℝ → ℝ} (hbd : ∀ x y, |h x y| ≤ g (Torus.eucDist x y))
    (hgi : IntegrableOn (fun w : Euc d => g ‖w‖) (cube d)) (x : Torus d) :
    Integrable (fun y => h x y) (withDensityReal ρ) ∧
      |∫ y, h x y ∂(withDensityReal ρ)| ≤ Rm * ∫ w in cube d, g ‖w‖ := by
  have hhx := measurable_slice hm x
  have hGm : Measurable fun y => ρ y * h x y := hρ.density.measurable.mul hhx
  have hGw : ∀ w ∈ cube d, |ρ (x + Torus.mk w) * h x (x + Torus.mk w)| ≤ Rm * g ‖w‖ := by
    intro w hw
    rw [abs_mul, abs_of_nonneg (hρ.density.nonneg _)]
    have h1 := hbd x (x + Torus.mk w)
    rw [eucDist_shift, eucDist_mk_zero hw] at h1
    exact mul_le_mul (hRm _) h1 (abs_nonneg _) ((hρ.density.nonneg x).trans (hRm x))
  have hmeas : Measurable fun w : Euc d => ρ (x + Torus.mk w) * h x (x + Torus.mk w) :=
    (hGm.comp (measurable_shift_mk x))
  have hGi : IntegrableOn (fun w : Euc d => ρ (x + Torus.mk w) * h x (x + Torus.mk w)) (cube d) :=
    Integrable.mono' (hgi.const_mul Rm) hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_cube).2
        (Filter.Eventually.of_forall fun w hw => by rw [Real.norm_eq_abs]; exact hGw w hw))
  have hGint := integrable_torus_of_cube hGm x hGi
  refine ⟨(integrable_mu_iff hρ).2 hGint, ?_⟩
  rw [integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg,
    integral_shift_cube x _ hGm, ← Real.norm_eq_abs]
  calc ‖∫ w in cube d, ρ (x + Torus.mk w) * h x (x + Torus.mk w)‖
      ≤ ∫ w in cube d, Rm * g ‖w‖ :=
        norm_integral_le_of_norm_le (hgi.const_mul Rm)
          ((ae_restrict_iff' measurableSet_cube).2
            (Filter.Eventually.of_forall fun w hw => by rw [Real.norm_eq_abs]; exact hGw w hw))
    _ = _ := integral_const_mul _ _


theorem measurable_eucDist_slice (x : Torus d) : Measurable fun y : Torus d => Torus.eucDist x y := by
  have e : (fun y : Torus d => Torus.eucDist x y) =
      (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) ∘ (fun y : Torus d => (x, y)) := rfl
  rw [e]
  exact measurable_eucDist.comp (Measurable.prodMk measurable_const measurable_id)

theorem lintegral_torus_cube (f : Torus d → ENNReal) (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ w in cube d, f (Torus.mk w) := by
  have hmp := mk_measurePreserving (d := d)
  rw [← hmp.map_eq]
  exact lintegral_map hf hmp.measurable

theorem L2_bound {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {Rm : ℝ} (hRm : ∀ y, ρ y ≤ Rm)
    {h : Torus d → Torus d → ℝ} (hm : Measurable fun p : Torus d × Torus d => h p.1 p.2)
    {g : ℝ → ℝ} (hg : Measurable g) (hbd : ∀ x y, |h x y| ≤ g (Torus.eucDist x y))
    (hgi : IntegrableOn (fun w : Euc d => g ‖w‖ ^ 2) (cube d)) :
    eLpNorm (fun p : Torus d × Torus d => h p.1 p.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ)) ≤
      ENNReal.ofReal (Real.sqrt (Rm * ∫ w in cube d, g ‖w‖ ^ 2)) := by
  have hprob := isProb_withDensityReal hρ.density
  have hRm0 : 0 ≤ Rm := (hρ.density.nonneg (Classical.arbitrary _)).trans (hRm _)
  set Θ : ℝ := ∫ w in cube d, g ‖w‖ ^ 2 with hΘ
  have hΘ0 : 0 ≤ Θ := setIntegral_nonneg measurableSet_cube fun w _ => sq_nonneg _
  -- pointwise bound on the lintegral in y
  have hinner : ∀ x : Torus d, ∫⁻ y, ‖h x y‖ₑ ^ (2 : ℝ) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Rm * Θ) := by
    intro x
    have hF : Measurable fun y : Torus d => ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) := by
      exact ENNReal.measurable_ofReal.comp ((hg.comp (measurable_eucDist_slice x)).pow_const 2)
    calc ∫⁻ y, ‖h x y‖ₑ ^ (2 : ℝ) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hbd x y) 2)
      _ = ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) := by
          unfold withDensityReal
          rw [lintegral_withDensity_eq_lintegral_mul (volume : Measure (Torus d))
            (f := fun x => ENNReal.ofReal (ρ x))
            (ENNReal.measurable_ofReal.comp hρ.density.measurable) hF]
          rfl
      _ ≤ ∫⁻ y, ENNReal.ofReal Rm * ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) :=
          lintegral_mono fun y => mul_le_mul' (ENNReal.ofReal_le_ofReal (hRm y)) le_rfl
      _ = ENNReal.ofReal Rm * ∫⁻ y, ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) :=
          lintegral_const_mul _ hF
      _ = ENNReal.ofReal Rm * ∫⁻ w in cube d, ENNReal.ofReal (g ‖w‖ ^ 2) := by
          congr 1
          have h1 : ∫⁻ y, ENNReal.ofReal (g (Torus.eucDist x y) ^ 2) =
              ∫⁻ z, ENNReal.ofReal (g (Torus.eucDist x (x + z)) ^ 2) :=
            (lintegral_add_left_eq_self (μ := (volume : Measure (Torus d)))
              (fun y => ENNReal.ofReal (g (Torus.eucDist x y) ^ 2)) x).symm
          rw [h1, lintegral_torus_cube]
          · refine setLIntegral_congr_fun measurableSet_cube fun w hw => ?_
            simp only [eucDist_shift, eucDist_mk_zero hw]
          · exact ENNReal.measurable_ofReal.comp
              ((hg.comp ((measurable_eucDist_slice x).comp (measurable_const_add x))).pow_const 2)
      _ = ENNReal.ofReal Rm * ENNReal.ofReal Θ := by
          congr 1
          rw [hΘ]
          exact (ofReal_integral_eq_lintegral_ofReal hgi
            (Filter.Eventually.of_forall fun w => sq_nonneg _)).symm
      _ = _ := (ENNReal.ofReal_mul hRm0).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  have hmeas : Measurable fun p : Torus d × Torus d => ‖h p.1 p.2‖ₑ ^ (2 : ℝ) :=
    (hm.enorm).pow_const _
  have hK : ∫⁻ p : Torus d × Torus d, ‖h p.1 p.2‖ₑ ^ (2 : ℝ)
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) ≤ ENNReal.ofReal (Rm * Θ) := by
    rw [lintegral_prod _ hmeas.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ‖h x y‖ₑ ^ (2 : ℝ) ∂(withDensityReal ρ) ∂(withDensityReal ρ)
        ≤ ∫⁻ x, ENNReal.ofReal (Rm * Θ) ∂(withDensityReal ρ) := lintegral_mono hinner
      _ = ENNReal.ofReal (Rm * Θ) := by simp
  have e2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [e2]
  calc (∫⁻ p : Torus d × Torus d, ‖h p.1 p.2‖ₑ ^ (2 : ℝ)
        ∂((withDensityReal ρ).prod (withDensityReal ρ))) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (Rm * Θ)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hK (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (Rm * Θ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]


theorem theta_tendsto (hd : 1 ≤ d) {a : ℝ} (ha : a < d) :
    Tendsto (fun ε : ℝ => ∫ w in cube d, (if ‖w‖ ≤ ε then ‖w‖ ^ (-a) else (0 : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nontrivial (Euc d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hint := integrableOn_cube_rpow hd ha
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Euc d)).restrict (cube d)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε w => if ‖w‖ ≤ ε then ‖w‖ ^ (-a) else (0 : ℝ)) (f := fun _ => (0 : ℝ))
    (bound := fun w => ‖w‖ ^ (-a)) ?_ ?_ hint ?_
  · simpa using h
  · refine Filter.Eventually.of_forall fun ε => ?_
    refine (Measurable.ite (measurableSet_le measurable_norm measurable_const)
      (measurable_norm.pow_const _) measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ε => ?_
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · simp only [abs_zero]; exact Real.rpow_nonneg (norm_nonneg _) _
  · have h0 : ∀ᵐ w ∂(volume : Measure (Euc d)), w ∉ ({0} : Set (Euc d)) :=
      (Set.countable_singleton (0 : Euc d)).ae_notMem _
    filter_upwards [ae_restrict_of_ae h0] with w hw
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (by simpa using hw)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hw0] with ε hε
    rw [if_neg (not_le.2 hε.2)]


theorem eucDist_eq_zero {x y : Torus d} (h : Torus.eucDist x y = 0) : x = y := by
  unfold Torus.eucDist at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i - y i‖)).1 h i (Finset.mem_univ i)
  have h2 : ‖x i - y i‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 h2)

theorem hT_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Torus d, |hTransport d s φ x y| ≤ B * Torus.eucDist x y ^ (-s) := by
  obtain ⟨B, hB0, hB⟩ := h_bound_torus hd hs0 hsd hφ
  refine ⟨B, hB0, fun x y => ?_⟩
  rcases (show 0 ≤ Torus.eucDist x y from Real.sqrt_nonneg _).lt_or_eq with h | h
  · exact hB x y h
  · have := eucDist_eq_zero h.symm
    subst this
    simp only [hTransport_self, abs_zero]
    exact mul_nonneg hB0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- the cutoff tail kernel -/
def kTail (d : ℕ) (s : ℝ) (f : Torus d → ℝ) (ε : ℝ) (x y : Torus d) : ℝ :=
  if Torus.eucDist x y ≤ ε then hTransport d s f x y else 0

theorem hC_eq_sub (s : ℝ) (f : Torus d → ℝ) (ε : ℝ) (x y : Torus d) :
    hC d s f ε x y = hTransport d s f x y - kTail d s f ε x y := by
  unfold hC kTail
  by_cases h : ε < Torus.eucDist x y
  · rw [if_pos h, if_neg (not_le.2 h)]; ring
  · rw [if_neg h, if_pos (not_lt.1 h)]; ring

theorem measurable_kTail {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (ε : ℝ) :
    Measurable (fun p : Torus d × Torus d => kTail d s f ε p.1 p.2) :=
  Measurable.ite (measurableSet_le measurable_eucDist measurable_const)
    (measurable_hTransport hsd hf) measurable_const

theorem kTail_symm {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (ε : ℝ)
    (x y : Torus d) : kTail d s f ε x y = kTail d s f ε y x := by
  unfold kTail
  rw [eucDist_symm x y, hTransport_symm hsd hf x y]

theorem cc_diff {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {Rm : ℝ} (hRm : ∀ y, ρ y ≤ Rm)
    {h k : Torus d → Torus d → ℝ} (hm : Measurable fun p : Torus d × Torus d => h p.1 p.2)
    (km : Measurable fun p : Torus d × Torus d => k p.1 p.2)
    (hs : ∀ x y, h x y = h y x) (ks : ∀ x y, k x y = k y x)
    {gh gk : ℝ → ℝ} (hbdh : ∀ x y, |h x y| ≤ gh (Torus.eucDist x y))
    (hbdk : ∀ x y, |k x y| ≤ gk (Torus.eucDist x y))
    (hghi : IntegrableOn (fun w : Euc d => gh ‖w‖) (cube d))
    (hgki : IntegrableOn (fun w : Euc d => gk ‖w‖) (cube d)) (x y : Torus d) :
    canonicalCenter (withDensityReal ρ) (fun x y => h x y - k x y) x y -
        canonicalCenter (withDensityReal ρ) h x y =
      -k x y + (∫ y', k x y' ∂(withDensityReal ρ)) + (∫ y', k y y' ∂(withDensityReal ρ)) -
        ∫ x', ∫ y', k x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  have hprob := isProb_withDensityReal hρ.density
  have ih := fun x => kernel_int hρ hRm hm hbdh hghi x
  have ik := fun x => kernel_int hρ hRm km hbdk hgki x
  have hAh : Measurable fun x => ∫ y', h x y' ∂(withDensityReal ρ) :=
    (hm.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  have hAk : Measurable fun x => ∫ y', k x y' ∂(withDensityReal ρ) :=
    (km.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  have iAh : Integrable (fun x => ∫ y', h x y' ∂(withDensityReal ρ)) (withDensityReal ρ) :=
    Integrable.of_bound hAh.aestronglyMeasurable (Rm * ∫ w in cube d, gh ‖w‖)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (ih x).2)
  have iAk : Integrable (fun x => ∫ y', k x y' ∂(withDensityReal ρ)) (withDensityReal ρ) :=
    Integrable.of_bound hAk.aestronglyMeasurable (Rm * ∫ w in cube d, gk ‖w‖)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (ik x).2)
  have e1 : ∀ x, ∫ y', (h x y' - k x y') ∂(withDensityReal ρ) =
      (∫ y', h x y' ∂(withDensityReal ρ)) - ∫ y', k x y' ∂(withDensityReal ρ) :=
    fun x => integral_sub (ih x).1 (ik x).1
  have e2 : ∀ (g : Torus d → Torus d → ℝ), (∀ x y, g x y = g y x) → ∀ y,
      ∫ x', g x' y ∂(withDensityReal ρ) = ∫ y', g y y' ∂(withDensityReal ρ) := by
    intro g hg y
    exact integral_congr_ae (Filter.Eventually.of_forall fun x' => hg x' y)
  have e3 : ∀ y, ∫ x', (h x' y - k x' y) ∂(withDensityReal ρ) =
      (∫ y', h y y' ∂(withDensityReal ρ)) - ∫ y', k y y' ∂(withDensityReal ρ) := by
    intro y
    have : ∀ x', h x' y - k x' y = h y x' - k y x' := fun x' => by rw [hs x' y, ks x' y]
    simp_rw [this]
    exact integral_sub (ih y).1 (ik y).1
  simp only [canonicalCenter]
  rw [e1 x, e3 y, e2 h hs y]
  have e4 : ∫ x', ∫ y', (h x' y' - k x' y') ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
      (∫ x', ∫ y', h x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ)) -
        ∫ x', ∫ y', k x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    simp_rw [e1]
    exact integral_sub iAh iAk
  rw [e4]
  ring


section Sub
variable {s : ℝ} {ρ φ : Torus d → ℝ}

theorem gT_sq {B t : ℝ} (ht : 0 ≤ t) (s : ℝ) : (B * t ^ (-s)) ^ 2 = B ^ 2 * t ^ (-(2 * s)) := by
  rw [mul_pow, ← Real.rpow_natCast (t ^ (-s)) 2, ← Real.rpow_mul ht]
  congr 2; push_cast; ring

theorem sub_setup (hρ : SmoothPosDensity ρ) :
    ∃ Rm : ℝ, 0 ≤ Rm ∧ ∀ y, ρ y ≤ Rm := by
  obtain ⟨Rm, hRm⟩ := isCompact_univ.exists_bound_of_continuousOn
    (PoleCavityAux.continuous_of_smoothPos hρ).continuousOn
  refine ⟨Rm, (norm_nonneg _).trans (hRm (Classical.arbitrary _) (mem_univ _)), fun y => ?_⟩
  have := hRm y (mem_univ y)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

theorem sub_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    MemLp (fun p : Torus d × Torus d => hTransport d s φ p.1 p.2) 2
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨B, hB0, hB⟩ := hT_bound hd hs0 hsd hφ
  obtain ⟨Rm, hRm0, hRm⟩ := sub_setup hρ
  have hint2 : IntegrableOn (fun w : Euc d => (B * ‖w‖ ^ (-s)) ^ 2) (cube d) := by
    have this : IntegrableOn (fun w : Euc d => B ^ 2 * ‖w‖ ^ (-(2 * s))) (cube d) :=
      (integrableOn_cube_rpow (d := d) (by omega) (a := 2 * s) (by linarith)).const_mul (B ^ 2)
    refine this.congr_fun (fun w _ => ?_) measurableSet_cube
    simp only
    rw [gT_sq (norm_nonneg _)]
  have hL2 := L2_bound hρ hRm (measurable_hTransport hsd hφ)
    (g := fun t => B * t ^ (-s)) ((measurable_id.pow_const _).const_mul B) hB hint2
  exact lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top


/-- cutoff radial integral over the cube -/
def Th (d : ℕ) (a ε : ℝ) : ℝ := ∫ w in cube d, (if ‖w‖ ≤ ε then ‖w‖ ^ (-a) else (0 : ℝ))

theorem Th_nonneg (a ε : ℝ) : 0 ≤ Th d a ε :=
  setIntegral_nonneg measurableSet_cube fun w _ => by
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl

theorem sub_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) {B Rm : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x y : Torus d, |hTransport d s φ x y| ≤ B * Torus.eucDist x y ^ (-s))
    (hRm0 : 0 ≤ Rm) (hRm : ∀ y, ρ y ≤ Rm) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun p : Torus d × Torus d =>
        canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 -
          canonicalCenter (withDensityReal ρ) (hTransport d s φ) p.1 p.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ)) ≤
      ENNReal.ofReal (Real.sqrt (Rm * (B ^ 2 * Th d (2 * s) ε))) +
        (ENNReal.ofReal (Rm * (B * Th d s ε)) + ENNReal.ofReal (Rm * (B * Th d s ε)) +
          ENNReal.ofReal (Rm * (B * Th d s ε))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hprob := isProb_withDensityReal hρ.density
  set μ := withDensityReal ρ with hμ
  set k := kTail d s φ ε with hk
  set gk : ℝ → ℝ := fun t => if t ≤ ε then B * t ^ (-s) else 0 with hgk
  have hbdh : ∀ x y, |hTransport d s φ x y| ≤ (fun t => B * t ^ (-s)) (Torus.eucDist x y) := hB
  have hbdk : ∀ x y, |k x y| ≤ gk (Torus.eucDist x y) := by
    intro x y
    simp only [hk, kTail, hgk]
    split_ifs with h
    · exact hB x y
    · simp
  have hgTi : IntegrableOn (fun w : Euc d => B * ‖w‖ ^ (-s)) (cube d) :=
    (integrableOn_cube_rpow (d := d) (by omega) hsd).const_mul B
  have hgki : IntegrableOn (fun w : Euc d => gk ‖w‖) (cube d) := by
    refine Integrable.mono' hgTi ?_ ((ae_restrict_iff' measurableSet_cube).2
      (Filter.Eventually.of_forall fun w _ => ?_))
    · exact (Measurable.ite (measurableSet_le measurable_norm measurable_const)
        ((measurable_norm.pow_const _).const_mul B) measurable_const).aestronglyMeasurable
    · simp only [hgk, Real.norm_eq_abs]
      split_ifs with h
      · rw [abs_of_nonneg (mul_nonneg hB0 (Real.rpow_nonneg (norm_nonneg _) _))]
      · simp only [abs_zero]; exact mul_nonneg hB0 (Real.rpow_nonneg (norm_nonneg _) _)
  have hgTi2 : IntegrableOn (fun w : Euc d => (B * ‖w‖ ^ (-s)) ^ 2) (cube d) := by
    have this : IntegrableOn (fun w : Euc d => B ^ 2 * ‖w‖ ^ (-(2 * s))) (cube d) :=
      (integrableOn_cube_rpow (d := d) (by omega) (a := 2 * s) (by linarith)).const_mul (B ^ 2)
    refine this.congr_fun (fun w _ => ?_) measurableSet_cube
    simp only
    rw [gT_sq (norm_nonneg _)]
  have hgki2 : IntegrableOn (fun w : Euc d => gk ‖w‖ ^ 2) (cube d) := by
    refine Integrable.mono' hgTi2 ?_ ((ae_restrict_iff' measurableSet_cube).2
      (Filter.Eventually.of_forall fun w _ => ?_))
    · exact ((Measurable.ite (measurableSet_le measurable_norm measurable_const)
        ((measurable_norm.pow_const _).const_mul B) measurable_const).pow_const 2).aestronglyMeasurable
    · simp only [hgk, Real.norm_eq_abs]
      split_ifs with h
      · rw [abs_of_nonneg (sq_nonneg _)]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, abs_zero]
        exact sq_nonneg _
  have hgkm : Measurable gk :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      ((measurable_id.pow_const _).const_mul B) measurable_const
  -- the integrals of gk
  have hI1 : ∫ w in cube d, gk ‖w‖ = B * Th d s ε := by
    unfold Th
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_cube fun w _ => ?_
    simp only [hgk]
    split_ifs <;> simp
  have hI2 : ∫ w in cube d, gk ‖w‖ ^ 2 = B ^ 2 * Th d (2 * s) ε := by
    unfold Th
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_cube fun w _ => ?_
    simp only [hgk]
    split_ifs
    · exact gT_sq (norm_nonneg _) s
    · simp
  -- identity
  have hTm := measurable_hTransport hsd hφ
  have hkm := measurable_kTail hsd hφ ε
  have hid : ∀ x y, canonicalCenter μ (hC d s φ ε) x y - canonicalCenter μ (hTransport d s φ) x y =
      -k x y + (∫ y', k x y' ∂μ) + (∫ y', k y y' ∂μ) - ∫ x', ∫ y', k x' y' ∂μ ∂μ := by
    intro x y
    have hfun : hC d s φ ε = fun x y => hTransport d s φ x y - k x y := by
      funext x y; exact hC_eq_sub s φ ε x y
    rw [hfun]
    exact cc_diff hρ hRm hTm hkm (hTransport_symm hsd hφ) (kTail_symm hsd hφ ε)
      (gh := fun t => B * t ^ (-s)) (gk := gk) hbdh hbdk hgTi hgki x y
  set A : Torus d → ℝ := fun x => ∫ y', k x y' ∂μ with hA
  set c : ℝ := ∫ x', ∫ y', k x' y' ∂μ ∂μ with hc
  set S : ℝ := Rm * (B * Th d s ε) with hSdef
  have hS : ∀ x, |A x| ≤ S := by
    intro x
    have := (kernel_int hρ hRm hkm hbdk hgki x).2
    rw [hI1] at this
    exact this
  have hAm : Measurable A := (hkm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hcb : |c| ≤ S := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := A) (C := S)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hS x)
    simpa [Real.norm_eq_abs, hc, hA] using this
  have hfun : (fun p : Torus d × Torus d =>
      canonicalCenter μ (hC d s φ ε) p.1 p.2 - canonicalCenter μ (hTransport d s φ) p.1 p.2) =
      fun p => -k p.1 p.2 + A p.1 + A p.2 - c := funext fun p => hid p.1 p.2
  rw [hfun]
  have hνprob : IsProbabilityMeasure (μ.prod μ) := inferInstance
  have f2m : AEStronglyMeasurable (fun p : Torus d × Torus d => A p.1) (μ.prod μ) :=
    (hAm.comp measurable_fst).aestronglyMeasurable
  have f3m : AEStronglyMeasurable (fun p : Torus d × Torus d => A p.2) (μ.prod μ) :=
    (hAm.comp measurable_snd).aestronglyMeasurable
  have f4m : AEStronglyMeasurable (fun _ : Torus d × Torus d => c) (μ.prod μ) :=
    aestronglyMeasurable_const
  have hp : (1 : ENNReal) ≤ 2 := by norm_num
  set F1 : Torus d × Torus d → ℝ := fun p => -k p.1 p.2 with hF1
  set F2 : Torus d × Torus d → ℝ := fun p => A p.1 with hF2
  set F3 : Torus d × Torus d → ℝ := fun p => A p.2 with hF3
  set F4 : Torus d × Torus d → ℝ := fun _ => c with hF4
  have hshape : (fun p : Torus d × Torus d => -k p.1 p.2 + A p.1 + A p.2 - c) = F1 + F2 + F3 - F4 :=
    rfl
  have b1 : eLpNorm F1 2 (μ.prod μ) ≤
      ENNReal.ofReal (Real.sqrt (Rm * (B ^ 2 * Th d (2 * s) ε))) := by
    have e : F1 = -(fun p : Torus d × Torus d => k p.1 p.2) := rfl
    rw [e, eLpNorm_neg]
    have := L2_bound hρ hRm hkm hgkm hbdk hgki2
    rwa [hI2] at this
  have b2 : eLpNorm F2 2 (μ.prod μ) ≤ ENNReal.ofReal S := by
    have := eLpNorm_le_of_ae_bound (μ := μ.prod μ) (p := 2) (f := F2)
      (C := S) f2m (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hS p.1)
    simpa using this
  have b3 : eLpNorm F3 2 (μ.prod μ) ≤ ENNReal.ofReal S := by
    have := eLpNorm_le_of_ae_bound (μ := μ.prod μ) (p := 2) (f := F3)
      (C := S) f3m (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hS p.2)
    simpa using this
  have b4 : eLpNorm F4 2 (μ.prod μ) ≤ ENNReal.ofReal S := by
    have := eLpNorm_le_of_ae_bound (μ := μ.prod μ) (p := 2) (f := F4)
      (C := S) f4m (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hcb)
    simpa using this
  rw [hshape]
  have t1 := eLpNorm_sub_le (f := F1 + F2 + F3) (g := F4) (μ := μ.prod μ) hp
  have t2 := eLpNorm_add_le (f := F1 + F2) (g := F3) (μ := μ.prod μ) hp
  have t3 := eLpNorm_add_le (f := F1) (g := F2) (μ := μ.prod μ) hp
  calc eLpNorm (F1 + F2 + F3 - F4) 2 (μ.prod μ)
      ≤ eLpNorm (F1 + F2 + F3) 2 (μ.prod μ) + eLpNorm F4 2 (μ.prod μ) := t1
    _ ≤ (eLpNorm (F1 + F2) 2 (μ.prod μ) + eLpNorm F3 2 (μ.prod μ)) + eLpNorm F4 2 (μ.prod μ) :=
        add_le_add t2 le_rfl
    _ ≤ ((eLpNorm F1 2 (μ.prod μ) + eLpNorm F2 2 (μ.prod μ)) + eLpNorm F3 2 (μ.prod μ)) +
          eLpNorm F4 2 (μ.prod μ) := add_le_add (add_le_add t3 le_rfl) le_rfl
    _ ≤ ((ENNReal.ofReal (Real.sqrt (Rm * (B ^ 2 * Th d (2 * s) ε))) + ENNReal.ofReal S) +
          ENNReal.ofReal S) + ENNReal.ofReal S :=
        add_le_add (add_le_add (add_le_add b1 b2) b3) b4
    _ = _ := by ring


theorem sub_conv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun p : Torus d × Torus d =>
        canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 -
          canonicalCenter (withDensityReal ρ) (hTransport d s φ) p.1 p.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ))) (𝓝[>] 0) (𝓝 0) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨B, hB0, hB⟩ := hT_bound hd hs0 hsd hφ
  obtain ⟨Rm, hRm0, hRm⟩ := sub_setup hρ
  have hΘ1 : Tendsto (Th d s) (𝓝[>] 0) (𝓝 0) := theta_tendsto (by omega) hsd
  have hΘ2 : Tendsto (Th d (2 * s)) (𝓝[>] 0) (𝓝 0) := theta_tendsto (by omega) (by linarith)
  have h1 : Tendsto (fun ε => ENNReal.ofReal (Real.sqrt (Rm * (B ^ 2 * Th d (2 * s) ε))))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 := (hΘ2.const_mul (B ^ 2)).const_mul Rm
    have h' := (Real.continuous_sqrt.tendsto _).comp h0
    have h'' := ENNReal.tendsto_ofReal h'
    simpa using h''
  have h2 : Tendsto (fun ε => ENNReal.ofReal (Rm * (B * Th d s ε))) (𝓝[>] 0) (𝓝 0) := by
    have h0 := (hΘ1.const_mul B).const_mul Rm
    have h'' := ENNReal.tendsto_ofReal h0
    simpa using h''
  have hU := h1.add ((h2.add h2).add h2)
  rw [add_zero, add_zero, add_zero] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact sub_bound hd hs0 hs hρ hφ hB0 hB hRm0 hRm hε

end Sub
end HRS.LocalDivAux
