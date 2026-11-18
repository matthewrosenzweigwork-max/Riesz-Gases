import HRS.Whole.Round2
import HRS.Prob.HilbertMartingale

/-!
# HRS.MS.R2ChaosAux1 -- measurability toolkit for S9.4 `round2_integrated_chaos`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.  See `docs/handoff` / the scratch plan `S94_PLAN.md`
for the per-row plan.  Summary of the route (it differs from the TeX supplement L7027-7124):

* finite-rank step kernels in time: `B_N = Ψ(ξ_N(u)) - m_N - (1/2)(μ_N(g_t) - E)` with `Ψ` continuous `C^m → L²(dt)`; the
  deterministic centering `m_N → m` pointwise in `t` (weak convergence at a fixed time plus uniform fourth moments) and
  boundedly, hence in `L²(dt)` (replaces the Skorokhod uniform-in-time estimate);
* general `h_t`: dyadic time averages, Lebesgue differentiation, S9.1 on each interval, S9.2 tail and dominated convergence in
  `t` (so that `L²(P ⊗ dt)` approximation suffices: no Minkowski in `L^r(L²)`);
* Gaussian side: the Wick sections for correlated Gaussian coordinates are `L²`-Lipschitz in the kernel (constant `Λ`);
  a single jointly measurable `F` for every `t` and every orthonormal basis;
* convergence in law by an approximation criterion across varying probability spaces; (ii) is the image of (i) under the
  continuous map `(B, w) ↦ (B, JB, w)`; (iii) by weak convergence plus uniform higher moments through the merged
  `wassersteinE_two_tendsto_of_weak` and an interpolation for `r > 2`.

This file: measurability of the maps `ζ ↦ r2L2Path T (f(·, ζ))` for jointly measurable `f`, and the integration map.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

/-- The set of `ζ` for which `t ↦ f(t,ζ)` lies in `L²([0,T])` is measurable. -/
theorem s94_measurableSet_memLp {Ω : Type*} [MeasurableSpace Ω] (T : ℝ) (f : ℝ × Ω → ℝ)
    (hf : Measurable f) :
    MeasurableSet {ζ : Ω | MemLp (fun t => f (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T))} := by
  have hlin : Measurable fun ζ : Ω => ∫⁻ t, ‖f (t, ζ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have : Measurable fun q : ℝ × Ω => ‖f q‖ₑ ^ (2 : ℝ) := hf.enorm.pow_const _
    exact this.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0 : ℝ) T))
  have hset : {ζ : Ω | MemLp (fun t => f (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T))} =
      {ζ : Ω | (∫⁻ t, ‖f (t, ζ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) T))) < ⊤} := by
    ext ζ
    show MemLp (fun t => f (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) ↔ _
    have hm : AEStronglyMeasurable (fun t => f (t, ζ)) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (hf.comp measurable_prodMk_right).aestronglyMeasurable
    constructor
    · intro h
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hm).1
        (show eLpNorm (fun t => f (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) < ⊤ from h.eLpNorm_lt_top)
      simpa using this
    · intro h
      have h' : eLpNorm (fun t => f (t, ζ)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) < ⊤ :=
        (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hm).2
          (by simpa using h)
      exact h'
  rw [hset]
  exact measurableSet_lt hlin measurable_const

/-- On the set `{t ↦ f(t,ζ) ∈ L²}`, `r2L2Path` is the `L²` class of `f(·,ζ)`. -/
theorem s94_r2L2Path_eq {T : ℝ} {g : ℝ → ℝ} (h : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r2L2Path T g = (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from h.toLp g) := by
  unfold r2L2Path
  exact dif_pos h

theorem s94_r2L2Path_eq_zero {T : ℝ} {g : ℝ → ℝ} (h : ¬ MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r2L2Path T g = 0 := by
  unfold r2L2Path
  exact dif_neg h

/-- For jointly measurable `f`, `ζ ↦ r2L2Path T (f(·,ζ))` is a measurable map into `R2L2 T`. -/
theorem s94_measurable_r2L2Path {Ω : Type*} [MeasurableSpace Ω] (T : ℝ) (f : ℝ × Ω → ℝ)
    (hf : Measurable f) : Measurable fun ζ : Ω => r2L2Path T (fun t => f (t, ζ)) := by
  classical
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  letI : MeasurableSpace (Lp ℝ 2 μT) := borel _
  haveI : BorelSpace (Lp ℝ 2 μT) := ⟨rfl⟩
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := Lp ℝ 2 μT)
  haveI := hι
  have hG := s94_measurableSet_memLp T f hf
  refine (HRS.measurable_of_inner_basis b (Z := Ω)
    (f := fun ζ => (r2L2Path T (fun t => f (t, ζ)) : Lp ℝ 2 μT)) (fun i => ?_) : Measurable fun ζ : Ω =>
      (r2L2Path T (fun t => f (t, ζ)) : Lp ℝ 2 μT))
  have hint : Measurable fun ζ : Ω => ∫ t, (b i : ℝ → ℝ) t * f (t, ζ) ∂μT := by
    have hsm : StronglyMeasurable fun q : ℝ × Ω => (b i : ℝ → ℝ) q.1 * f q :=
      ((Lp.stronglyMeasurable (b i)).comp_measurable measurable_fst).mul hf.stronglyMeasurable
    exact hsm.integral_prod_left'.measurable
  have heq : (fun ζ : Ω => inner ℝ (b i) (r2L2Path T (fun t => f (t, ζ)) : Lp ℝ 2 μT)) =
      Set.indicator {ζ : Ω | MemLp (fun t => f (t, ζ)) 2 μT}
        (fun ζ => ∫ t, (b i : ℝ → ℝ) t * f (t, ζ) ∂μT) := by
    funext ζ
    by_cases hz : MemLp (fun t => f (t, ζ)) 2 μT
    · rw [Set.indicator_of_mem (show ζ ∈ {ζ : Ω | MemLp (fun t => f (t, ζ)) 2 μT} from hz),
        s94_r2L2Path_eq hz, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hz.coeFn_toLp] with t ht
      rw [ht]
      simp [mul_comm]
    · rw [Set.indicator_of_notMem (show ζ ∉ {ζ : Ω | MemLp (fun t => f (t, ζ)) 2 μT} from hz),
        s94_r2L2Path_eq_zero hz]
      exact inner_zero_right _
  show Measurable fun ζ : Ω => inner ℝ (b i) (r2L2Path T (fun t => f (t, ζ)) : Lp ℝ 2 μT)
  rw [heq]
  exact hint.indicator hG

/-! ### The integration map `J : L²([0,T]) → C([0,T])` -/

section Integration

variable {T : ℝ}

/-- The primitive `u ↦ ∫_0^u g` of a class `g ∈ L²([0,T])`. -/
def s94_prim (T : ℝ) (g : R2L2 T) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g) t

theorem s94_integrableOn (g : R2L2 T) :
    IntegrableOn (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g) (Set.Icc (0 : ℝ) T) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    constructor; simp
  exact (Lp.memLp (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g)).integrable (by norm_num)

theorem s94_ae_Ioc {P : ℝ → Prop} (h : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), P t)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) u)), P t :=
  ae_restrict_of_ae_restrict_of_subset
    (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hu.2)) h

theorem s94_continuousOn_prim (hT : 0 ≤ T) (g : R2L2 T) :
    ContinuousOn (s94_prim T g) (Set.Icc (0 : ℝ) T) := by
  have hint : IntervalIntegrable (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact s94_integrableOn g
  have := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) (Set.left_mem_uIcc)
  rwa [Set.uIcc_of_le hT] at this

theorem s94_prim_add (g h : R2L2 T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    s94_prim T (g + h) u = s94_prim T g u + s94_prim T h u := by
  have hu0 : 0 ≤ u := hu.1
  unfold s94_prim
  have hg : IntegrableOn (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g) (Set.Ioc 0 u) volume :=
    (s94_integrableOn g).mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hu.2))
  have hh : IntegrableOn (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from h) (Set.Ioc 0 u) volume :=
    (s94_integrableOn h).mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hu.2))
  rw [intervalIntegral.integral_of_le hu0, intervalIntegral.integral_of_le hu0,
    intervalIntegral.integral_of_le hu0, ← integral_add hg hh]
  refine integral_congr_ae ?_
  filter_upwards [s94_ae_Ioc (Lp.coeFn_add (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g)
    (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from h) |>.mono fun t ht => ht) hu] with t ht
  exact ht

theorem s94_prim_smul (c : ℝ) (g : R2L2 T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    s94_prim T (c • g) u = c * s94_prim T g u := by
  have hu0 : 0 ≤ u := hu.1
  unfold s94_prim
  rw [intervalIntegral.integral_of_le hu0, intervalIntegral.integral_of_le hu0, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [s94_ae_Ioc (Lp.coeFn_smul c (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from g)
    |>.mono fun t ht => ht) hu] with t ht
  exact ht

theorem s94_norm_prim_le (g : R2L2 T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    ‖s94_prim T g u‖ ≤ Real.sqrt T * ‖g‖ := by
  have hu0 : 0 ≤ u := hu.1
  have hT : 0 ≤ T := hu0.trans hu.2
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  set G : Lp ℝ 2 μT := g with hG
  unfold s94_prim
  rw [intervalIntegral.integral_of_le hu0]
  have h1 : ‖∫ t in Set.Ioc (0 : ℝ) u, G t‖ ≤ (∫⁻ t in Set.Ioc (0 : ℝ) u, ‖G t‖ₑ).toReal := by
    have := norm_integral_le_lintegral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) u)) (fun t => (G : ℝ → ℝ) t)
    simp only [ofReal_norm_eq_enorm] at this
    exact this
  have h2 : ∫⁻ t in Set.Ioc (0 : ℝ) u, ‖G t‖ₑ ≤ ∫⁻ t, ‖G t‖ₑ ∂μT :=
    lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hu.2))
  have h3 : ∫⁻ t, ‖G t‖ₑ ∂μT = eLpNorm G 1 μT := (eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable G)).symm
  have hfin : IsFiniteMeasure μT := by
    constructor; simp [hμT]
  have h4 : eLpNorm G 1 μT ≤ eLpNorm G 2 μT * μT Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (Lp.aestronglyMeasurable G)
  have hμ : μT Set.univ = ENNReal.ofReal T := by simp [hμT]
  have h5 : μT Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal (Real.sqrt T) := by
    rw [hμ]
    have : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [this, ENNReal.ofReal_rpow_of_nonneg hT (by norm_num), Real.sqrt_eq_rpow]
  rw [h5] at h4
  have hne : eLpNorm G 2 μT ≠ ⊤ := (Lp.memLp G).eLpNorm_ne_top
  have h6 : (eLpNorm G 1 μT).toReal ≤ ‖G‖ * Real.sqrt T := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hne ENNReal.ofReal_ne_top) h4
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
    rwa [Lp.norm_def]
  have h7 : (∫⁻ t in Set.Ioc (0 : ℝ) u, ‖G t‖ₑ).toReal ≤ (eLpNorm G 1 μT).toReal := by
    refine ENNReal.toReal_mono ?_ (h2.trans h3.le)
    have : eLpNorm G 1 μT ≤ eLpNorm G 2 μT * ENNReal.ofReal (Real.sqrt T) := h4
    exact (this.trans_lt (ENNReal.mul_lt_top hne.lt_top ENNReal.ofReal_lt_top)).ne
  calc ‖∫ t in Set.Ioc (0 : ℝ) u, G t‖ ≤ _ := h1
    _ ≤ _ := h7
    _ ≤ ‖G‖ * Real.sqrt T := h6
    _ = Real.sqrt T * ‖g‖ := by rw [mul_comm]; rfl

/-- The linear integration map. -/
def s94_Jlin (hT : 0 ≤ T) : R2L2 T →ₗ[ℝ] C(Set.Icc (0 : ℝ) T, ℝ) where
  toFun g := ⟨fun u => s94_prim T g u, (s94_continuousOn_prim hT g).restrict⟩
  map_add' g h := by
    ext u
    exact s94_prim_add g h u.2
  map_smul' c g := by
    ext u
    exact s94_prim_smul c g u.2

/-- The integration map `J : L²([0,T]) →L C([0,T])`, `‖J‖ ≤ √T`. -/
def s94_J (hT : 0 ≤ T) : R2L2 T →L[ℝ] C(Set.Icc (0 : ℝ) T, ℝ) :=
  LinearMap.mkContinuous (s94_Jlin hT) (Real.sqrt T) fun g =>
    (ContinuousMap.norm_le _ (by positivity)).2 fun u => s94_norm_prim_le g u.2

theorem s94_J_apply (hT : 0 ≤ T) (g : R2L2 T) (u : Set.Icc (0 : ℝ) T) :
    s94_J hT g u = s94_prim T g u := rfl

theorem s94_J_lipschitz (hT : 0 ≤ T) : LipschitzWith ⟨Real.sqrt T, Real.sqrt_nonneg _⟩ (s94_J hT) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    have h : ‖s94_J hT (x - y)‖ ≤ Real.sqrt T * ‖x - y‖ :=
      (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
        fun u => s94_norm_prim_le (x - y) u.2
    exact h

theorem s94_r2ContPath_eq {T : ℝ} {f : ℝ → ℝ} (h : Continuous fun t : Set.Icc (0 : ℝ) T => f t) :
    r2ContPath T f = ⟨fun t => f t, h⟩ := by
  unfold r2ContPath
  exact dif_pos h

/-- `r2IntPath` of an `L²` function is `J` of its class. -/
theorem s94_r2IntPath_eq (hT : 0 ≤ T) {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r2IntPath T f = s94_J hT (r2L2Path T f) := by
  rw [s94_r2L2Path_eq hf]
  set g : R2L2 T := (hf.toLp f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))) with hg
  have hfun : (fun t : Set.Icc (0 : ℝ) T => ∫ s in (0 : ℝ)..(t : ℝ), f s) =
      fun t : Set.Icc (0 : ℝ) T => s94_prim T g (t : ℝ) := by
    funext t
    have hu0 : 0 ≤ (t : ℝ) := t.2.1
    unfold s94_prim
    rw [intervalIntegral.integral_of_le hu0, intervalIntegral.integral_of_le hu0]
    refine integral_congr_ae ?_
    filter_upwards [s94_ae_Ioc hf.coeFn_toLp t.2] with s hs
    exact hs.symm
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => ∫ s in (0 : ℝ)..(t : ℝ), f s := by
    rw [hfun]; exact (s94_continuousOn_prim hT g).restrict
  unfold r2IntPath
  rw [s94_r2ContPath_eq (T := T) (f := fun u => ∫ s in (0 : ℝ)..u, f s) hc]
  ext t
  exact congrFun hfun t

end Integration

end HRS.MS.R2Chaos
