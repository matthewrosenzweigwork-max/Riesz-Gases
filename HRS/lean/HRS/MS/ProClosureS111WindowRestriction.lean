import HRS.MS.S111TermAux7
import HRS.MS.ProClosureS111PathMoments

/-! A concrete bounded restriction map from the physical full path pair
to its moving observation window. Its evaluation identity is pointwise. -/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111T

variable {d : ℕ} {m T u H : ℝ}

def physicalWindowTime (hu : 0 ≤ u) (hH : u + T ≤ H)
    (tau : Icc (0 : ℝ) T) : Icc (0 : ℝ) H :=
  ⟨u + tau, add_nonneg hu tau.property.1,
    by linarith [tau.property.2]⟩

def physicalWindowRestriction (hu : 0 ≤ u) (hH : u + T ≤ H) :
    OscPath d m H →L[ℝ] OscPath d m T :=
  ({ toFun := fun w =>
       (⟨fun tau => OscPath.at' w (physicalWindowTime hu hH tau),
         (show Continuous (fun tau : Icc (0 : ℝ) T =>
           (show C(Icc (0 : ℝ) H, OscDual d m) from w) (physicalWindowTime hu hH tau)) from
           w.continuous.comp (by unfold physicalWindowTime; fun_prop))⟩ :
         C(Icc (0 : ℝ) T, OscDual d m))
     map_add' := fun _ _ => ContinuousMap.ext fun _ => rfl
     map_smul' := fun _ _ => ContinuousMap.ext fun _ => rfl } :
    OscPath d m H →ₗ[ℝ] OscPath d m T).mkContinuous 1 (by
      intro w
      simp only [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg w)).2 fun tau =>
        ContinuousMap.norm_coe_le_norm w (physicalWindowTime hu hH tau))

@[simp] theorem physicalWindowRestriction_apply (hu : 0 ≤ u) (hH : u + T ≤ H)
    (w : OscPath d m H) (tau : Icc (0 : ℝ) T) :
    OscPath.at' (physicalWindowRestriction hu hH w) tau =
      OscPath.at' w (physicalWindowTime hu hH tau) := rfl

def physicalPairedWindow (hu : 0 ≤ u) (hH : u + T ≤ H) (side : Fin 2)
    (w : PathPair d m H) : OscPath d m T :=
  physicalWindowRestriction hu hH (if side = 0 then w.1 else w.2)

theorem physicalPairedWindow_measurable (hu : 0 ≤ u) (hH : u + T ≤ H) (side : Fin 2) :
    Measurable (physicalPairedWindow (d := d) (m := m) hu hH side) := by
  unfold physicalPairedWindow
  by_cases hi : side = 0
  · simpa only [if_pos hi, Function.comp_def] using
      (physicalWindowRestriction (d := d) (m := m) hu hH).continuous.measurable.comp measurable_fst
  · simpa only [if_neg hi, Function.comp_def] using
      (physicalWindowRestriction (d := d) (m := m) hu hH).continuous.measurable.comp measurable_snd

theorem physicalPairedWindow_apply (hu : 0 ≤ u) (hH : u + T ≤ H)
    (hH0 : 0 ≤ H) (side : Fin 2) (w : PathPair d m H) (tau : Icc (0 : ℝ) T) :
    OscPath.at' (physicalPairedWindow hu hH side w) tau =
      pairedProcess d m H hH0 side (u + tau) w := by
  have ht : physicalWindowTime hu hH tau = clippedTime H hH0 (u + tau) := by
    apply Subtype.ext
    change u + (tau : ℝ) = max 0 (min (u + (tau : ℝ)) H)
    exact (s111t_clip_of_mem (physicalWindowTime hu hH tau).property).symm
  change OscPath.at' (if side = 0 then w.1 else w.2) (physicalWindowTime hu hH tau) =
    OscPath.at' (if side = 0 then w.1 else w.2) (clippedTime H hH0 (u + tau))
  rw [ht]

/-- The concrete moving-window map has norm at most one, including an
empty observation interval. -/
theorem physicalWindowRestriction_norm_le (hu : 0 ≤ u) (hH : u + T ≤ H)
    (w : OscPath d m H) :
    ‖physicalWindowRestriction hu hH w‖ ≤ ‖w‖ := by
  exact (ContinuousMap.norm_le _ (norm_nonneg w)).2 fun tau =>
    ContinuousMap.norm_coe_le_norm w (physicalWindowTime hu hH tau)

/-- Restricting a random path to its moving window preserves every finite
moment exponent without a multiplicative loss. -/
theorem physicalWindowRestriction_memLp
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {p : ℝ≥0∞} (hu : 0 ≤ u) (hH : u + T ≤ H)
    {X : Omega → OscPath d m H} (hX : MemLp X p P) :
    MemLp (fun w => physicalWindowRestriction hu hH (X w)) p P := by
  refine hX.norm.mono'
    ((physicalWindowRestriction (d := d) (m := m) hu hH).continuous.comp_aestronglyMeasurable
      hX.aestronglyMeasurable) ?_
  exact ae_of_all _ fun w => physicalWindowRestriction_norm_le hu hH (X w)

/-- The actual fourth Bochner moment decreases under moving-window
restriction. -/
theorem physicalWindowRestriction_fourth_moment_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (hu : 0 ≤ u) (hH : u + T ≤ H)
    {X : Omega → OscPath d m H} (hX : MemLp X 4 P) :
    (∫ w, ‖physicalWindowRestriction hu hH (X w)‖ ^ 4 ∂P) ≤
      ∫ w, ‖X w‖ ^ 4 ∂P := by
  have hW := physicalWindowRestriction_memLp hu hH hX
  exact integral_mono
    (hW.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0))
    (hX.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0))
    (fun w => pow_le_pow_left₀ (norm_nonneg _) (physicalWindowRestriction_norm_le hu hH (X w)) 4)

/-- A paired path difference is restricted by the same norm-one linear
map, so its fourth moment also incurs no loss. -/
theorem physicalPairedWindow_difference_fourth_moment_le
    (hu : 0 ≤ u) (hH : u + T ≤ H) (P : Measure (PathPair d m H))
    (hD : MemLp (fun w : PathPair d m H => w.1 - w.2) 4 P) :
    (∫ w, ‖physicalPairedWindow hu hH 0 w -
      physicalPairedWindow hu hH 1 w‖ ^ 4 ∂P) ≤
      ∫ w, ‖w.1 - w.2‖ ^ 4 ∂P := by
  have he : ∀ w : PathPair d m H,
      physicalPairedWindow hu hH 0 w - physicalPairedWindow hu hH 1 w =
        physicalWindowRestriction hu hH (w.1 - w.2) := by
    intro w
    simp [physicalPairedWindow, map_sub]
  simpa only [he] using physicalWindowRestriction_fourth_moment_le hu hH hD

/-- The Gaussian-series input already used by the accepted physical path
construction supplies the initial fourth moment. Together with its fourth
increments this gives an explicit moment bound for the exact continuous
modification on every moving window.

The feature trace and increment constant remain explicit inputs. Uniform
physical estimates for those inputs are needed for all-start bounds. -/
theorem gaussian_series_window_fourth_moment
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : ℕ → Omega → ℝ)
    (hg : ∀ k, ProbabilityTheory.HasLaw (g k) (ProbabilityTheory.gaussianReal 0 1) P)
    (hind : ProbabilityTheory.iIndepFun g P)
    (X : ℝ → Omega → OscDual d m) (hX : ∀ t, Measurable (X t))
    (ell : ℕ → OscDual d m) (hs : Summable fun k => ‖ell k‖ ^ 2)
    (hX0 : S111tIsGSL P g ell (X 0))
    {r C : ℝ} (hH0 : 0 < H) (hr0 : 0 < r) (hr1 : r < 1)
    (hr : 1 < 2 * r ^ 4) (hC : 0 ≤ C)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2))
    (hu : 0 ≤ u) (hH : u + T ≤ H) :
    let W := fun w => physicalWindowRestriction hu hH
      (HRS.Whole.AppendixALemmas.contPathOf H
        (fun t => HRS.MP.KC.mkc_Zc X H r t w) : OscPath d m H)
    MemLp W 4 P ∧
      (∫ w, ‖W w‖ ^ 4 ∂P) ≤
        8 * (3 * (∑' k, ‖ell k‖ ^ 2) ^ 2 +
          (HRS.MP.KC.mkc_c r) ^ 4 * (C * H ^ 2 / (1 - 1 / (2 * r ^ 4)))) := by
  have hinit := s111t_gsl_fourth hg hind ell hs (X 0) hX0
  have hX04 : MemLp (X 0) 4 P := by
    change eLpNorm (X 0) 4 P < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
      (hX 0).aestronglyMeasurable).2
    simpa only [ENNReal.toReal_ofNat] using
      hinit.trans_lt ENNReal.ofReal_lt_top
  have henorm (y : OscDual d m) :
      ENNReal.ofReal (‖y‖ ^ 4) = ‖y‖ₑ ^ (4 : ℝ) := by
    rw [← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_pow (norm_nonneg y) 4).trans
      (ENNReal.rpow_natCast (ENNReal.ofReal ‖y‖) 4).symm
  have hinit_bound : (∫ w, ‖X 0 w‖ ^ 4 ∂P) ≤ 3 * (∑' k, ‖ell k‖ ^ 2) ^ 2 := by
    have he := ofReal_integral_eq_lintegral_ofReal
      (hX04.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0))
      (ae_of_all _ fun w => pow_nonneg (norm_nonneg (X 0 w)) 4)
    have hb : ENNReal.ofReal (∫ w, ‖X 0 w‖ ^ 4 ∂P) ≤
        ENNReal.ofReal (3 * (∑' k, ‖ell k‖ ^ 2) ^ 2) := by
      rw [he]
      simpa only [henorm] using hinit
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  have hmom' : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro s hs t ht
    simpa only [henorm] using hmom s hs t ht
  let Y : Omega → OscPath d m H := fun w =>
    HRS.Whole.AppendixALemmas.contPathOf H (fun t => HRS.MP.KC.mkc_Zc X H r t w)
  have hY : MemLp Y 4 P :=
    continuous_modification_memLp_four_of_fourth_increments P X hH0 hr0 hr1 hr
      hX hX04 hC hmom'
  have hY_bound := continuous_modification_fourth_moment_bound P X hH0 hr0 hr1 hr
    hX hX04 hC hmom'
  refine ⟨physicalWindowRestriction_memLp hu hH hY, ?_⟩
  exact (physicalWindowRestriction_fourth_moment_le hu hH hY).trans
    (hY_bound.trans (by gcongr))


end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physicalWindowRestriction
#print axioms HRS.MS.ProClosureS111.physicalPairedWindow_apply


#print axioms HRS.MS.ProClosureS111.gaussian_series_window_fourth_moment
#print axioms HRS.MS.ProClosureS111.physicalPairedWindow_difference_fourth_moment_le

