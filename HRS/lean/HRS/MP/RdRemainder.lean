import HRS.Whole.AppendixALemmas2
import HRS.MP.HNegInfra

/-!
# Packet MPRREM: `E sup_t ‖ℝ_N^t‖_{H^{-q_R}(ℝ^d)} ≤ C T σ_N(𝔈_N + e_N)` (S.A.25 on `ℝ^d`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.Whole.AppendixALemmas (HasContVersion IsRemainderW SelectedCommutatorInput PathAdjointInput)
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MP.RdRem

variable {d : ℕ}

/-! ### Elementary facts -/

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem mrr_sobolevNorm_mono {a b : ℝ} (hab : a ≤ b) {φ : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev b φ) :
    HRS.Whole.sobolevNorm a φ ≤ HRS.Whole.sobolevNorm b φ := by
  unfold HRS.Whole.sobolevNorm
  refine Real.sqrt_le_sqrt ?_
  have hm := memSobolev_mono hab h
  unfold sobolevNormSq
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => ?_) h.2
    (Filter.Eventually.of_forall fun ξ => ?_)
  · have := wt_pos (d := d) ξ
    positivity
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) hab) (by positivity)

theorem mrr_abs_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) (x : Euc d) :
    |f x| ≤ cbNorm k f := by
  have h0 : |f x| ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 f z‖ := by
    have := le_ciSup (hf.2 0 (Nat.zero_le _)) x
    simpa using this
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))

theorem mrr_eN_nonneg {s : ℝ} (fd : FieldDensityRd d s) (N : ℕ) : 0 ≤ fd.eN N := by
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  cases fd with
  | nd Rg => simp [FieldDensityRd.eN]
  | decSub c =>
    cases c with
    | sharp a ha => simp [FieldDensityRd.eN, DecayingDensity.errorRate]
    | lower hs =>
      simp only [FieldDensityRd.eN, DecayingDensity.errorRate]
      refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      split_ifs <;> linarith
  | decSuperIso m p => simp [FieldDensityRd.eN]
  | decSuperHilb m => simp [FieldDensityRd.eN]

theorem mrr_sigma_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.sigma N := by
  unfold WholeMainData.sigma sigmaScale
  have hκ := (S.hκ N).le
  split_ifs
  · exact hκ
  · exact le_min hκ (Real.sqrt_nonneg _)

/-! ### The pathwise bound of the remainder integral for one test -/

theorem mrr_path_bound (S : WholeMainData d) {Γ : ℝ} {T K C₀ Λ : ℝ} {e : ℕ → ℝ}
    (hsel : SelectedCommutatorInput S Γ T K C₀ Λ e) {N : ℕ} (hN : 2 ≤ N) (Xp : ℝ → EucConfig d N)
    (hnn : ∀ r ∈ Set.Icc (0 : ℝ) T, Function.Injective (Xp r) →
      0 ≤ rieszModulatedEnergy d S.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N)
    (hinj : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Function.Injective (Xp r))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {Γ' : ℝ} (hΓ : Γ ≤ Γ') {φ : Euc d → ℝ}
    (hφ : HRS.Whole.IsSobolevTest Γ' φ) :
    ENNReal.ofReal |∫ r in (0 : ℝ)..t,
        commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
          (Xp r) (HRS.Whole.withDensityReal (S.ρ N r))| ≤
      ENNReal.ofReal (max K 0 * HRS.Whole.sobolevNorm Γ' φ) *
        ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N) := by
  classical
  have ht0 := ht.1
  rw [intervalIntegral.integral_of_le ht0]
  have hφΓ : HRS.Whole.IsSobolevTest Γ φ := ⟨hφ.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hΓ hφ.2⟩
  have hnorm : HRS.Whole.sobolevNorm Γ φ ≤ HRS.Whole.sobolevNorm Γ' φ := mrr_sobolevNorm_mono hΓ hφ.2
  have ha : 0 ≤ HRS.Whole.sobolevNorm Γ φ := Real.sqrt_nonneg _
  have hcoef : 0 ≤ max K 0 * HRS.Whole.sobolevNorm Γ' φ :=
    mul_nonneg (le_max_right _ _) ((ha.trans hnorm))
  set f : ℝ → ℝ := fun r =>
    commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
      (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) with hf
  set E : ℝ → ℝ := fun r =>
    rieszModulatedEnergy d S.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N with hE
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖f r‖ₑ ≤ ENNReal.ofReal (max K 0 * HRS.Whole.sobolevNorm Γ' φ) * ENNReal.ofReal (E r) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub hinj
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with r hr hrm
    have hrI := hsub hrm
    have hb := hsel N hN (Xp r) hr r t hrm.1.le hrm.2 ht.2 φ hφΓ
    have hE0 : 0 ≤ E r := hnn r hrI hr
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hcoef]
    refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
    have hKa : K * HRS.Whole.sobolevNorm Γ φ ≤ max K 0 * HRS.Whole.sobolevNorm Γ' φ :=
      (mul_le_mul_of_nonneg_right (le_max_left K 0) ha).trans
        (mul_le_mul_of_nonneg_left hnorm (le_max_right K 0))
    exact mul_le_mul_of_nonneg_right hKa hE0
  calc ENNReal.ofReal |∫ r in Set.Ioc (0 : ℝ) t, f r|
      = ‖∫ r in Set.Ioc (0 : ℝ) t, f r‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) t, ‖f r‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (max K 0 * HRS.Whole.sobolevNorm Γ' φ) * ENNReal.ofReal (E r) :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal (max K 0 * HRS.Whole.sobolevNorm Γ' φ) * ∫⁻ r in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (E r) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max K 0 * HRS.Whole.sobolevNorm Γ' φ) * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (E r) := by
        gcongr

/-! ### Joint measurability of the flow and of the corrected energy -/

/-- clamp a time into `[0,T]` -/
def mrrClamp (T r : ℝ) : ℝ := max 0 (min r T)

theorem mrrClamp_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : mrrClamp T r ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem mrrClamp_of_mem {T r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : mrrClamp T r = r := by
  unfold mrrClamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem continuous_mrrClamp (T : ℝ) : Continuous (mrrClamp T) := by
  unfold mrrClamp; fun_prop

theorem mrr_prog_meas {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → E) (hprog : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ}
    (hT : 0 ≤ T) : Measurable fun p : ℝ × Ω => X (Real.toNNReal (mrrClamp T p.1)) p.2 := by
  have h1 := hprog T
  have hle : (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod (ℱ T) ≤
      (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le T))
  have h2 : Measurable fun p : Set.Iic T × Ω => ofNNRealTime X p.1 p.2 := h1.mono hle le_rfl
  have h3 : Measurable fun p : ℝ × Ω =>
      ((⟨mrrClamp T p.1, (mrrClamp_mem hT p.1).2⟩ : Set.Iic T), p.2) :=
    (((continuous_mrrClamp T).measurable.comp measurable_fst).subtype_mk).prodMk measurable_snd
  exact h2.comp h3

theorem mrr_measurable_rieszKernel (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [hs, if_false]
    exact measurable_norm.pow_const _

theorem mrr_integral_withDensityReal (ρ : Euc d → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : Euc d → ℝ) : ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y)]

section Energy

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem mrr_rho_cont_time (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (x : Euc d) : ContinuousOn (fun u => S.ρ N u x) (Set.Icc 0 S.T) := by
  obtain ⟨B, ρt, h⟩ := hS.mean_field.time_derivative
  intro t ht
  exact ((h N hN).1 t ht x).continuousWithinAt

theorem mrr_rho_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    Measurable fun p : ℝ × Euc d => S.ρ N (mrrClamp S.T p.1) p.2 := by
  have hT : 0 ≤ S.T := S.hT.le
  have hρc : ∀ q, Continuous (S.ρ N (mrrClamp S.T q)) := fun q =>
    ((hS.mean_field.regular N hN).1 _ (mrrClamp_mem hT q)).1.1.continuous
  have hpt : ∀ x, Continuous fun q => S.ρ N (mrrClamp S.T q) x := fun x => by
    have h1 : ContinuousOn (fun u => S.ρ N u x) (Set.Icc 0 S.T) := mrr_rho_cont_time hS hN x
    exact h1.comp_continuous (continuous_mrrClamp S.T) (fun q => mrrClamp_mem hT q)
  exact measurable_uncurry_of_continuous_of_measurable (u := fun (q : ℝ) (x : Euc d) =>
    S.ρ N (mrrClamp S.T q) x) (fun x => hpt x) (fun q => (hρc q).measurable)

theorem mrr_energy_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    Measurable fun p : ℝ × EucConfig d N =>
      rieszModulatedEnergy d S.s p.2 (HRS.Whole.withDensityReal (S.ρ N (mrrClamp S.T p.1))) +
        oNΛ d S.s C₀ Λ N := by
  have hT : 0 ≤ S.T := S.hT.le
  have hgm : Measurable (rieszKernel d S.s) := mrr_measurable_rieszKernel S.s
  have hjm := mrr_rho_meas hS hN
  set ρt : ℝ → Euc d → ℝ := fun q => S.ρ N (mrrClamp S.T q) with hρt
  have hprob : ∀ q, HRS.Whole.IsProbDensity (ρt q) := fun q =>
    (hS.mean_field.solution N hN).density _ (mrrClamp_mem hT q)
  have hint : ∀ (q : ℝ) (f : Euc d → ℝ),
      ∫ y, f y ∂(HRS.Whole.withDensityReal (ρt q)) = ∫ y, ρt q y * f y :=
    fun q f => mrr_integral_withDensityReal (ρt q) (hprob q).measurable (hprob q).nonneg f
  have hjm' : Measurable fun p : ℝ × Euc d => ρt p.1 p.2 := hjm
  unfold rieszModulatedEnergy HRS.Whole.modulatedEnergy
  refine Measurable.add (Measurable.add (Measurable.sub ?_ ?_) ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).sub
      ((measurable_pi_apply j).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have e' : (fun p : ℝ × EucConfig d N => HRS.Whole.convMeasure (rieszKernel d S.s) (HRS.Whole.withDensityReal (ρt p.1)) (p.2 i)) =
        fun p => ∫ y, ρt p.1 y * rieszKernel d S.s (p.2 i - y) := funext fun p => hint p.1 _
    rw [e']
    have : StronglyMeasurable (fun q : (ℝ × EucConfig d N) × Euc d =>
        ρt q.1.1 q.2 * rieszKernel d S.s (q.1.2 i - q.2)) := by
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
          measurable_snd)
    exact (this.integral_prod_right' (ν := volume)).measurable
  · have e : (fun p : ℝ × EucConfig d N => HRS.Whole.energyPairing (rieszKernel d S.s)
          (HRS.Whole.withDensityReal (ρt p.1)) (HRS.Whole.withDensityReal (ρt p.1))) =
        fun p => ∫ x, ρt p.1 x * ∫ y, ρt p.1 y * rieszKernel d S.s (x - y) := by
      funext p
      unfold HRS.Whole.energyPairing
      rw [hint p.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [hint p.1]
    refine Measurable.const_mul ?_ _
    rw [e]
    have h1 : StronglyMeasurable (fun q : (ℝ × Euc d) × Euc d =>
        ρt q.1.1 q.2 * rieszKernel d S.s (q.1.2 - q.2)) := by
      refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
    have h2 := h1.integral_prod_right' (ν := volume)
    have h3 : StronglyMeasurable (fun q : ℝ × Euc d =>
        ρt q.1 q.2 * ∫ y, ρt q.1 y * rieszKernel d S.s (q.2 - y)) :=
      (hjm'.stronglyMeasurable).mul h2
    have h4 := h3.integral_prod_right' (ν := volume)
    exact h4.measurable.comp measurable_fst

end Energy

/-! ### Collisions on a null set of times, and the dual-norm reduction -/

theorem mrr_measurableSet_coll (N : ℕ) : MeasurableSet (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ _ : i ≠ j, {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)

theorem mrr_coll_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    {T : ℝ} (hT : 0 ≤ T) (X : ℝ≥0 → Ω → EucConfig d N)
    (hm : Measurable fun p : ℝ × Ω => X (Real.toNNReal (mrrClamp T p.1)) p.2)
    (hcoll : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, X (Real.toNNReal t) ζ ∉ eucCollisionSet d N) :
    ∀ᵐ ζ ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Function.Injective (X (Real.toNNReal r) ζ) := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  set A : Set (Ω × ℝ) := {p | X (Real.toNNReal (mrrClamp T p.2)) p.1 ∈ eucCollisionSet d N} with hA
  have hAm : MeasurableSet A :=
    (hm.comp measurable_swap) (mrr_measurableSet_coll N)
  have h0 : (P.prod ν) A = 0 := by
    rw [Measure.prod_apply_symm hAm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have := hcoll r hr
    have e : (fun x : Ω => (x, r)) ⁻¹' A = {ζ | X (Real.toNNReal r) ζ ∈ eucCollisionSet d N} := by
      ext ζ; simp [hA, mrrClamp_of_mem hr]
    rw [e]
    exact measure_eq_zero_iff_ae_notMem.2 this
  have h1 := (Measure.measure_prod_null hAm).1 h0
  filter_upwards [h1] with ζ hζ
  have : ν (Prod.mk ζ ⁻¹' A) = 0 := hζ
  have h2 := measure_eq_zero_iff_ae_notMem.1 this
  filter_upwards [h2, ae_restrict_mem measurableSet_Icc] with r hr hrm
  have hr' : X (Real.toNNReal r) ζ ∉ eucCollisionSet d N := by
    intro h
    exact hr (by simp only [hA, Set.mem_preimage, Set.mem_setOf_eq]; rwa [mrrClamp_of_mem hrm])
  intro i j hij
  by_contra hne
  exact hr' ⟨i, j, hne, hij⟩

theorem mrr_enorm_le {Γ' : ℝ} {F : HNeg d Γ'} {p : ℕ → ℝ} (h : ‖F‖ = ⨆ n, p n) (B : ℝ≥0∞)
    (hB : ∀ n, ENNReal.ofReal (p n) ≤ B) : ‖F‖ₑ ≤ B := by
  rcases eq_or_ne B ⊤ with rfl | hBt
  · exact le_top
  · have hb : ∀ n, p n ≤ B.toReal := fun n => (ENNReal.ofReal_le_iff_le_toReal hBt).1 (hB n)
    have h2 : ‖F‖ ≤ B.toReal := by rw [h]; exact ciSup_le hb
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖F‖ ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal h2
      _ = B := ENNReal.ofReal_toReal hBt

theorem mrr_closure_bound {Γ' T : ℝ} (D : Set (Set.Icc (0 : ℝ) T)) (hD : Dense D) (g : ℝ → HNeg d Γ')
    (hg : ContinuousOn g (Set.Icc 0 T)) (b : ℝ) (hDB : ∀ t : Set.Icc (0 : ℝ) T, t ∈ D → ‖g t‖ ≤ b) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖g t‖ ≤ b := by
  have hc : Continuous (fun t : Set.Icc (0 : ℝ) T => g t) := hg.restrict
  have hn : Continuous (fun t : Set.Icc (0 : ℝ) T => ‖g t‖) := continuous_norm.comp hc
  have hcl : IsClosed ((fun t : Set.Icc (0 : ℝ) T => ‖g t‖) ⁻¹' Set.Iic b) := isClosed_Iic.preimage hn
  have h1 : closure D ⊆ (fun t : Set.Icc (0 : ℝ) T => ‖g t‖) ⁻¹' Set.Iic b :=
    closure_minimal (fun t ht => hDB t ht) hcl
  intro t ht
  have h2 : (⟨t, ht⟩ : Set.Icc (0 : ℝ) T) ∈ closure D := by
    rw [hD.closure_eq]; exact Set.mem_univ _
  have h3 := h1 h2
  exact h3

/-- a bound `‖F‖ₑ ≤ B` along a dense set of times, extended to all times by continuity -/
theorem mrr_closure_enorm {Γ' T : ℝ} (D : Set (Set.Icc (0 : ℝ) T)) (hD : Dense D) (g : ℝ → HNeg d Γ')
    (hg : ContinuousOn g (Set.Icc 0 T)) (B : ℝ≥0∞)
    (hDB : ∀ t : Set.Icc (0 : ℝ) T, t ∈ D → ‖g t‖ₑ ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖g t‖ₑ ≤ B := by
  rcases eq_or_ne B ⊤ with rfl | hBt
  · intro t _; exact le_top
  · intro t ht
    have hb : ∀ t : Set.Icc (0 : ℝ) T, t ∈ D → ‖g t‖ ≤ B.toReal := by
      intro u hu
      have := hDB u hu
      rw [← ofReal_norm_eq_enorm] at this
      exact (ENNReal.ofReal_le_iff_le_toReal hBt).1 this
    have h := mrr_closure_bound D hD g hg B.toReal hb t ht
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖g t‖ ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal h
      _ = B := ENNReal.ofReal_toReal hBt

theorem mrr_time_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (G : ℝ → Ω → ℝ) (hGm : Measurable fun p : ℝ × Ω => G p.1 p.2) (E1 : ℝ≥0∞)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (G r ζ) ∂P ≤ E1) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (G r ζ)) ∂P ≤ ENNReal.ofReal T * E1 := by
  have hm : Measurable (Function.uncurry fun (ζ : Ω) (r : ℝ) => ENNReal.ofReal (G r ζ)) :=
    ENNReal.measurable_ofReal.comp (hGm.comp measurable_swap)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ζ, ENNReal.ofReal (G r ζ) ∂P)
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, E1 := setLIntegral_mono' measurableSet_Icc hmom
    _ = ENNReal.ofReal T * E1 := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

section PerN

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ}

/-- The per-`N` form of the remainder bound. -/
theorem mrr_perN (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    {K' : ℝ} {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    {N : ℕ} (hN : 2 ≤ N)
    (hcoll : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ᵐ ζ ∂(R N).P,
      (R N).X (Real.toNNReal t) ζ ∉ eucCollisionSet d N)
    (Rm Rc : ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hRem : IsRemainderW S R N (Γ + 2) Rm) (hCont : HasContVersion S.T (R N).P Rm Rc) :
    ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hXm := mrr_prog_meas ℱ (R N).X hF.progressive hT
  have hinjAE := mrr_coll_ae (R N).P hT (R N).X hXm (fun t ht => hcoll t ht)
  set Gc : ℝ → (R N).Ω → ℝ := fun r ζ =>
    rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (mrrClamp S.T r)) ζ)
      (HRS.Whole.withDensityReal (S.ρ N (mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + e N with hGc
  have hGm : Measurable fun p : ℝ × (R N).Ω => Gc p.1 p.2 :=
    ((mrr_energy_meas hS hN1).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N + e N) := by
    intro r hr
    have hb := hS.energy.bound N hN1 r hr
    calc ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) +
            ENNReal.ofReal (e N)) ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          simp only [hGc, mrrClamp_of_mem hr]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) ∂(R N).P +
            ENNReal.ofReal (e N) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (𝔈 N) + ENNReal.ofReal (e N) := add_le_add hb le_rfl
      _ = ENNReal.ofReal (𝔈 N + e N) := (ENNReal.ofReal_add h𝔈 (he N)).symm
  have hZ := mrr_time_moment (R N).P Gc hGm _ hmom
  set Z : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Gc r ζ) with hZdef
  set c : ℝ := S.sigma N / 2 * max K' 0 with hc
  have hσ := mrr_sigma_nonneg S N
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (le_max_right _ _)
  obtain ⟨φ, hφt, hφn, hnormF⟩ := HRS.MP.HNegInfra.hneg_norming d (((Γ + 2 : ℕ) : ℝ))
  have hΓle : (Γ : ℝ) ≤ ((Γ + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right Γ 2
  -- the pathwise bound for one time and one test
  have hpair : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ n : ℕ, ∀ᵐ ζ ∂(R N).P,
      ENNReal.ofReal |HNeg.pairing (φ n) (Rc t ζ)| ≤ ENNReal.ofReal c * Z ζ := by
    intro t ht n
    filter_upwards [hCont.1 t ht, hRem.2 t ht (φ n) (hφt n), hinjAE] with ζ hRc hpairζ hinj
    rw [hRc, hpairζ]
    have hnn' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Function.Injective ((R N).X (Real.toNNReal r) ζ) →
        0 ≤ rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ)
          (HRS.Whole.withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N := by
      intro r hr hinjr
      have hreg := (hS.mean_field.regular N hN1).1 r hr
      have hrho := (hS.mean_field.solution N hN1).density r hr
      have hle : ∀ x, S.ρ N r x ≤ Λ := fun x =>
        ((le_abs_self _).trans (mrr_abs_le_cbNorm hreg.1 x)).trans
          (le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) hreg.2.2)
      have hcomp := hS.energy.completion.2 Λ hΛ N hN (S.ρ N r) hrho hle
        (fun _ => Q09A.log_integrable_withDensityReal hrho
          ((hS.mean_field.solution N hN1).second_moment r hr))
        ((R N).X (Real.toNNReal r) ζ) (fun ⟨i, j, hij, heq⟩ => hij (hinjr heq))
      exact add_nonneg hcomp (he N)
    have hb := mrr_path_bound S hsel hN (fun r => (R N).X (Real.toNNReal r) ζ) hnn' hinj ht hΓle
      (hφt n)
    have hZeq : ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + e N) = Z ζ := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [hGc, mrrClamp_of_mem hr]
    rw [hZeq] at hb
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ S.sigma N / 2),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
    have h1 : ENNReal.ofReal (max K' 0 * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) (φ n)) ≤
        ENNReal.ofReal (max K' 0) :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (le_max_right _ _) (hφn n))
    calc ENNReal.ofReal (S.sigma N / 2) * ENNReal.ofReal |∫ r in (0 : ℝ)..t,
          commN d S.s (fun x => Torus.matVec S.M.transpose
            (gradient (propagatorW (S.coeff N) r t (φ n)) x))
            ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r))|
        ≤ ENNReal.ofReal (S.sigma N / 2) * (ENNReal.ofReal (max K' 0) * Z ζ) := by
          gcongr
          exact hb.trans (by gcongr)
      _ = ENNReal.ofReal c * Z ζ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
  -- the supremum over all times
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) S.T)
  haveI : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ζ ∂(R N).P, ∀ (t : D) (n : ℕ),
      ENNReal.ofReal |HNeg.pairing (φ n) (Rc t.1.1 ζ)| ≤ ENNReal.ofReal c * Z ζ :=
    ae_all_iff.2 fun t => ae_all_iff.2 fun n => hpair t.1.1 t.1.2 n
  have hsup : ∀ᵐ ζ ∂(R N).P, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ≤ ENNReal.ofReal c * Z ζ := by
    filter_upwards [hall, hCont.2] with ζ hζ hcont
    have hD : ∀ t : Set.Icc (0 : ℝ) S.T, t ∈ D → ‖Rc t.1 ζ‖ₑ ≤ ENNReal.ofReal c * Z ζ :=
      fun t ht => mrr_enorm_le (hnormF (Rc t.1 ζ)) _ (fun n => hζ ⟨t, ht⟩ n)
    have := mrr_closure_enorm D hDd (fun t => Rc t ζ) hcont _ hD
    exact iSup₂_le this
  calc ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R N).P
      ≤ ∫⁻ ζ, ENNReal.ofReal c * Z ζ ∂(R N).P := lintegral_mono_ae hsup
    _ = ENNReal.ofReal c * ∫⁻ ζ, Z ζ ∂(R N).P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + e N)) := by gcongr
    _ = ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) := by
        have h2 : 0 ≤ 𝔈 N + e N := add_nonneg h𝔈 (he N)
        rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul hc0]
        congr 1
        rw [hc]; ring

end PerN

theorem path_remainder_rd_proof (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw C₀ K' : ℝ) (m₀ : ℕ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (m20 : ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      SelectedCommutatorInput S (fd.Gamma : ℝ) T K' C₀ Λ fd.eN →
      Tendsto (fun N => S.sigma N * (𝔈 N + fd.eN N)) atTop (𝓝 0) →
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂(R N).P,
        (R N).X (Real.toNNReal t) ζ ∉ eucCollisionSet d N) →
      ∀ (Rm Rc : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 2 ≤ N → IsRemainderW S R N (fd.Gamma + 2) (Rm N)) →
      (∀ N : ℕ, 2 ≤ N → HasContVersion T (R N).P (Rm N) (Rc N)) →
      (∀ N : ℕ, 2 ≤ N →
        ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc N t ζ‖ₑ ∂(R N).P ≤
          ENNReal.ofReal (C * T * S.sigma N * (𝔈 N + fd.eN N))) ∧
      Tendsto (fun N => C * T * S.sigma N * (𝔈 N + fd.eN N)) atTop (𝓝 0) := by
  refine ⟨max K' 0 / 2, ?_⟩
  intro S hs hT hinv hHolds R 𝔈 m20 hS hPA hsel hsmall hcoll Rm Rc hRem hCont
  subst hT
  refine ⟨fun N hN => ?_, ?_⟩
  · exact mrr_perN (Γ := fd.Gamma) hS hΛ (mrr_eN_nonneg fd) hsel hN (hcoll N (by omega))
      (Rm N) (Rc N) (hRem N hN) (hCont N hN)
  · have h := hsmall.const_mul (max K' 0 / 2 * S.T)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    ring

example := (@path_remainder_rd_proof : type_of% @HRS.Whole.AppendixALemmas.path_remainder_rd)

end HRS.MP.RdRem
