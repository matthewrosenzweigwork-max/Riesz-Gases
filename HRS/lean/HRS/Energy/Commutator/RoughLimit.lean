import HRS.Energy.Commutator.RoughKernel

/-!
# Properties of the slice kernel and force used in the limit `ε → 0` (packet CM-S3 helpers)

Oddness and continuity of `∇𝒢_l` away from the origin, the majorant `|k| ≤ L(A𝒢_l + B)` for the
commutator kernel, its integrability, and the heat-time-shifted energy kernel.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat
  HRS.Commutator.RoughKernel

namespace HRS.Commutator.RoughLimit

variable {d : ℕ}

theorem psiG_neg (j : Fin d) (x : Torus d) (u : ℝ) : psiG j (-x) u = - psiG j x u := by
  unfold psiG
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [KernelGrad.sinMode_neg_arg]
  ring

theorem sgc_neg (j : Fin d) (l : ℝ) (z : Torus d) : SliceAux.sgc j l (-z) = - SliceAux.sgc j l z := by
  unfold SliceAux.sgc
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [psiG_neg]
  ring

theorem sgv_neg (l : ℝ) (z : Torus d) : SliceAux.sgv l (-z) = - SliceAux.sgv l z := by
  ext j
  simp [SliceAux.sgv, sgc_neg]

theorem sliceG_continuousAt {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (sliceG d l) z := by
  have h := EnergyAux.sliceG_continuousAt_lift (d := d) hl (w := Torus.rep z)
    (by rw [Torus.mk_rep]; exact hz)
  have h2 : ContinuousAt (sliceG d l ∘ (Torus.mk : Euc d → Torus d)) (Torus.rep z) := h
  have h3 := (KernelGrad.isOpenQuotientMap_mk.continuousAt_comp_iff).mp h2
  rwa [Torus.mk_rep] at h3

theorem sgc_continuousAt (j : Fin d) {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (SliceAux.sgc j l) z := by
  have hr : 0 < KernelGrad.tdist z 0 / 2 := by have := KernelGrad.tdist_pos hz; positivity
  obtain ⟨M, hM0, hM⟩ := SliceAux.psiG_bound_unif (d := d) j hr
  have hU : ∀ᶠ y in 𝓝 z, KernelGrad.tdist z 0 / 2 ≤ KernelGrad.tdist y 0 := by
    have hc : Continuous fun y : Torus d => KernelGrad.tdist y 0 := CoercAux.continuous_tdist_zero
    have := hc.continuousAt (x := z)
    have h2 : KernelGrad.tdist z 0 / 2 < KernelGrad.tdist z 0 := by
      have := KernelGrad.tdist_pos hz; linarith
    exact (this.eventually (lt_mem_nhds h2)).mono fun y hy => hy.le
  have hb : ∀ᶠ y in 𝓝 z, ∀ t : ℝ, 0 < t →
      |psiG j y (4 * Real.pi ^ 2 * t)| ≤ M * Real.exp (-(4 * Real.pi ^ 2 * t)) := by
    filter_upwards [hU] with y hy t ht
    obtain ⟨c, hc1, hc2⟩ := KernelGrad.exists_mk_box y
    have hcn : KernelGrad.tdist z 0 / 2 ≤ ‖c‖ := by
      rw [← hc1, KernelGrad.tdist_mk hc2] at hy; exact hy
    rw [← hc1]
    exact hM c hc2 hcn _ (by positivity)
  unfold SliceAux.sgc
  refine continuousAt_of_dominated (bound := fun t => Real.exp (-l * t) * (M * Real.exp (-(4 * Real.pi ^ 2 * t))))
    ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (((by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t))).aestronglyMeasurable).mul
      ((SliceAux.measurable_psiG_uncurry j).comp (measurable_const.prodMk
        (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards [hb] with y hy
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hy t ht') (Real.exp_pos _).le
  · have hI : IntegrableOn (fun t : ℝ => M * Real.exp (-((l + 4 * Real.pi ^ 2) * t))) (Ioi 0) :=
      (integrableOn_Ioi_exp_neg _ (by positivity)).const_mul M
    refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only []
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    exact (continuous_const.mul (continuous_psiG j (by positivity : 0 < 4 * Real.pi ^ 2 * t))).continuousAt


/-- `(x,y) ↦ φ(x-y)` is integrable on the torus squared for `φ ∈ L¹`. -/
theorem integrable_sub_prod {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ) :
    Integrable (fun p : Torus d × Torus d => φ (p.1 - p.2))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => φ (p.1 - p.2))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    exact (hφm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · exact hφ.comp_sub_right y
  · have : (fun y : Torus d => ∫ x, ‖φ (x - y)‖) = fun _ => ∫ x, ‖φ x‖ := by
      funext y
      exact integral_sub_right_eq_self (fun x => ‖φ x‖) y
    rw [this]
    exact integrable_const _

/-- The commutator kernel with the force `sgv`. -/
abbrev kk (l : ℝ) (v : Torus d → Euc d) : Torus d → Torus d → ℝ := commKernel (SliceAux.sgv l) v

theorem commKernel_sliceGrad {l : ℝ} (hl : 0 ≤ l) (v : Torus d → Euc d) :
    commKernel (sliceGrad d l) v = kk l v := by
  funext x y
  unfold kk commKernel
  split_ifs with h
  · rfl
  · rw [sliceGrad_eq hl (sub_ne_zero.mpr h)]
    rfl

theorem kk_diag (l : ℝ) (v : Torus d → Euc d) (x : Torus d) : kk l v x x = 0 := by
  simp [kk, commKernel]

theorem kk_symm (l : ℝ) (v : Torus d → Euc d) (x y : Torus d) : kk l v x y = kk l v y x := by
  unfold kk commKernel
  by_cases h : x = y
  · subst h; rfl
  · have h' : ¬ y = x := fun e => h e.symm
    rw [if_neg h, if_neg h']
    have : y - x = -(x - y) := by abel
    rw [this, sgv_neg, inner_neg_right, ← inner_neg_left, neg_sub]

theorem measurable_kk {l : ℝ} {v : Torus d → Euc d} (hv : Continuous v) :
    Measurable (Function.uncurry (kk l v)) := by
  have hvm : Measurable v := hv.measurable
  simp only [Function.uncurry, kk, commKernel]
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hvm.comp measurable_fst).sub (hvm.comp measurable_snd)
  · have := (SliceAux.measurable_sgv (d := d)).comp (measurable_const.prodMk (measurable_fst.sub measurable_snd) :
      Measurable fun p : Torus d × Torus d => (l, p.1 - p.2))
    exact this

theorem sliceG_zero_arg_nonneg (l : ℝ) : 0 ≤ sliceG d l (0 : Torus d) := by
  unfold sliceG
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.exp_pos _).le (CoercAux.psi_zero_nonneg (by have : (0 : ℝ) < t := ht; positivity))

/-- Majorant of the commutator kernel (K1). -/
theorem kk_majorant (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ x y : Torus d, |kk l v x y| ≤ L * (A * sliceG d l (x - y) + B) := by
  obtain ⟨A, B, hA, hB, h⟩ := HeatAux.tdist_grad_le hd hl
  refine ⟨A, B, hA, hB, fun L v hL hv x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    rw [kk_diag, abs_zero, sub_self]
    have := sliceG_zero_arg_nonneg (d := d) l
    positivity
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h1 := h (x - y) hz
    have h2 : ‖SliceAux.sgv l (x - y)‖ = ‖sliceGrad d l (x - y)‖ := by
      rw [sliceGrad_eq hl hz]; rfl
    have h3 : |kk l v x y| ≤ ‖v x - v y‖ * ‖SliceAux.sgv l (x - y)‖ := by
      simp only [kk, commKernel, hxy, if_false]
      exact abs_real_inner_le_norm _ _
    have h4 : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := by
      unfold KernelGrad.tdist; rw [sub_zero]
    calc |kk l v x y| ≤ ‖v x - v y‖ * ‖SliceAux.sgv l (x - y)‖ := h3
      _ ≤ (L * KernelGrad.tdist x y) * ‖SliceAux.sgv l (x - y)‖ :=
          mul_le_mul_of_nonneg_right (hv x y) (norm_nonneg _)
      _ = L * (KernelGrad.tdist (x - y) 0 * ‖sliceGrad d l (x - y)‖) := by rw [h2, h4]; ring
      _ ≤ L * (A * sliceG d l (x - y) + B) := mul_le_mul_of_nonneg_left h1 hL


theorem sgv_continuousAt {l : ℝ} (hl : 0 ≤ l) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (SliceAux.sgv l) z := by
  unfold SliceAux.sgv
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).continuousAt.comp
    (continuousAt_pi.mpr fun j => sgc_continuousAt j hl hz)

theorem kk_continuousAt {l : ℝ} (hl : 0 ≤ l) {v : Torus d → Euc d} (hv : Continuous v) {y z : Torus d}
    (hyz : y ≠ z) : ContinuousAt (fun p : Torus d × Torus d => kk l v p.1 p.2) (y, z) := by
  have hopen : IsOpen {p : Torus d × Torus d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hev : ∀ᶠ p in 𝓝 (y, z), p.1 ≠ p.2 := hopen.mem_nhds hyz
  have hz : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have h1 : ContinuousAt (fun p : Torus d × Torus d => SliceAux.sgv l (p.1 - p.2)) (y, z) :=
    ContinuousAt.comp (f := fun p : Torus d × Torus d => p.1 - p.2) (x := (y, z))
      (g := SliceAux.sgv l) (sgv_continuousAt hl hz) (continuous_fst.sub continuous_snd).continuousAt
  have h2 : ContinuousAt (fun p : Torus d × Torus d => inner ℝ (v p.1 - v p.2) (SliceAux.sgv l (p.1 - p.2))) (y, z) :=
    ContinuousAt.inner (((hv.comp continuous_fst).sub (hv.comp continuous_snd)).continuousAt) h1
  refine h2.congr ?_
  filter_upwards [hev] with p hp
  simp [kk, commKernel, hp]

/-- Integrability of the commutator kernel on the torus squared. -/
theorem integrable_kk (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) :
    Integrable (fun p : Torus d × Torus d => kk l v p.1 p.2)
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
  obtain ⟨A, B, hA, hB, h⟩ := kk_majorant hd hl
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have hmaj : Integrable (fun p : Torus d × Torus d => L * (A * sliceG d l (p.1 - p.2) + B))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    have h1 : Integrable (fun w : Torus d => L * (A * sliceG d l w + B)) :=
      (((integrable_sliceG hl).const_mul A).add (integrable_const B)).const_mul L
    exact integrable_sub_prod (((EnergyAux.measurable_sliceG l).const_mul A).add measurable_const |>.const_mul L) h1
  refine Integrable.mono' hmaj (measurable_kk hvc).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact h L v hL hv p.1 p.2


/-! ### The heat-time-shifted energy kernel -/

/-- `Ê_ε = e^{2lε} ser(cW l (2ε)) = 𝒢_l^{full} ⋆ hk_{2ε}`. -/
def Ehat (l ε : ℝ) (w : Torus d) : ℝ := Real.exp (2 * l * ε) * ser (cW l (2 * ε)) w

/-- The time integrand of `𝒢_l` at `w` is integrable. -/
def IntW (l : ℝ) (w : Torus d) : Prop :=
  IntegrableOn (fun t : ℝ => Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t)) (Ioi 0)

theorem intW_of_ne_zero {l : ℝ} (hl : 0 ≤ l) {w : Torus d} (hw : w ≠ 0) : IntW l w :=
  SliceAux.integrableOn_slice_psi hl hw

theorem Ehat_eq {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (w : Torus d) :
    Ehat l ε w = Real.exp (2 * l * ε) * (∫ t in Ioi (2 * ε), Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t)) +
      1 / l := by
  unfold Ehat
  rw [ser_cW_eq hl (by positivity : 0 < 2 * ε) w, mul_add]
  congr 1
  by_cases hl0 : l = 0
  · simp [hl0]
  · rw [mul_div_assoc', ← Real.exp_add]
    have : 2 * l * ε + -(l * (2 * ε)) = 0 := by ring
    rw [this]; simp

theorem Ehat_neg (l ε : ℝ) (w : Torus d) : Ehat l ε (-w) = Ehat l ε w := by
  unfold Ehat; rw [ser_neg]

theorem sliceGfull_eq_of_intW {l : ℝ} (hl : 0 ≤ l) {w : Torus d} (hw : IntW l w) :
    sliceGfull d l w = (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t)) + 1 / l := rfl

theorem measurable_timeInt (l : ℝ) (w : Torus d) :
    Measurable fun t : ℝ => Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) :=
  (by fun_prop : Measurable fun t : ℝ => Real.exp (-l * t)).mul
    (EnergyAux.measurable_psiFn_uncurry.comp (measurable_const.prodMk (measurable_const.mul measurable_id)))

theorem tendsto_tail_integral (f : ℝ → ℝ) (hfm : Measurable f) (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (2 * ε), f t) (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (0 : ℝ), f t)) := by
  have hfi : Integrable ((Ioi (0 : ℝ)).indicator f) := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have e : ∀ ε : ℝ, ∫ t in Ioi (2 * ε), f t = ∫ t, (Ioi (2 * ε)).indicator f t := fun ε =>
    (integral_indicator measurableSet_Ioi).symm
  simp_rw [e]
  rw [← integral_indicator measurableSet_Ioi]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖(Ioi (0 : ℝ)).indicator f t‖) ?_ ?_
    hfi.norm ?_
  · exact Filter.Eventually.of_forall fun ε => (hfm.indicator measurableSet_Ioi).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Filter.Eventually.of_forall fun t => ?_
    have hε' : (0 : ℝ) < ε := hε
    by_cases ht : t ∈ Ioi (2 * ε)
    · have ht0 : t ∈ Ioi (0 : ℝ) := by
        simp only [mem_Ioi] at ht ⊢; linarith
      simp [indicator, ht, ht0]
    · simp [indicator, ht]
  · refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : (0 : ℝ) < t
    · have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (Ioi (2 * ε)).indicator f t = (Ioi (0 : ℝ)).indicator f t := by
        have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 2 * ε < t := by
          have : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 (2 * 0)) := (continuous_const.mul continuous_id).tendsto 0
          rw [mul_zero] at this
          exact this.eventually (gt_mem_nhds ht)
        filter_upwards [nhdsWithin_le_nhds h1] with ε hε
        simp [indicator, hε, ht]
      exact tendsto_const_nhds.congr' (this.mono fun ε h => h.symm)
    · have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (Ioi (2 * ε)).indicator f t = (Ioi (0 : ℝ)).indicator f t := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0 : ℝ) < ε := hε
        have h1 : t ∉ Ioi (2 * ε) := by simp only [mem_Ioi, not_lt]; linarith [not_lt.mp ht]
        have h2 : t ∉ Ioi (0 : ℝ) := by simpa using ht
        simp [indicator, h1, h2]
      exact tendsto_const_nhds.congr' (this.mono fun ε h => h.symm)

theorem Ehat_tendsto {l : ℝ} (hl : 0 ≤ l) {w : Torus d} (hw : IntW l w) :
    Tendsto (fun ε => Ehat l ε w) (𝓝[>] (0 : ℝ)) (𝓝 (sliceGfull d l w)) := by
  have hI := tendsto_tail_integral _ (measurable_timeInt l w) hw
  have hE : Tendsto (fun ε : ℝ => Real.exp (2 * l * ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => Real.exp (2 * l * ε)) (𝓝 0) (𝓝 (Real.exp (2 * l * 0))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, Real.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (hE.mul hI).add_const (1 / l)
  rw [one_mul] at h2
  refine (show sliceGfull d l w = (∫ t in Ioi (0:ℝ), Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t)) + 1 / l
    from rfl) ▸ h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (Ehat_eq hl hε w).symm


theorem integrableOn_exp_neg_mul_Ioi {l : ℝ} (hl : 0 < l) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi c) := by
  have := integrableOn_exp_Ioi hl c
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [neg_mul]

theorem tail_split {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Ioi (0 : ℝ), f t = (∫ t in Ioc (0 : ℝ) a, f t) + ∫ t in Ioi a, f t := by
  have hunion : Ioc (0 : ℝ) a ∪ Ioi a = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi ha
  conv_lhs => rw [← hunion]
  exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
      simp only [mem_Ioc, mem_Ioi] at hx hx'; linarith [hx.2]) measurableSet_Ioi
    (hf.mono_set (by rw [← hunion]; exact subset_union_left))
    (hf.mono_set (by rw [← hunion]; exact subset_union_right))

theorem Ehat_upper {l : ℝ} (hl : 0 ≤ l) {w : Torus d} (hw : IntW l w) {ε : ℝ} (hε : 0 < ε) :
    Ehat l ε w ≤ Real.exp (2 * l * ε) * sliceGfull d l w + 2 * ε := by
  set f : ℝ → ℝ := fun t => Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) with hf
  have hint : IntegrableOn f (Ioi 0) := hw
  have hS : sliceGfull d l w = (∫ t in Ioi (0 : ℝ), f t) + 1 / l := rfl
  rw [Ehat_eq hl hε w, hS]
  show Real.exp (2 * l * ε) * (∫ t in Ioi (2 * ε), f t) + 1 / l ≤
    Real.exp (2 * l * ε) * ((∫ t in Ioi (0 : ℝ), f t) + 1 / l) + 2 * ε
  by_cases hl0 : l = 0
  · subst hl0
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul, div_zero, add_zero]
    have h1 := tail_split hint (by linarith : (0 : ℝ) ≤ 2 * ε)
    have h2 : -(2 * ε) ≤ ∫ t in Ioc (0 : ℝ) (2 * ε), f t := by
      have hc : IntegrableOn (fun _ : ℝ => (-1 : ℝ)) (Ioc 0 (2 * ε)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have := setIntegral_mono_on hc (hint.mono_set Ioc_subset_Ioi_self)
        measurableSet_Ioc (fun t ht => by
          have ht' : (0 : ℝ) < t := ht.1
          have := EnergyAux.one_add_psiFn_nonneg' w (by positivity : 0 < 4 * Real.pi ^ 2 * t)
          simp only [hf, neg_zero, zero_mul, Real.exp_zero, one_mul]
          linarith)
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)] at this
      simp only [smul_eq_mul] at this
      linarith
    linarith
  · have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
    set g : ℝ → ℝ := fun t => Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) with hg
    have hgf : ∀ t, g t = f t + Real.exp (-l * t) := fun t => by simp only [hg, hf]; ring
    have hgn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := fun t ht =>
      mul_nonneg (Real.exp_pos _).le (EnergyAux.one_add_psiFn_nonneg' w (by have : (0 : ℝ) < t := ht; positivity))
    have hE0 := integrableOn_exp_neg_mul_Ioi hlp 0
    have hg0 : IntegrableOn g (Ioi 0) := by
      have := hint.add hE0
      exact this.congr_fun (fun t _ => (hgf t).symm) measurableSet_Ioi
    have hexp : ∀ c : ℝ, ∫ t in Ioi c, Real.exp (-l * t) = Real.exp (-(l * c)) / l := fun c => by
      have := integral_exp_Ioi hlp c
      simpa [neg_mul] using this
    have hg2 : ∫ t in Ioi (2 * ε), g t = (∫ t in Ioi (2 * ε), f t) + Real.exp (-(l * (2 * ε))) / l := by
      simp_rw [hgf]
      rw [integral_add (hint.mono_set (Ioi_subset_Ioi (by linarith))) (hE0.mono_set (Ioi_subset_Ioi (by linarith))),
        hexp]
    have hg0' : ∫ t in Ioi (0 : ℝ), g t = (∫ t in Ioi (0 : ℝ), f t) + 1 / l := by
      simp_rw [hgf]
      rw [integral_add hint hE0, hexp]
      simp
    have hmono : ∫ t in Ioi (2 * ε), g t ≤ ∫ t in Ioi (0 : ℝ), g t :=
      setIntegral_mono_set hg0 (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hgn t ht)
        (Eventually.of_forall (Ioi_subset_Ioi (by linarith)))
    have hE : Real.exp (2 * l * ε) * (Real.exp (-(l * (2 * ε))) / l) = 1 / l := by
      rw [mul_div_assoc', ← Real.exp_add]
      have : 2 * l * ε + -(l * (2 * ε)) = 0 := by ring
      rw [this]; simp
    have hpos : 0 < Real.exp (2 * l * ε) := Real.exp_pos _
    have hkey : Real.exp (2 * l * ε) * (∫ t in Ioi (2 * ε), f t) + 1 / l =
        Real.exp (2 * l * ε) * ∫ t in Ioi (2 * ε), g t := by
      rw [hg2, mul_add, hE]
    rw [hkey]
    have := mul_le_mul_of_nonneg_left hmono hpos.le
    rw [hg0'] at this
    linarith


theorem Ehat_eq_g {l : ℝ} (hlp : 0 < l) {w : Torus d} (hw : IntW l w) {ε : ℝ} (hε : 0 < ε) :
    Ehat l ε w = Real.exp (2 * l * ε) *
      ∫ t in Ioi (2 * ε), Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) := by
  set f : ℝ → ℝ := fun t => Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) with hf
  have hint : IntegrableOn f (Ioi 0) := hw
  have hE0 := integrableOn_exp_neg_mul_Ioi hlp 0
  have hexp : ∀ c : ℝ, ∫ t in Ioi c, Real.exp (-l * t) = Real.exp (-(l * c)) / l := fun c => by
    have := integral_exp_Ioi hlp c
    simpa [neg_mul] using this
  have hgf : ∀ t, Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) = f t + Real.exp (-l * t) :=
    fun t => by simp only [hf]; ring
  rw [Ehat_eq hlp.le hε w]
  simp_rw [hgf]
  rw [integral_add (hint.mono_set (Ioi_subset_Ioi (by linarith))) (hE0.mono_set (Ioi_subset_Ioi (by linarith))),
    hexp, mul_add]
  have hE : Real.exp (2 * l * ε) * (Real.exp (-(l * (2 * ε))) / l) = 1 / l := by
    rw [mul_div_assoc', ← Real.exp_add]
    have : 2 * l * ε + -(l * (2 * ε)) = 0 := by ring
    rw [this]; simp
  rw [hE]

theorem Ehat_lower (d : ℕ) : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (l : ℝ), 0 ≤ l → ∀ w : Torus d, IntW l w →
    ∀ ε : ℝ, 0 < ε → -Kc ≤ Ehat l ε w := by
  obtain ⟨K, hK0, hK⟩ := EnergyAux.psiFn_ge_neg_exp d
  refine ⟨K / (4 * Real.pi ^ 2), by positivity, fun l hl w hw ε hε => ?_⟩
  by_cases hl0 : l = 0
  · subst hl0
    rw [Ehat_eq le_rfl hε w]
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul, div_zero, add_zero]
    have hint : IntegrableOn (fun t : ℝ => Real.exp (-0 * t) * psiFn w (4 * Real.pi ^ 2 * t)) (Ioi (2 * ε)) :=
      (hw : IntW 0 w).mono_set (Ioi_subset_Ioi (by linarith))
    have hE : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi (2 * ε)) :=
      (integrableOn_exp_Ioi (by positivity) _).const_mul K
    have h1 : ∫ t in Ioi (2 * ε), -(K * Real.exp (-(4 * Real.pi ^ 2 * t))) ≤
        ∫ t in Ioi (2 * ε), Real.exp (-0 * t) * psiFn w (4 * Real.pi ^ 2 * t) :=
      setIntegral_mono_on hE.neg hint measurableSet_Ioi (fun t ht => by
        have ht' : (2 * ε) < t := ht
        have ht0 : 0 < t := by linarith
        have := hK w (4 * Real.pi ^ 2 * t) (by positivity)
        simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
        linarith)
    rw [integral_neg, integral_const_mul, integral_exp_Ioi (by positivity)] at h1
    have h2 : K * (Real.exp (-(4 * Real.pi ^ 2 * (2 * ε))) / (4 * Real.pi ^ 2)) ≤ K / (4 * Real.pi ^ 2) := by
      rw [← mul_div_assoc]
      have h3 : Real.exp (-(4 * Real.pi ^ 2 * (2 * ε))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left h3 hK0]) (by positivity)
    linarith
  · have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
    rw [Ehat_eq_g hlp hw hε]
    have : 0 ≤ Real.exp (2 * l * ε) * ∫ t in Ioi (2 * ε), Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) :=
      mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.exp_pos _).le (EnergyAux.one_add_psiFn_nonneg' w (by
          have : (2 * ε) < t := ht
          have ht0 : 0 < t := by linarith
          positivity)))
    have : 0 ≤ K / (4 * Real.pi ^ 2) := by positivity
    linarith

end HRS.Commutator.RoughLimit
