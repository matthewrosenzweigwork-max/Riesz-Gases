import HRS.MS.UniqN3aF

/-!
# N3a, part G: from Schwartz `v` to `v ∈ C²_c` (Schwartz `u`)

Assuming the Schwartz-level identity `hid` (part A), `symbolForm m_q u v = - ∫ u (g * D_q² v)` holds
for Schwartz `u` and `v ∈ C²_c`: both sides are continuous along the mollifications `S_n → v`.
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

theorem integrable_mul_conj {f g : Euc d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun ξ => f ξ * conj (g ξ)) volume := by
  have hP : Integrable (fun ξ => ‖f ξ‖ ^ 2) := hf.norm.integrable_sq
  have hQ : Integrable (fun ξ => ‖g ξ‖ ^ 2) := hg.norm.integrable_sq
  refine Integrable.mono' ((hP.add hQ).div_const 2)
    (hf.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable))
    (Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
  nlinarith [sq_nonneg (‖f ξ‖ - ‖g ξ‖)]

/-- `m û ∈ L²` for Schwartz `u`. -/
theorem memLp_mq_schwartz {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q : Euc d)
    (u : SchwartzMap (Euc d) ℝ) :
    MemLp (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * fourierL2 u ξ) 2 volume := by
  have hmeasm : Measurable fun ξ : Euc d => ((mq c s q ξ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_mq c s q)
  exact (memLp_two_iff_integrable_sq_norm (hmeasm.aestronglyMeasurable.mul
    (aestronglyMeasurable_fourierL2 (u.memLp 2 volume)))).2 (mq_schwartz hc hs2 hsd q u).1

/-- Convergence of the Fourier side along the mollification. -/
theorem lhs_conv {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q : Euc d)
    (u : SchwartzMap (Euc d) ℝ) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    Tendsto (fun n => symbolForm (mq c s q) u (Sn n hv hvc)) atTop
      (𝓝 (symbolForm (mq c s q) u v)) := by
  have hmv : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have hms : ∀ n, MemLp (⇑(Sn n hv hvc)) 2 volume := fun n => (Sn n hv hvc).memLp 2 volume
  have hGu := memLp_mq_schwartz hc hs2 hsd q u
  have hdiff : ∀ n, ‖symbolForm (mq c s q) u (Sn n hv hvc) - symbolForm (mq c s q) u v‖ ≤
      Real.sqrt (∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 u ξ‖ ^ 2) *
        Real.sqrt (∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2) := by
    intro n
    have hal := memLp_fourierL2 (hms n)
    have har := memLp_fourierL2 hmv
    have e : symbolForm (mq c s q) u (Sn n hv hvc) - symbolForm (mq c s q) u v =
        (∫ ξ, (((mq c s q ξ : ℝ) : ℂ) * fourierL2 u ξ) *
          conj (fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ)).re := by
      have i1 := integrable_mul_conj hGu hal
      have i2 := integrable_mul_conj hGu har
      unfold symbolForm
      rw [← Complex.sub_re, ← integral_sub]
      · congr 1; refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [map_sub]; ring
      · exact i1.congr (Eventually.of_forall fun ξ => by simp only; ring)
      · exact i2.congr (Eventually.of_forall fun ξ => by simp only; ring)
    rw [Real.norm_eq_abs, e]
    exact (Complex.abs_re_le_norm _).trans (cs_L2 hGu (hal.sub har))
  have hz : Tendsto (fun n => Real.sqrt (∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 u ξ‖ ^ 2) *
      Real.sqrt (∫ ξ, ‖fourierL2 (Sn n hv hvc) ξ - fourierL2 v ξ‖ ^ 2)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp (a_tendsto hv hvc)).const_mul
      (Real.sqrt (∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 u ξ‖ ^ 2))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hdiff hz

/-- Linearity and bounds for `g * h`, `h` supported in a fixed ball. -/
theorem conv_diff_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (R0 : ℝ) (hR : 0 ≤ R0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h1 h2 : Euc d → ℝ) (M1 M2 η : ℝ), Continuous h1 → Continuous h2 →
      (∀ t, h1 t ≠ 0 → t ∈ closedBall (0 : Euc d) R0) → (∀ t, h2 t ≠ 0 → t ∈ closedBall (0 : Euc d) R0) →
      (∀ t, |h1 t| ≤ M1) → (∀ t, |h2 t| ≤ M2) → (∀ t, |h1 t - h2 t| ≤ η) → ∀ x,
      |HRS.Whole.convFun (rieszKernel d s) h1 x - HRS.Whole.convFun (rieszKernel d s) h2 x| ≤
        η * K * (1 + ‖x‖) := by
  obtain ⟨K, hK0, hK⟩ := conv_bound_unif hs0 hsd R0 hR
  refine ⟨K, hK0, fun h1 h2 M1 M2 η c1 c2 s1 s2 b1 b2 bd x => ?_⟩
  have i1 := (hK h1 M1 c1 s1 b1 x).1
  have i2 := (hK h2 M2 c2 s2 b2 x).1
  have hd : Continuous fun t => h1 t - h2 t := c1.sub c2
  have sd : ∀ t, h1 t - h2 t ≠ 0 → t ∈ closedBall (0 : Euc d) R0 := by
    intro t ht
    by_cases h : h1 t = 0
    · have : h2 t ≠ 0 := fun h' => ht (by rw [h, h']; ring)
      exact s2 t this
    · exact s1 t h
  have := (hK (fun t => h1 t - h2 t) η hd sd bd x).2
  have e : HRS.Whole.convFun (rieszKernel d s) h1 x - HRS.Whole.convFun (rieszKernel d s) h2 x =
      HRS.Whole.convFun (rieszKernel d s) (fun t => h1 t - h2 t) x := by
    unfold HRS.Whole.convFun
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; ring
  rw [e]; exact this

/-- Convergence of the physical side along the mollification (Schwartz `u`). -/
theorem rhs_conv {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (u : SchwartzMap (Euc d) ℝ)
    {f : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {R : ℝ}
    (hsupp : Function.support f ⊆ closedBall 0 R) :
    Tendsto (fun n => ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (mo n f) x) atTop
      (𝓝 (∫ x, u x * HRS.Whole.convFun (rieszKernel d s) f x)) := by
  set R0 : ℝ := max R 0 + 1 with hR0
  have hR00 : 0 ≤ R0 := by positivity
  obtain ⟨K, hK0, hK⟩ := conv_diff_bound hs0 hsd R0 hR00
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ x, |f x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  have hsf : ∀ t, f t ≠ 0 → t ∈ closedBall (0 : Euc d) R0 := fun t ht =>
    closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hsupp ht)
  have hsmo : ∀ n t, mo n f t ≠ 0 → t ∈ closedBall (0 : Euc d) R0 := fun n t ht =>
    closedBall_subset_closedBall (by linarith [le_max_left R 0])
      (mo_supp n hsupp t ht)
  have hcmo : ∀ n, Continuous (mo n f) := fun n => (mo_contDiff n hf).continuous
  obtain ⟨N0, hN0⟩ := mo_unif hf hfc (ε := 1) one_pos
  have hmo1 : ∀ n, N0 ≤ n → ∀ t, |mo n f t| ≤ M + 1 := by
    intro n hn t
    have h1 := hN0 n hn t
    calc |mo n f t| = |(mo n f t - f t) + f t| := by ring_nf
      _ ≤ |mo n f t - f t| + |f t| := abs_add_le _ _
      _ ≤ _ := by linarith [hM' t]
  have hu1 : Integrable (fun x : Euc d => u x) volume := u.integrable
  have hu2 : Integrable (fun x : Euc d => ‖x‖ * u x) volume := (HRS.MS.UniqN0.n0_schwartz_int u).2
  have hbi : Integrable (fun x : Euc d => (M + 1) * K * (|u x| + |‖x‖ * u x|)) volume :=
    (hu1.abs.add hu2.abs).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : Euc d => (M + 1) * K * (|u x| + |‖x‖ * u x|)) ?_ ?_ hbi ?_
  · refine Eventually.of_forall fun n => ?_
    exact u.continuous.aestronglyMeasurable.mul
      (convFun_continuous hs0 hsd (hcmo n) (mo_hasCompactSupport n hfc)).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop N0] with n hn
    refine Eventually.of_forall fun x => ?_
    have := hK (mo n f) (fun _ => 0) (M + 1) 0 (M + 1) (hcmo n) continuous_const (hsmo n)
      (fun t ht => absurd rfl ht) (hmo1 n hn) (fun t => by simp) (fun t => by simpa using hmo1 n hn t) x
    have e0 : HRS.Whole.convFun (rieszKernel d s) (fun _ => (0 : ℝ)) x = 0 := by
      simp [HRS.Whole.convFun]
    rw [e0, sub_zero] at this
    rw [Real.norm_eq_abs, abs_mul]
    calc |u x| * |HRS.Whole.convFun (rieszKernel d s) (mo n f) x|
        ≤ |u x| * ((M + 1) * K * (1 + ‖x‖)) := by gcongr
      _ = (M + 1) * K * (|u x| + |‖x‖ * u x|) := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg x)]; ring
  · refine Eventually.of_forall fun x => ?_
    refine Tendsto.const_mul _ ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    set A : ℝ := K * (1 + ‖x‖) with hA
    have hA0 : 0 ≤ A := by positivity
    set η : ℝ := ε / (A + 1) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨N, hN⟩ := mo_unif hf hfc hη0
    refine ⟨max N N0, fun n hn => ?_⟩
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnN0 : N0 ≤ n := (le_max_right _ _).trans hn
    have := hK (mo n f) f (M + 1) M η (hcmo n) hf (hsmo n) hsf (hmo1 n hnN0) hM'
      (fun t => hN n hnN t) x
    rw [Real.dist_eq]
    refine this.trans_lt ?_
    rw [hη, div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hA0]

end HRS.MS.UniqN3a
