import HRS.MP.SelfSimP4Jensen

/-!
# MP-SSP4MOLLSC: `p4_mollify_lsc` (lower semicontinuity of the entropy and of the Fisher information under
the Gaussian mollification)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4m_`.  Theorem `p4_mollify_lsc_proof`, tied to
`HRS.MP.SelfSimP4.p4_mollify_lsc`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory Set
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-! ### The mollified measures and their narrow convergence -/

/-- The measure `u_v dx` with `u_v = G_v * μ`. -/
def p4m_molMeas (v : ℝ) (μ : Measure (EucConfig d N)) : Measure (EucConfig d N) :=
  (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (p4Mol v μ x))

theorem p4m_molMeas_prob {v : ℝ} (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (p4m_molMeas v μ) := by
  refine ⟨?_⟩
  unfold p4m_molMeas
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact p4j_mol_lintegral_one hv μ

/-- Approximate identity `∫ G_v(z) f(y + z) dz → f(y)` as `v → 0`. -/
theorem p4m_mollify_tendsto {f : EucConfig d N → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    (y : EucConfig d N) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (hv0 : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, p4Gauss d N (v n) z * f (y + z)) atTop (𝓝 (f y)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [Metric.tendsto_atTop]
  intro η hη
  have hfc := hf.continuousAt (x := y)
  rw [Metric.continuousAt_iff] at hfc
  obtain ⟨δ, hδ, hδf⟩ := hfc (η / 2) (by positivity)
  set c : ℝ := 2 * C / δ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hmain : ∀ n, |(∫ z, p4Gauss d N (v n) z * f (y + z)) - f y| ≤
      η / 2 + c * p4j_m d N (v n) := by
    intro n
    have hvn := hv n
    have hgi := p4j_integrable_gauss (d := d) (N := N) hvn
    have hfi : Integrable (fun z : EucConfig d N => p4Gauss d N (v n) z * f (y + z)) := by
      refine Integrable.mono' (hgi.mul_const C) ?_ (ae_of_all _ fun z => ?_)
      · exact ((p4j_gauss_continuous _).mul (hf.comp (continuous_const.add continuous_id))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (p4j_gauss_pos hvn z)]
        exact mul_le_mul_of_nonneg_left (hC _) (p4j_gauss_pos hvn z).le
    have e : (∫ z, p4Gauss d N (v n) z * f (y + z)) - f y =
        ∫ z, p4Gauss d N (v n) z * (f (y + z) - f y) := by
      have h1 : ∫ z, p4Gauss d N (v n) z * (f (y + z) - f y) =
          (∫ z, p4Gauss d N (v n) z * f (y + z)) - ∫ z : EucConfig d N, p4Gauss d N (v n) z * f y := by
        rw [← integral_sub hfi (hgi.mul_const _)]
        exact integral_congr_ae (ae_of_all _ fun z => by simp only [mul_sub])
      rw [h1, integral_mul_const, p4j_integral_gauss hvn, one_mul]
    rw [e]
    have hb : ∀ z : EucConfig d N, |f (y + z) - f y| ≤ η / 2 + c * p4j_Phi z := by
      intro z
      have hP := p4j_Phi_nonneg z
      have hPn := p4j_norm_sq_le_Phi z
      by_cases hz : ‖z‖ < δ
      · have := hδf (x := y + z) (by simpa [dist_eq_norm] using hz)
        rw [Real.dist_eq] at this
        have : 0 ≤ c * p4j_Phi z := by positivity
        linarith
      · push_neg at hz
        have h1 : |f (y + z) - f y| ≤ 2 * C := by
          calc |f (y + z) - f y| ≤ |f (y + z)| + |f y| := abs_sub _ _
            _ ≤ C + C := add_le_add (hC _) (hC _)
            _ = 2 * C := by ring
        have h2 : 2 * C ≤ c * p4j_Phi z := by
          rw [hc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have : δ ^ 2 ≤ p4j_Phi z := (pow_le_pow_left₀ hδ.le hz 2).trans hPn
          exact mul_le_mul_of_nonneg_left this (by positivity)
        linarith
    have hbi : Integrable (fun z : EucConfig d N => p4Gauss d N (v n) z * (η / 2 + c * p4j_Phi z)) := by
      have := (hgi.const_mul (η / 2)).add ((p4j_integrable_gauss_Phi hvn).const_mul c)
      refine this.congr (ae_of_all _ fun z => ?_)
      simp only [Pi.add_apply]; ring
    have hbv : ∫ z : EucConfig d N, p4Gauss d N (v n) z * (η / 2 + c * p4j_Phi z) =
        η / 2 + c * p4j_m d N (v n) := by
      have : ∀ z : EucConfig d N, p4Gauss d N (v n) z * (η / 2 + c * p4j_Phi z) =
          η / 2 * p4Gauss d N (v n) z + c * (p4Gauss d N (v n) z * p4j_Phi z) := fun z => by ring
      simp_rw [this]
      rw [integral_add (hgi.const_mul _) ((p4j_integrable_gauss_Phi hvn).const_mul _), integral_const_mul,
        integral_const_mul, p4j_integral_gauss hvn]
      unfold p4j_m
      ring
    calc |∫ z, p4Gauss d N (v n) z * (f (y + z) - f y)|
        ≤ ∫ z, |p4Gauss d N (v n) z * (f (y + z) - f y)| := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun z => p4Gauss d N (v n) z * (f (y + z) - f y))
      _ ≤ ∫ z, p4Gauss d N (v n) z * (η / 2 + c * p4j_Phi z) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hbi (ae_of_all _ fun z => ?_)
          show |p4Gauss d N (v n) z * (f (y + z) - f y)| ≤ _
          rw [abs_mul, abs_of_pos (p4j_gauss_pos (hv n) z)]
          exact mul_le_mul_of_nonneg_left (hb z) (p4j_gauss_pos (hv n) z).le
      _ = η / 2 + c * p4j_m d N (v n) := hbv
  have hsmall : ∀ᶠ n in atTop, c * p4j_m d N (v n) < η / 2 := by
    have : Tendsto (fun n => c * p4j_m d N (v n)) atTop (𝓝 (c * (0 * p4j_m d N 1))) := by
      have h1 : Tendsto (fun n => v n * p4j_m d N 1) atTop (𝓝 (0 * p4j_m d N 1)) :=
        hv0.mul_const _
      refine (h1.const_mul c).congr fun n => ?_
      rw [p4j_m_scaling (hv n)]
    rw [zero_mul, mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hsmall
  refine ⟨n0, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have := hmain n
  have := hn0 n hn
  linarith

theorem p4m_molMeas_inner {v : ℝ} (hv : 0 < v) {ψ : EucConfig d N → ℝ} (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ z, |ψ z| ≤ C) (y : EucConfig d N) :
    ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (ψ (y + w) + C) =
      ENNReal.ofReal ((∫ z, p4Gauss d N v z * ψ (y + z)) + C) := by
  have hgi := p4j_integrable_gauss (d := d) (N := N) hv
  have hnn : ∀ z : EucConfig d N, 0 ≤ ψ (y + z) + C := fun z => by linarith [(abs_le.1 (hC (y + z))).1]
  have hf : Integrable (fun z : EucConfig d N => p4Gauss d N v z * (ψ (y + z) + C)) := by
    refine Integrable.mono' (hgi.mul_const (2 * C)) ?_ (ae_of_all _ fun z => ?_)
    · exact ((p4j_gauss_continuous _).mul ((hψ.comp (continuous_const.add continuous_id)).add
        continuous_const)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (p4j_gauss_pos hv z).le (hnn z))]
      refine mul_le_mul_of_nonneg_left ?_ (p4j_gauss_pos hv z).le
      linarith [(abs_le.1 (hC (y + z))).2]
  have hψi : Integrable (fun z : EucConfig d N => p4Gauss d N v z * ψ (y + z)) := by
    refine Integrable.mono' (hgi.mul_const C) ?_ (ae_of_all _ fun z => ?_)
    · exact ((p4j_gauss_continuous _).mul (hψ.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (p4j_gauss_pos hv z)]
      exact mul_le_mul_of_nonneg_left (hC _) (p4j_gauss_pos hv z).le
  have e : ∀ z : EucConfig d N, ENNReal.ofReal (p4Gauss d N v z) * ENNReal.ofReal (ψ (y + z) + C) =
      ENNReal.ofReal (p4Gauss d N v z * (ψ (y + z) + C)) := fun z =>
    (ENNReal.ofReal_mul (p4j_gauss_pos hv z).le).symm
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hf
    (ae_of_all _ fun z => mul_nonneg (p4j_gauss_pos hv z).le (hnn z))]
  congr 1
  have : ∀ z : EucConfig d N, p4Gauss d N v z * (ψ (y + z) + C) =
      p4Gauss d N v z * ψ (y + z) + C * p4Gauss d N v z := fun z => by ring
  simp_rw [this]
  rw [integral_add hψi (hgi.const_mul C), integral_const_mul, p4j_integral_gauss hv, mul_one]

/-- Narrow convergence of the mollified measures. -/
theorem p4m_molMeas_tendsto (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] {v : ℕ → ℝ}
    (hv : ∀ n, 0 < v n) (hv0 : Tendsto v atTop (𝓝 0)) {ψ : EucConfig d N → ℝ} (hψ : Continuous ψ)
    {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) :
    Tendsto (fun n => ∫ z, ψ z ∂(p4m_molMeas (v n) μ)) atTop (𝓝 (∫ z, ψ z ∂μ)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hnn : ∀ z : EucConfig d N, 0 ≤ ψ z + C := fun z => by linarith [(abs_le.1 (hC z)).1]
  set w : EucConfig d N → ℝ≥0∞ := fun x => ENNReal.ofReal (ψ x + C) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp (hψ.add continuous_const).measurable
  have h1 : ∀ n, ∫⁻ x, w x ∂(p4m_molMeas (v n) μ) =
      ∫⁻ y, ENNReal.ofReal ((∫ z, p4Gauss d N (v n) z * ψ (y + z)) + C) ∂μ := by
    intro n
    unfold p4m_molMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (p4Mol (v n) μ x))
      (ENNReal.measurable_ofReal.comp (p4j_mol_continuous (hv n) μ).measurable) hwm]
    simp only [Pi.mul_apply]
    rw [p4j_transport (hv n) μ hwm]
    refine lintegral_congr fun y => ?_
    exact p4m_molMeas_inner (hv n) hψ hC y
  have h2 : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal ((∫ z, p4Gauss d N (v n) z * ψ (y + z)) + C) ∂μ)
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (ψ y + C) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (2 * C)) ?_ ?_ ?_ ?_
    · intro n
      refine ENNReal.measurable_ofReal.comp ?_
      have : Measurable fun y : EucConfig d N => ∫ z, p4Gauss d N (v n) z * ψ (y + z) := by
        have hc : Continuous (Function.uncurry fun (y : EucConfig d N) (z : EucConfig d N) =>
            p4Gauss d N (v n) z * ψ (y + z)) :=
          ((p4j_gauss_continuous _).comp continuous_snd).mul (hψ.comp (continuous_fst.add continuous_snd))
        exact (hc.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
      exact this.add_const C
    · intro n
      refine Eventually.of_forall fun y => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hgi := p4j_integrable_gauss (d := d) (N := N) (hv n)
      have : |∫ z, p4Gauss d N (v n) z * ψ (y + z)| ≤ C := by
        calc |∫ z, p4Gauss d N (v n) z * ψ (y + z)|
            ≤ ∫ z, |p4Gauss d N (v n) z * ψ (y + z)| := by
              simpa [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (fun z => p4Gauss d N (v n) z * ψ (y + z))
          _ ≤ ∫ z, p4Gauss d N (v n) z * C := by
              refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (hgi.mul_const C)
                (ae_of_all _ fun z => ?_)
              show |p4Gauss d N (v n) z * ψ (y + z)| ≤ _
              rw [abs_mul, abs_of_pos (p4j_gauss_pos (hv n) z)]
              exact mul_le_mul_of_nonneg_left (hC _) (p4j_gauss_pos (hv n) z).le
          _ = C := by rw [integral_mul_const, p4j_integral_gauss (hv n), one_mul]
      linarith [(abs_le.1 this).2]
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · refine Eventually.of_forall fun y => ?_
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((p4m_mollify_tendsto hψ hC y hv hv0).add_const C)
  have hconv : ∀ (ρ : Measure (EucConfig d N)) [IsProbabilityMeasure ρ],
      ∫⁻ x, w x ∂ρ = ENNReal.ofReal (∫ z, ψ z ∂ρ + C) := by
    intro ρ _
    have hi : Integrable ψ ρ := Integrable.of_bound hψ.aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)
    have := ofReal_integral_eq_lintegral_ofReal (f := fun x => ψ x + C) (hi.add (integrable_const C))
      (ae_of_all _ hnn)
    simp only [hw]
    rw [← this, integral_add hi (integrable_const C)]
    simp
  haveI : ∀ n, IsProbabilityMeasure (p4m_molMeas (v n) μ) := fun n => p4m_molMeas_prob (hv n) μ
  have h3 : Tendsto (fun n => ENNReal.ofReal (∫ z, ψ z ∂(p4m_molMeas (v n) μ) + C)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, ψ z ∂μ + C))) := by
    have := h2
    simp_rw [← h1, hconv] at this
    rwa [hconv μ] at this
  have h4 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h3
  have e : ∀ (ρ : Measure (EucConfig d N)) [IsProbabilityMeasure ρ],
      (ENNReal.ofReal (∫ z, ψ z ∂ρ + C)).toReal = ∫ z, ψ z ∂ρ + C := by
    intro ρ _
    rw [ENNReal.toReal_ofReal]
    have hi : Integrable ψ ρ := Integrable.of_bound hψ.aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)
    have := integral_mono (integrable_const (-C)) hi (fun z => (abs_le.1 (hC z)).1)
    simp at this
    linarith
  simp only [Function.comp_def, e] at h4
  simpa using h4.sub_const C

/-! ### Compactification of `ℝ^{dN}` into a cube and lower semicontinuity of `klDiv` -/

/-- The compact target. -/
abbrev P4MCube (d N : ℕ) := (Fin N × Fin d) → Icc (-1 : ℝ) 1

/-- Squashing `ℝ → [-1,1]`. -/
def p4m_sq (x : ℝ) : Icc (-1 : ℝ) 1 :=
  ⟨x / (1 + |x|), by
    have h : 0 < 1 + |x| := by positivity
    have h1 : |x / (1 + |x|)| ≤ 1 := by
      rw [abs_div, abs_of_pos h, div_le_one h]; linarith
    exact abs_le.1 h1⟩

theorem p4m_continuous_sq : Continuous p4m_sq := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_id.div (continuous_const.add continuous_abs) fun x => by positivity

/-- Inverse of the squashing on `(-1,1)`. -/
def p4m_isq (y : Icc (-1 : ℝ) 1) : ℝ := (y : ℝ) / (1 - |(y : ℝ)|)

theorem p4m_isq_sq (x : ℝ) : p4m_isq (p4m_sq x) = x := by
  unfold p4m_isq p4m_sq
  simp only
  have h : 0 < 1 + |x| := by positivity
  have h2 : 1 - |x / (1 + |x|)| = 1 / (1 + |x|) := by
    rw [abs_div, abs_of_pos h]; field_simp; ring
  rw [h2]
  field_simp

/-- The coordinatewise embedding. -/
def p4m_pi (x : EucConfig d N) : P4MCube d N := fun k => p4m_sq (x k.1 k.2)

theorem p4m_continuous_pi : Continuous (p4m_pi : EucConfig d N → P4MCube d N) := by
  refine continuous_pi fun k => p4m_continuous_sq.comp ?_
  exact (EuclideanSpace.proj k.2).continuous.comp (continuous_apply k.1)

/-- Left inverse of the embedding. -/
def p4m_pinv (a : P4MCube d N) : EucConfig d N :=
  fun i => WithLp.toLp 2 fun j => p4m_isq (a (i, j))

theorem p4m_measurable_pinv : Measurable (p4m_pinv : P4MCube d N → EucConfig d N) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun j => ?_
  unfold p4m_isq
  have hy : Measurable fun a : P4MCube d N => ((a (i, j) : Icc (-1 : ℝ) 1) : ℝ) :=
    measurable_subtype_coe.comp (measurable_pi_apply (i, j))
  exact hy.div (measurable_const.sub hy.abs)

theorem p4m_pinv_pi (x : EucConfig d N) : p4m_pinv (p4m_pi x) = x := by
  funext i
  ext j
  simp [p4m_pinv, p4m_pi, p4m_isq_sq]

theorem p4m_map_pinv_pi (μ : Measure (EucConfig d N)) : (μ.map p4m_pi).map p4m_pinv = μ := by
  rw [Measure.map_map p4m_measurable_pinv p4m_continuous_pi.measurable]
  have : (p4m_pinv ∘ p4m_pi : EucConfig d N → EucConfig d N) = id := funext p4m_pinv_pi
  rw [this, Measure.map_id]

/-- Pushing forward by the embedding does not change `klDiv`. -/
theorem p4m_klDiv_map_pi (μ ν : Measure (EucConfig d N)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = klDiv (μ.map p4m_pi) (ν.map p4m_pi) := by
  refine le_antisymm ?_ (klDiv_map_le μ ν p4m_continuous_pi.measurable)
  have h := klDiv_map_le (μ.map p4m_pi) (ν.map p4m_pi) p4m_measurable_pinv
  rwa [p4m_map_pinv_pi μ, p4m_map_pinv_pi ν] at h

/-- Lower semicontinuity of `klDiv` along narrowly convergent sequences, with a fixed reference. -/
theorem p4m_klDiv_liminf {μ ν : Measure (EucConfig d N)} {μn : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [∀ n, IsProbabilityMeasure (μn n)]
    (hconv : ∀ ψ : EucConfig d N → ℝ, Continuous ψ → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(μn n)) atTop (𝓝 (∫ z, ψ z ∂μ))) :
    klDiv μ ν ≤ liminf (fun n => klDiv (μn n) ν) atTop := by
  haveI : IsProbabilityMeasure (μ.map p4m_pi) :=
    (Measure.isProbabilityMeasure_map_iff p4m_continuous_pi.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (ν.map p4m_pi) :=
    (Measure.isProbabilityMeasure_map_iff p4m_continuous_pi.aemeasurable).2 inferInstance
  haveI : ∀ n, IsProbabilityMeasure ((μn n).map p4m_pi) := fun n =>
    (Measure.isProbabilityMeasure_map_iff p4m_continuous_pi.aemeasurable).2 inferInstance
  have hP : ∀ φ : P4MCube d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂((μn n).map p4m_pi)) atTop (𝓝 (∫ x, φ x ∂(μ.map p4m_pi))) := by
    intro φ hφ
    have hc : Continuous (φ ∘ p4m_pi) := hφ.comp p4m_continuous_pi
    have hb : ∃ C, ∀ z, |(φ ∘ p4m_pi) z| ≤ C := by
      obtain ⟨C, hC⟩ := (isCompact_univ (X := P4MCube d N)).exists_bound_of_continuousOn hφ.continuousOn
      exact ⟨C, fun z => by simpa using hC (p4m_pi z) (mem_univ _)⟩
    have := hconv (φ ∘ p4m_pi) hc hb
    have e : ∀ m : Measure (EucConfig d N), ∫ x, φ x ∂(m.map p4m_pi) = ∫ z, (φ ∘ p4m_pi) z ∂m := fun m =>
      integral_map p4m_continuous_pi.aemeasurable hφ.aestronglyMeasurable
    simp only [e]
    exact this
  rw [p4m_klDiv_map_pi μ ν, b15b_klDiv_eq_iSup_proof]
  refine iSup_le fun φ => ?_
  have hφc : Continuous φ := φ.continuous
  have hexp : Continuous fun x => Real.exp (φ x) := Real.continuous_exp.comp hφc
  have h1 := hP φ hφc
  have hpos : 0 < ∫ x, Real.exp (φ x) ∂(ν.map p4m_pi) := by
    refine integral_exp_pos ?_
    exact hexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 := ENNReal.tendsto_ofReal (h1.sub (tendsto_const_nhds (x := Real.log (∫ x, Real.exp (φ x) ∂(ν.map p4m_pi)))))
  rw [← h3.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  refine le_trans ?_ (klDiv_map_le (μn n) ν p4m_continuous_pi.measurable)
  rw [b15b_klDiv_eq_iSup_proof ((μn n).map p4m_pi) (ν.map p4m_pi)]
  exact le_iSup (fun φ : C(P4MCube d N, ℝ) =>
    ENNReal.ofReal (∫ x, φ x ∂((μn n).map p4m_pi) - Real.log (∫ x, Real.exp (φ x) ∂(ν.map p4m_pi)))) φ

/-! ### The entropy of the mollified density -/

theorem p4m_klDiv_density {θ : ℝ} {W : EucConfig d N → ℝ} (hG : P4JWeight (p4GibbsOf θ W))
    {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1)
    (hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x))) :
    klDiv ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)))
        (gibbsRefW (p4GibbsOf θ W)) ≠ ⊤ ∧
      (klDiv ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)))
        (gibbsRefW (p4GibbsOf θ W))).toReal =
        (∫ x, (ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x))) +
          Real.log (gibbsPartitionW (p4GibbsOf θ W)).toReal := by
  set G := p4GibbsOf θ W with hGdef
  set dM : Measure (EucConfig d N) :=
    (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)) with hdM
  haveI : IsProbabilityMeasure dM := ⟨by
    rw [hdM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hρ1⟩
  haveI : IsProbabilityMeasure (gibbsRefW G) := hG.ref_prob
  have hac : dM ≪ gibbsRefW G := by
    rw [hdM, p4j_density_eq_ref hG hρ]
    exact withDensity_absolutelyContinuous _ _
  have hρi := p4j_integrable_of_lintegral hρ hρ0 hρ1
  set Lz : ℝ := Real.log (gibbsPartitionW G).toReal with hLz
  have hsm : ∀ x, ρ x * (Real.log (ρ x) + Lz + θ⁻¹ * W x) =
      (ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) + Lz * ρ x := fun x => by ring
  have hℓ : Integrable (fun x => Real.log (ρ x) + Lz + θ⁻¹ * W x) dM := by
    rw [hdM, p4j_integrable_dMeas_iff hρ hρ0]
    exact (hΦ.add (hρi.const_mul Lz)).congr (ae_of_all _ fun x => (hsm x).symm)
  have hllr := p4j_llr_density hG hρ hρ0
  have hint : Integrable (llr dM (gibbsRefW G)) dM :=
    hℓ.congr (by filter_upwards [hllr] with x hx using hx.symm)
  have h1 := toReal_klDiv hac hint
  refine ⟨?_, ?_⟩
  · rw [klDiv_of_ac_of_integrable hac hint]; exact ENNReal.ofReal_ne_top
  · rw [h1]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [integral_congr_ae hllr, p4j_integral_dMeas hρ hρ0]
    have e : ∫ x, ρ x * (Real.log (ρ x) + Lz + θ⁻¹ * W x) =
        ∫ x, ((ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) + Lz * ρ x) :=
      integral_congr_ae (ae_of_all _ hsm)
    rw [e, integral_add hΦ (hρi.const_mul Lz), integral_const_mul, p4j_integral_of_lintegral hρ hρ0 hρ1, mul_one]

theorem p4m_liminf_sub_const (a : ℕ → ℝ≥0∞) (c : ℝ) :
    (((liminf a atTop : ℝ≥0∞) : EReal)) - (c : EReal) =
      liminf (fun n => (a n : EReal) - (c : EReal)) atTop := by
  have e : (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) = fun x : ℝ≥0∞ => (x : EReal) + ((-c : ℝ) : EReal) := by
    funext x; rw [sub_eq_add_neg, EReal.coe_neg]
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) := by
    rw [e]; intro x y hxy
    exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy) _
  have hcont : Continuous (fun x : ℝ≥0∞ => (x : EReal) - (c : EReal)) := by
    rw [e]
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hadd := EReal.continuousAt_add (p := ((x : EReal), ((-c : ℝ) : EReal))) (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))
    have hf : ContinuousAt (fun y : ℝ≥0∞ => ((y : EReal), ((-c : ℝ) : EReal))) x :=
      continuous_coe_ennreal_ereal.continuousAt.prodMk continuousAt_const
    exact ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
      (f := fun y : ℝ≥0∞ => ((y : EReal), ((-c : ℝ) : EReal))) hadd hf
  exact hmono.map_liminf_of_continuousAt a hcont.continuousAt

/-- The free energy of the mollified density is `klDiv - log Z`. -/
theorem p4m_free_eq {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) {v : ℝ} (hv : 0 < v) :
    ((p4Free θ (V 0) (p4Mol v μ) : ℝ) : EReal) =
      ((klDiv (p4m_molMeas v μ) (gibbsRefW (p4GibbsOf θ (V 0))) : ℝ≥0∞) : EReal) -
        ((Real.log (gibbsPartitionW (p4GibbsOf θ (V 0))).toReal : ℝ) : EReal) := by
  obtain ⟨c0, C0, hc0, hconf⟩ := hV.conf
  have hconf0 : ∀ x, c0 * ‖x‖ ^ 2 - C0 ≤ V 0 x := fun x => hconf 0 ⟨le_rfl, hT⟩ x
  have hVc : Continuous (V 0) :=
    hV.cont_V.comp (continuous_const.prodMk continuous_id : Continuous fun x : EucConfig d N => ((0 : ℝ), x))
  have hG := p4j_weight_of_conf hθ hVc hc0 hconf0
  obtain ⟨Cq, hCq0, hq⟩ := p4j_quad_growth hT hV
  obtain ⟨κ, hκ, hsym⟩ := p4j_symm_bound hT hV
  have hVμ : Integrable (V 0) μ :=
    Integrable.mono' (((integrable_const (1 : ℝ)).add hΦ).const_mul Cq) hVc.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hq x)
  have hC0 : ∀ x, 0 ≤ V 0 x + C0 := fun x => by
    have := mul_nonneg hc0.le (sq_nonneg ‖x‖)
    have := hconf0 x
    linarith
  obtain ⟨hPI, -⟩ := p4j_pot_real hv hVc hC0 hκ hsym hq μ hVμ hΦ
  have hIlog := p4j_mol_log_integrable hv μ hΦ
  have hΦρ : Integrable (fun x => p4Mol v μ x * Real.log (p4Mol v μ x) +
      θ⁻¹ * (p4Mol v μ x * V 0 x)) := hIlog.add (hPI.const_mul θ⁻¹)
  obtain ⟨hne, hval⟩ := p4m_klDiv_density hG (p4j_mol_continuous hv μ).measurable
    (fun x => integral_nonneg fun y => (p4j_gauss_pos hv _).le) (p4j_mol_lintegral_one hv μ) hΦρ
  have hne' : klDiv (p4m_molMeas v μ) (gibbsRefW (p4GibbsOf θ (V 0))) ≠ ⊤ := hne
  have hval' : (klDiv (p4m_molMeas v μ) (gibbsRefW (p4GibbsOf θ (V 0)))).toReal = _ := hval
  rw [← EReal.coe_ennreal_toReal hne', hval', ← EReal.coe_sub]
  congr 1
  unfold p4Free
  have : ∀ x, p4Mol v μ x * Real.log (p4Mol v μ x) + p4Mol v μ x * V 0 x / θ =
      p4Mol v μ x * Real.log (p4Mol v μ x) + θ⁻¹ * (p4Mol v μ x * V 0 x) := fun x => by ring
  simp_rw [this]
  ring

/-- Lower semicontinuity of the entropy under the Gaussian mollification. -/
theorem p4m_entropy_lsc {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ]
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) :
    gibbsEntropyW (p4GibbsOf θ (V 0)) μ ≤
      liminf (fun n => ((p4Free θ (V 0) (p4Mol (v n) μ) : ℝ) : EReal)) atTop := by
  have hΦ := p4j_Phi_integrable hmom
  obtain ⟨c0, C0, hc0, hconf⟩ := hV.conf
  have hconf0 : ∀ x, c0 * ‖x‖ ^ 2 - C0 ≤ V 0 x := fun x => hconf 0 ⟨le_rfl, hT⟩ x
  have hVc : Continuous (V 0) :=
    hV.cont_V.comp (continuous_const.prodMk continuous_id : Continuous fun x : EucConfig d N => ((0 : ℝ), x))
  have hG := p4j_weight_of_conf hθ hVc hc0 hconf0
  haveI := hG.ref_prob
  haveI : ∀ n, IsProbabilityMeasure (p4m_molMeas (v n) μ) := fun n => p4m_molMeas_prob (hv n) μ
  set ref := gibbsRefW (p4GibbsOf θ (V 0)) with href
  set Lz : ℝ := Real.log (gibbsPartitionW (p4GibbsOf θ (V 0))).toReal with hLz
  have hkey := fun n => p4m_free_eq hθ hT hV μ hΦ (hv n)
  simp_rw [hkey]
  rw [← p4m_liminf_sub_const (fun n => klDiv (p4m_molMeas (v n) μ) ref) Lz]
  unfold gibbsEntropyW relEntropy
  have hle : klDiv μ ref ≤ liminf (fun n => klDiv (p4m_molMeas (v n) μ) ref) atTop :=
    p4m_klDiv_liminf (fun ψ hψ hb => by
      obtain ⟨C, hC⟩ := hb
      exact p4m_molMeas_tendsto μ hv hv0 hψ hC)
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - (Lz : EReal)) := fun x y hxy => by
    show (x : EReal) - (Lz : EReal) ≤ (y : EReal) - (Lz : EReal)
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy) _
  exact hmono hle

/-! ### Differentiability of the mollification -/

theorem p4m_innerL_cont : Continuous (p4InnerL : EucConfig d N → EucConfig d N →L[ℝ] ℝ) := by
  unfold p4InnerL
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((innerSL ℝ).continuous.comp (continuous_apply i)).clm_comp continuous_const

theorem p4m_Phi_hasFDerivAt (w : EucConfig d N) :
    HasFDerivAt (p4j_Phi : EucConfig d N → ℝ) ((2 : ℝ) • p4InnerL w) w := by
  unfold p4j_Phi p4InnerL
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)), HasFDerivAt (fun w' : EucConfig d N => ‖w' i‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (w i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)) w :=
    fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt.norm_sq
  have := HasFDerivAt.fun_sum h
  convert this using 1
  rw [← Finset.smul_sum, two_smul ℝ, two_nsmul]

theorem p4m_gauss_hasFDerivAt {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    HasFDerivAt (p4Gauss d N v) ((-(p4Gauss d N v w / v)) • p4InnerL w) w := by
  have h1 := (((p4m_Phi_hasFDerivAt w).const_mul (-(1 / (2 * v)))).exp).const_mul (p4j_c d N v)
  have e : (p4Gauss d N v : EucConfig d N → ℝ) =
      fun w' => p4j_c d N v * Real.exp (-(1 / (2 * v)) * p4j_Phi w') := by
    funext w'
    rw [p4j_gauss_eq]; congr 2; ring
  rw [e]
  convert h1 using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  field_simp

theorem p4m_opNorm_innerL (w : EucConfig d N) : ‖p4InnerL w‖ ≤ N * ‖w‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => by
    rw [Real.norm_eq_abs]; exact p4j_innerL_bound w y

theorem p4m_Gd_cont {v : ℝ} :
    Continuous fun w : EucConfig d N => (-(p4Gauss d N v w / v)) • p4InnerL w :=
  (((p4j_gauss_continuous v).div_const v).neg).smul p4m_innerL_cont

theorem p4m_Gd_bound {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    ‖(-(p4Gauss d N v w / v)) • p4InnerL w‖ ≤ p4j_c d N v * N * (1 + v) / v := by
  have hc := p4j_c_pos (d := d) (N := N) hv
  have hG0 := p4j_gauss_pos hv w
  set t : ℝ := ‖w‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg w
  have hPn := p4j_norm_sq_le_Phi w
  set s : ℝ := t ^ 2 / (2 * v) with hs
  have hs0 : 0 ≤ s := by positivity
  have hE : Real.exp (-(p4j_Phi w) / (2 * v)) ≤ Real.exp (-s) := by
    refine Real.exp_le_exp.2 ?_
    have : t ^ 2 / (2 * v) ≤ p4j_Phi w / (2 * v) := div_le_div_of_nonneg_right hPn (by positivity)
    have e : -(p4j_Phi w) / (2 * v) = -(p4j_Phi w / (2 * v)) := by ring
    rw [e]; linarith
  have hse : s * Real.exp (-s) ≤ 1 := by
    have h1 := Real.add_one_le_exp s
    have h2 : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
    rw [h2, ← div_eq_mul_inv, div_le_one (Real.exp_pos s)]
    linarith
  have hE1 : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hts : t ≤ (1 + t ^ 2) / 2 := by nlinarith [sq_nonneg (t - 1)]
  have hkey : t * Real.exp (-s) ≤ 1 + v := by
    have e1 : (1 + t ^ 2) / 2 * Real.exp (-s) = Real.exp (-s) / 2 + v * (s * Real.exp (-s)) := by
      rw [hs]; field_simp
    calc t * Real.exp (-s) ≤ (1 + t ^ 2) / 2 * Real.exp (-s) :=
          mul_le_mul_of_nonneg_right hts (Real.exp_pos _).le
      _ = Real.exp (-s) / 2 + v * (s * Real.exp (-s)) := e1
      _ ≤ 1 + v := by nlinarith [mul_le_mul_of_nonneg_left hse hv.le]
  have hGt : p4Gauss d N v w * t ≤ p4j_c d N v * (1 + v) := by
    rw [p4j_gauss_eq]
    calc p4j_c d N v * Real.exp (-(p4j_Phi w) / (2 * v)) * t
        ≤ p4j_c d N v * Real.exp (-s) * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hc.le) ht0
      _ = p4j_c d N v * (t * Real.exp (-s)) := by ring
      _ ≤ p4j_c d N v * (1 + v) := mul_le_mul_of_nonneg_left hkey hc.le
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (div_nonneg hG0.le hv.le)]
  calc p4Gauss d N v w / v * ‖p4InnerL w‖ ≤ p4Gauss d N v w / v * (N * t) :=
        mul_le_mul_of_nonneg_left (p4m_opNorm_innerL w) (div_nonneg hG0.le hv.le)
    _ = (p4Gauss d N v w * t) * N / v := by ring
    _ ≤ (p4j_c d N v * (1 + v)) * N / v := by
        gcongr
    _ = p4j_c d N v * N * (1 + v) / v := by ring

theorem p4m_mol_hasFDerivAt {v : ℝ} (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (x : EucConfig d N) :
    HasFDerivAt (p4Mol v μ)
      (∫ y, (-(p4Gauss d N v (x - y) / v)) • p4InnerL (x - y) ∂μ) x := by
  unfold p4Mol
  have hcont : ∀ x : EucConfig d N, Continuous fun y : EucConfig d N => p4Gauss d N v (x - y) :=
    fun x => (p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun (x y : EucConfig d N) => p4Gauss d N v (x - y))
    (F' := fun (x y : EucConfig d N) => (-(p4Gauss d N v (x - y) / v)) • p4InnerL (x - y))
    (x₀ := x) (bound := fun _ => p4j_c d N v * N * (1 + v) / v) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    (Integrable.of_bound (hcont x).aestronglyMeasurable (p4j_c d N v) (ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]; exact p4j_gauss_le hv _))
    ((p4m_Gd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun y x' _ => p4m_Gd_bound hv (x' - y))
    (integrable_const _)
    (ae_of_all _ fun y x' _ => by
      have h := (p4m_gauss_hasFDerivAt hv (x' - y)).comp x' ((hasFDerivAt_id x').sub_const y)
      simpa [Function.comp_def] using h)
  exact this

theorem p4m_mol_contDiff {v : ℝ} (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    ContDiff ℝ 1 (p4Mol v μ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (p4m_mol_hasFDerivAt hv μ x).differentiableAt, ?_⟩
  have : fderiv ℝ (p4Mol v μ) =
      fun x => ∫ y, (-(p4Gauss d N v (x - y) / v)) • p4InnerL (x - y) ∂μ :=
    funext fun x => (p4m_mol_hasFDerivAt hv μ x).fderiv
  rw [this]
  refine continuous_of_dominated (bound := fun _ => p4j_c d N v * N * (1 + v) / v) (fun x => ?_)
    (fun x => ?_) (integrable_const _) (ae_of_all _ fun y => ?_)
  · exact (p4m_Gd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun y => p4m_Gd_bound hv (x - y)
  · exact p4m_Gd_cont.comp (continuous_id.sub continuous_const)


/-! ### The `ζ`-functionals are bounded by the dissipation -/

theorem p4m_coord_expand (L : EucConfig d N →L[ℝ] ℝ) (z : EucConfig d N) :
    L z = ∑ k : Fin N × Fin d, z k.1 k.2 * L (configBasis d N k) := by
  have h : z = ∑ k : Fin N × Fin d, z k.1 k.2 • configBasis d N k := by
    funext i
    ext j
    simp [configBasis, Finset.sum_apply, Fintype.sum_prod_type, Pi.single_apply,
      EuclideanSpace.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

theorem p4m_norm_sq_sum (z : EucConfig d N) :
    ∑ i, ‖z i‖ ^ 2 = ∑ k : Fin N × Fin d, (z k.1 k.2) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem p4m_ofReal_integral_le {G : EucConfig d N → ℝ} (hG : Integrable G) :
    ENNReal.ofReal (∫ x, G x) ≤ ∫⁻ x, ENNReal.ofReal (G x) := by
  have hp : Integrable (fun x => max (G x) 0) := hG.pos_part
  have h1 : ∫ x, G x ≤ ∫ x, max (G x) 0 := integral_mono hG hp (fun x => le_max_left _ _)
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal hp (ae_of_all _ fun x => le_max_right _ _)]
  refine le_of_eq (lintegral_congr fun x => ?_)
  simp [ENNReal.ofReal_max]

/-- The `ζ`-functional of the variational formula for the Fisher information. -/
def p4m_psi (G : EucConfig d N → ℝ) (ζ : EucConfig d N → EucConfig d N) (X : EucConfig d N) : ℝ :=
  -2 * configDivW ζ X - 2 * fderiv ℝ (fun Z : EucConfig d N => Real.log (G Z)) X (ζ X) -
    ∑ i, ‖ζ X i‖ ^ 2

theorem p4m_fisherInfo_eq (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) :
    fisherInfoW G P = ⨆ (ζ : EucConfig d N → EucConfig d N) (_ : IsFisherTestFieldW ζ),
      ENNReal.ofReal (∫ X, p4m_psi G ζ X ∂P) := rfl

theorem p4m_fderiv_log {θ : ℝ} {W : EucConfig d N → ℝ} (hW : ∀ x, DifferentiableAt ℝ W x)
    (X : EucConfig d N) :
    fderiv ℝ (fun Z : EucConfig d N => Real.log (p4GibbsOf θ W Z)) X = (-θ⁻¹) • fderiv ℝ W X := by
  have : (fun Z : EucConfig d N => Real.log (p4GibbsOf θ W Z)) = fun Z => (-θ⁻¹) * W Z :=
    funext fun Z => by unfold p4GibbsOf; rw [Real.log_exp]
  rw [this]
  exact fderiv_const_mul (hW X) (-θ⁻¹)


theorem p4m_psi_le {θ : ℝ} (hθ : 0 < θ) {W u : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ x, 0 < u x) {ζ : EucConfig d N → EucConfig d N}
    (hζ : IsFisherTestFieldW ζ) :
    ENNReal.ofReal (∫ X, p4m_psi (p4GibbsOf θ W) ζ X * u X) ≤ p4Diss θ W u := by
  obtain ⟨K, hKc, -, hKz⟩ := hζ.support
  have hζs : ContDiff ℝ ∞ ζ := hζ.smooth
  have hζc : Continuous ζ := hζs.continuous
  set e : Fin N × Fin d → EucConfig d N := fun k => configBasis d N k with he
  set ζk : Fin N × Fin d → EucConfig d N → ℝ := fun k Z => ζ Z k.1 k.2 with hζk
  have hzk : ∀ k, ContDiff ℝ ∞ (ζk k) := fun k =>
    ((EuclideanSpace.proj k.2).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Euc d) k.1)).contDiff.comp hζs
  have hzkc : ∀ k, Continuous (ζk k) := fun k => (hzk k).continuous
  have hzkK : ∀ k X, X ∉ K → ζk k X = 0 := fun k X hX => by simp [hζk, hKz X hX]
  have hDk : ∀ k, ContDiff ℝ 1 (ζk k) := fun k => (hzk k).of_le (by norm_num)
  have hDc : ∀ k, Continuous (fderiv ℝ (ζk k)) := fun k => (hDk k).continuous_fderiv (by simp)
  have hdzK : ∀ k X, X ∉ K → fderiv ℝ (ζk k) X = 0 := fun k X hX => by
    have hev : (ζk k) =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hX] with Z hZ
      exact hzkK k Z hZ
    rw [hev.fderiv_eq]; simp
  have hu1 : ContDiff ℝ 1 u := hu
  have hucont : Continuous u := hu.continuous
  have hu'c : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hW'c : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  have hudiff : ∀ x, DifferentiableAt ℝ u x := fun x => hu.differentiable (by simp) x
  have hWdiff : ∀ x, DifferentiableAt ℝ W x := fun x => hW.differentiable (by simp) x
  have hudiff' : ∀ x, HasFDerivAt u (fderiv ℝ u x) x := fun x => (hudiff x).hasFDerivAt
  have hzdiff : ∀ k x, DifferentiableAt ℝ (ζk k) x := fun k x => (hDk k).differentiable (by simp) x
  -- compact supports
  have hcs : ∀ (f : EucConfig d N → ℝ), Continuous f → (∀ X, X ∉ K → f X = 0) → Integrable f :=
    fun f hf hz => hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hz)
  -- integration by parts
  have hibp : ∀ k, ∫ X, u X * fderiv ℝ (ζk k) X (e k) = -∫ X, fderiv ℝ u X (e k) * ζk k X := by
    intro k
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ (fun x _ => hudiff x)
      (fun x _ => hzdiff k x)
    · exact hcs _ ((hu'c.clm_apply continuous_const).mul (hzkc k)) fun X hX => by
        simp [hzkK k X hX]
    · exact hcs _ (hucont.mul ((hDc k).clm_apply continuous_const)) fun X hX => by
        simp [hdzK k X hX]
    · exact hcs _ (hucont.mul (hzkc k)) fun X hX => by simp [hzkK k X hX]
  -- the pieces
  have hdiv : ∀ X, configDivW ζ X = ∑ k, fderiv ℝ (ζk k) X (e k) := fun X => rfl
  have hζK : ∀ X, X ∉ K → ζ X = 0 := hKz
  have hdivc : Continuous (configDivW ζ) := by
    have : configDivW ζ = fun X => ∑ k, fderiv ℝ (ζk k) X (e k) := funext hdiv
    rw [this]
    exact continuous_finset_sum _ fun k _ => (hDc k).clm_apply continuous_const
  have hdivK : ∀ X, X ∉ K → configDivW ζ X = 0 := fun X hX => by
    rw [hdiv]; simp [hdzK _ X hX]
  have hnormc : Continuous fun X : EucConfig d N => ∑ i, ‖ζ X i‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => (((continuous_apply i).comp hζc).norm).pow 2
  have hnormK : ∀ X, X ∉ K → ∑ i, ‖ζ X i‖ ^ 2 = 0 := fun X hX => by simp [hζK X hX]
  set P1 : EucConfig d N → ℝ := fun X => u X * configDivW ζ X with hP1
  set P2 : EucConfig d N → ℝ := fun X => fderiv ℝ u X (ζ X) with hP2
  set P3 : EucConfig d N → ℝ := fun X => u X * fderiv ℝ W X (ζ X) with hP3
  set P4 : EucConfig d N → ℝ := fun X => u X * ∑ i, ‖ζ X i‖ ^ 2 with hP4
  have iP1 : Integrable P1 := hcs _ (hucont.mul hdivc) fun X hX => by simp [hP1, hdivK X hX]
  have iP2 : Integrable P2 := hcs _ (hu'c.clm_apply hζc) fun X hX => by simp [hP2, hζK X hX]
  have iP3 : Integrable P3 := hcs _ (hucont.mul (hW'c.clm_apply hζc)) fun X hX => by
    simp [hP3, hζK X hX]
  have iP4 : Integrable P4 := hcs _ (hucont.mul hnormc) fun X hX => by simp [hP4, hnormK X hX]
  -- ∫ P1 = - ∫ P2
  have hexp2 : ∀ X, P2 X = ∑ k, fderiv ℝ u X (e k) * ζk k X := fun X => by
    simp only [hP2]
    rw [p4m_coord_expand (fderiv ℝ u X) (ζ X)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have iA : ∀ k, Integrable (fun X => u X * fderiv ℝ (ζk k) X (e k)) := fun k =>
    hcs _ (hucont.mul ((hDc k).clm_apply continuous_const)) fun X hX => by simp [hdzK k X hX]
  have iB : ∀ k, Integrable (fun X => fderiv ℝ u X (e k) * ζk k X) := fun k =>
    hcs _ ((hu'c.clm_apply continuous_const).mul (hzkc k)) fun X hX => by simp [hzkK k X hX]
  have hI1 : ∫ X, P1 X = -∫ X, P2 X := by
    have e1 : ∀ X, P1 X = ∑ k, u X * fderiv ℝ (ζk k) X (e k) := fun X => by
      simp only [hP1]; rw [hdiv, Finset.mul_sum]
    simp_rw [e1, hexp2]
    rw [integral_finset_sum _ (fun k _ => iA k), integral_finset_sum _ (fun k _ => iB k),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hibp k
  -- the integral of the functional
  have hpsi : ∀ X, p4m_psi (p4GibbsOf θ W) ζ X * u X = -2 * P1 X + 2 * θ⁻¹ * P3 X - P4 X := by
    intro X
    unfold p4m_psi
    rw [p4m_fderiv_log hWdiff X]
    simp only [hP1, hP3, hP4, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  set H : EucConfig d N → ℝ := fun X => 2 * P2 X + 2 * θ⁻¹ * P3 X - P4 X with hH
  have iH : Integrable H := ((iP2.const_mul 2).add (iP3.const_mul (2 * θ⁻¹))).sub iP4
  have hint : ∫ X, p4m_psi (p4GibbsOf θ W) ζ X * u X = ∫ X, H X := by
    simp_rw [hpsi]
    have hA : Integrable (fun X => -2 * P1 X + 2 * θ⁻¹ * P3 X) :=
      (iP1.const_mul (-2)).add (iP3.const_mul (2 * θ⁻¹))
    rw [integral_sub hA iP4, integral_add (iP1.const_mul (-2)) (iP3.const_mul (2 * θ⁻¹)),
      integral_const_mul, integral_const_mul]
    simp only [hH]
    have hA2 : Integrable (fun X => 2 * P2 X + 2 * θ⁻¹ * P3 X) :=
      (iP2.const_mul 2).add (iP3.const_mul (2 * θ⁻¹))
    rw [integral_sub hA2 iP4,
      integral_add (iP2.const_mul 2) (iP3.const_mul (2 * θ⁻¹)), integral_const_mul, integral_const_mul,
      hI1]
    ring
  -- pointwise bound
  have hle : ∀ X, H X ≤ u X * ∑ k : Fin N × Fin d,
      ((u X)⁻¹ * fderiv ℝ u X (configBasis d N k) + θ⁻¹ * fderiv ℝ W X (configBasis d N k)) ^ 2 := by
    intro X
    have hux := hu0 X
    have e2 : P2 X = ∑ k, ζ X k.1 k.2 * fderiv ℝ u X (e k) := by
      simp only [hP2]; exact p4m_coord_expand (fderiv ℝ u X) (ζ X)
    have e3 : P3 X = u X * ∑ k, ζ X k.1 k.2 * fderiv ℝ W X (e k) := by
      simp only [hP3]; rw [p4m_coord_expand (fderiv ℝ W X) (ζ X)]
    have e4 : P4 X = u X * ∑ k : Fin N × Fin d, (ζ X k.1 k.2) ^ 2 := by
      simp only [hP4]; rw [p4m_norm_sq_sum]
    have hsum : H X = ∑ k : Fin N × Fin d, (2 * (ζ X k.1 k.2 * fderiv ℝ u X (e k)) +
        2 * θ⁻¹ * (u X * (ζ X k.1 k.2 * fderiv ℝ W X (e k))) - u X * (ζ X k.1 k.2) ^ 2) := by
      simp only [hH, e2, e3, e4]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    set a : ℝ := ζ X k.1 k.2
    set p : ℝ := fderiv ℝ u X (e k)
    set q : ℝ := fderiv ℝ W X (e k)
    set ux : ℝ := u X
    have hw : p + θ⁻¹ * ux * q = ux * (ux⁻¹ * p + θ⁻¹ * q) := by
      field_simp
    have hsq := mul_nonneg hux.le (sq_nonneg ((ux⁻¹ * p + θ⁻¹ * q) - a))
    have e5 : 2 * (a * p) + 2 * θ⁻¹ * (ux * (a * q)) = 2 * a * (ux * (ux⁻¹ * p + θ⁻¹ * q)) := by
      rw [← hw]; ring
    rw [e5]
    nlinarith [hsq]
  -- conclusion
  rw [hint]
  refine (p4m_ofReal_integral_le iH).trans ?_
  unfold p4Diss
  exact lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hle X)


/-! ### Fisher information and assembly -/

theorem p4m_psi_cont {θ : ℝ} {W : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    {ζ : EucConfig d N → EucConfig d N} (hζ : IsFisherTestFieldW ζ) :
    Continuous (p4m_psi (p4GibbsOf θ W) ζ) ∧ ∃ C : ℝ, ∀ X, |p4m_psi (p4GibbsOf θ W) ζ X| ≤ C := by
  obtain ⟨K, hKc, -, hKz⟩ := hζ.support
  have hζs : ContDiff ℝ ∞ ζ := hζ.smooth
  have hζc : Continuous ζ := hζs.continuous
  set e : Fin N × Fin d → EucConfig d N := fun k => configBasis d N k with he
  set ζk : Fin N × Fin d → EucConfig d N → ℝ := fun k Z => ζ Z k.1 k.2 with hζk
  have hzk : ∀ k, ContDiff ℝ ∞ (ζk k) := fun k =>
    ((EuclideanSpace.proj k.2).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Euc d) k.1)).contDiff.comp hζs
  have hzkK : ∀ k X, X ∉ K → ζk k X = 0 := fun k X hX => by simp [hζk, hKz X hX]
  have hDk : ∀ k, ContDiff ℝ 1 (ζk k) := fun k => (hzk k).of_le (by norm_num)
  have hDc : ∀ k, Continuous (fderiv ℝ (ζk k)) := fun k => (hDk k).continuous_fderiv (by simp)
  have hdzK : ∀ k X, X ∉ K → fderiv ℝ (ζk k) X = 0 := fun k X hX => by
    have hev : (ζk k) =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hX] with Z hZ
      exact hzkK k Z hZ
    rw [hev.fderiv_eq]; simp
  have hW'c : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  have hWdiff : ∀ x, DifferentiableAt ℝ W x := fun x => hW.differentiable (by simp) x
  have hdiv : ∀ X, configDivW ζ X = ∑ k, fderiv ℝ (ζk k) X (e k) := fun X => rfl
  have hdivc : Continuous (configDivW ζ) := by
    have : configDivW ζ = fun X => ∑ k, fderiv ℝ (ζk k) X (e k) := funext hdiv
    rw [this]
    exact continuous_finset_sum _ fun k _ => (hDc k).clm_apply continuous_const
  have hdivK : ∀ X, X ∉ K → configDivW ζ X = 0 := fun X hX => by
    rw [hdiv]; simp [hdzK _ X hX]
  have hnormc : Continuous fun X : EucConfig d N => ∑ i, ‖ζ X i‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => (((continuous_apply i).comp hζc).norm).pow 2
  have hpsi : p4m_psi (p4GibbsOf θ W) ζ = fun X => -2 * configDivW ζ X -
      2 * ((-θ⁻¹) * fderiv ℝ W X (ζ X)) - ∑ i, ‖ζ X i‖ ^ 2 := by
    funext X
    unfold p4m_psi
    rw [p4m_fderiv_log hWdiff X]
    simp
  have hc : Continuous (p4m_psi (p4GibbsOf θ W) ζ) := by
    rw [hpsi]
    exact ((continuous_const.mul hdivc).sub
      (continuous_const.mul (continuous_const.mul (hW'c.clm_apply hζc)))).sub hnormc
  have hcs : HasCompactSupport (p4m_psi (p4GibbsOf θ W) ζ) :=
    HasCompactSupport.intro hKc fun X hX => by
      rw [hpsi]; simp [hdivK X hX, hKz X hX]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨hc, C, fun X => by simpa [Real.norm_eq_abs] using hC X⟩

theorem p4m_mol_pos' {v : ℝ} (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (x : EucConfig d N) : 0 < p4Mol v μ x := by
  unfold p4Mol
  have hI : Integrable (fun y : EucConfig d N => p4Gauss d N v (x - y)) μ :=
    Integrable.of_bound ((p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (p4j_c d N v) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]; exact p4j_gauss_le hv _)
  rw [integral_pos_iff_support_of_nonneg (fun y => (p4j_gauss_pos hv _).le) hI]
  have : Function.support (fun y : EucConfig d N => p4Gauss d N v (x - y)) = Set.univ := by
    ext y; simp [Function.mem_support, (p4j_gauss_pos hv _).ne']
  rw [this, measure_univ]
  exact one_pos

/-- Lower semicontinuity of the Fisher information under the Gaussian mollification. -/
theorem p4m_fisher_lsc {θ : ℝ} (hθ : 0 < θ) {W : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) :
    fisherInfoW (p4GibbsOf θ W) μ ≤ liminf (fun n => p4Diss θ W (p4Mol (v n) μ)) atTop := by
  rw [p4m_fisherInfo_eq]
  refine iSup_le fun ζ => iSup_le fun hζ => ?_
  obtain ⟨hψc, C, hC⟩ := p4m_psi_cont (θ := θ) hW hζ
  haveI : ∀ n, IsProbabilityMeasure (p4m_molMeas (v n) μ) := fun n => p4m_molMeas_prob (hv n) μ
  have hlim := p4m_molMeas_tendsto μ hv hv0 hψc hC
  have hlim' := ENNReal.tendsto_ofReal hlim
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  have h1 : ∫ z, p4m_psi (p4GibbsOf θ W) ζ z ∂(p4m_molMeas (v n) μ) =
      ∫ X, p4m_psi (p4GibbsOf θ W) ζ X * p4Mol (v n) μ X := by
    unfold p4m_molMeas
    rw [p4j_integral_dMeas (p4j_mol_continuous (hv n) μ).measurable
      (fun x => (p4m_mol_pos' (hv n) μ x).le)]
    exact integral_congr_ae (ae_of_all _ fun X => mul_comm _ _)
  rw [h1]
  exact p4m_psi_le hθ hW (p4m_mol_contDiff (hv n) μ) (p4m_mol_pos' (hv n) μ) hζ

/-- The time-`τ` slice of a potential hypothesis is a (time-constant) potential hypothesis on `[0,0]`. -/
theorem p4m_const_hyp {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ}
    (hV : P4PotHyp V b T) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    P4PotHyp (fun _ : ℝ => V τ) (fun _ : ℝ => b τ) 0 where
  grad := fun _ x => hV.grad τ x
  cont_b := (hV.cont_b.comp (continuous_const.prodMk continuous_snd) :
    Continuous fun p : ℝ × EucConfig d N => Function.uncurry b (τ, p.2))
  lip := by
    obtain ⟨K, hK⟩ := hV.lip
    exact ⟨K, fun _ _ => hK τ hτ⟩
  cont_V := (hV.cont_V.comp (continuous_const.prodMk continuous_snd) :
    Continuous fun p : ℝ × EucConfig d N => Function.uncurry V (τ, p.2))
  dtime := ⟨fun _ _ => 0, continuous_const, fun _ x => hasDerivAt_const _ _, fun _ _ _ => le_rfl, 0,
    fun _ _ x => by simp⟩
  conf := by
    obtain ⟨c, C, hc, h⟩ := hV.conf
    exact ⟨c, C, hc, fun _ _ x => h τ hτ x⟩

theorem p4m_contDiff_of_hyp {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N}
    {T : ℝ} (hV : P4PotHyp V b T) (τ : ℝ) : ContDiff ℝ 1 (V τ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hV.grad τ x).differentiableAt, ?_⟩
  have : fderiv ℝ (V τ) = fun x => -(p4InnerL (b τ x)) := funext fun x => (hV.grad τ x).fderiv
  rw [this]
  exact (p4m_innerL_cont.comp (hV.cont_b.comp (continuous_const.prodMk continuous_id))).neg

theorem p4_mollify_lsc_proof {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ]
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) :
    gibbsEntropyW (p4GibbsOf θ (V τ)) μ ≤
        liminf (fun n => ((p4Free θ (V τ) (p4Mol (v n) μ) : ℝ) : EReal)) atTop ∧
      fisherInfoW (p4GibbsOf θ (V τ)) μ ≤ liminf (fun n => p4Diss θ (V τ) (p4Mol (v n) μ)) atTop :=
  ⟨p4m_entropy_lsc hθ (le_refl (0 : ℝ)) (p4m_const_hyp hV hτ) hmom hv hv0,
    p4m_fisher_lsc hθ (p4m_contDiff_of_hyp hV τ) μ hv hv0⟩

example := (@p4_mollify_lsc_proof : type_of% @HRS.MP.SelfSimP4.p4_mollify_lsc)


end HRS.MP.SelfSimP4Impl
