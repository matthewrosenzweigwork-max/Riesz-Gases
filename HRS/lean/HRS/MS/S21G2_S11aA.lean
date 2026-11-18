import HRS.Prob.HilbertCLT

/-!
# S21G2 S11a (part A) -- real Gaussian series with an `L²` limit (R26-T3.S11a)

For an i.i.d. standard Gaussian sequence `g` and `a ∈ ℓ²`, the partial sums `∑_{j<k} a_j g_j` converge in `L²(P)` to a
measurable `F`, `E[F²] = ∑ a_j²`, and `P.map F = N(0, ∑ a_j²)`.  (Real-valued, shared noise sequence; the repository's
`exists_gauss_series` hides `g`.)  Helper names carry the prefix `s21g2_s11a_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section Series

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

def s21g2_s11a_S (g : ℕ → Ω → ℝ) (a : ℕ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range k, a j * g j ω

theorem s21g2_s11a_sq (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (a : ℕ → ℝ) (F : Finset ℕ) : ∫ ω, (∑ j ∈ F, a j * g j ω) ^ 2 ∂P = ∑ j ∈ F, a j ^ 2 := by
  have := HRS.HilbertCLTAux.gauss_sum_sq_integral (H := ℝ) hg hind a F
  simpa [mul_comm, Real.norm_eq_abs, sq_abs] using this

theorem s21g2_s11a_memLp (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (a : ℕ → ℝ) (k : ℕ) :
    MemLp (s21g2_s11a_S g a k) 2 P :=
  memLp_finsetSum (f := fun j ω => a j * g j ω) (Finset.range k) fun j _ =>
    (HRS.HilbertCLTAux.gauss_memLp hg j).const_mul (a j)

theorem s21g2_s11a_limit (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (a : ℕ → ℝ) (ha : Summable fun j => a j ^ 2) :
    ∃ F : Ω → ℝ, Measurable F ∧ MemLp F 2 P ∧
      Tendsto (fun k => ∫ ω, (s21g2_s11a_S g a k ω - F ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hdiff : ∀ n m, n ≤ m → ∫ ω, (s21g2_s11a_S g a m ω - s21g2_s11a_S g a n ω) ^ 2 ∂P =
      ∑ j ∈ Finset.range m, a j ^ 2 - ∑ j ∈ Finset.range n, a j ^ 2 := by
    intro n m hnm
    have : ∀ ω, s21g2_s11a_S g a m ω - s21g2_s11a_S g a n ω = ∑ j ∈ Finset.Ico n m, a j * g j ω :=
      fun ω => by simp only [s21g2_s11a_S]; rw [Finset.sum_Ico_eq_sub _ hnm]
    simp_rw [this]
    rw [s21g2_s11a_sq hg hind, Finset.sum_Ico_eq_sub _ hnm]
  have hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ ω, ‖s21g2_s11a_S g a m ω - s21g2_s11a_S g a n ω‖ ^ 2 ∂P < ε := by
    intro ε hε
    have hc := ha.hasSum.tendsto_sum_nat.cauchySeq
    rw [Metric.cauchySeq_iff] at hc
    obtain ⟨N, hN⟩ := hc ε hε
    have key : ∀ m n, n ≤ m → m ≥ N → n ≥ N →
        ∫ ω, ‖s21g2_s11a_S g a m ω - s21g2_s11a_S g a n ω‖ ^ 2 ∂P < ε := by
      intro m n h hm hn
      have h1 := hdiff n m h
      have h0 : 0 ≤ ∫ ω, (s21g2_s11a_S g a m ω - s21g2_s11a_S g a n ω) ^ 2 ∂P :=
        integral_nonneg fun _ => sq_nonneg _
      have := hN m hm n hn
      rw [Real.dist_eq, abs_of_nonneg (by linarith)] at this
      simpa [Real.norm_eq_abs, sq_abs, h1] using this
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total n m with h | h
    · exact key m n h hm hn
    · have := key n m h hn hm
      simpa [norm_sub_rev] using this
  obtain ⟨F, hF, hlim⟩ := HRS.HilbertCLTAux.exists_L2_limit (H := ℝ)
    (fun k => s21g2_s11a_memLp hg a k) hcau
  refine ⟨hF.aestronglyMeasurable.aemeasurable.mk F, hF.aestronglyMeasurable.aemeasurable.measurable_mk,
    hF.ae_eq hF.aestronglyMeasurable.aemeasurable.ae_eq_mk, ?_⟩
  refine (hlim.congr fun k => ?_)
  refine integral_congr_ae ?_
  filter_upwards [hF.aestronglyMeasurable.aemeasurable.ae_eq_mk] with ω hω
  rw [← hω]; simp [Real.norm_eq_abs, sq_abs]

theorem s21g2_s11a_law (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (a : ℕ → ℝ) (ha : Summable fun j => a j ^ 2) {F : Ω → ℝ} (hF : MemLp F 2 P)
    (hlim : Tendsto (fun k => ∫ ω, (s21g2_s11a_S g a k ω - F ω) ^ 2 ∂P) atTop (𝓝 0)) :
    P.map F = gaussianReal 0 (Real.toNNReal (∑' j, a j ^ 2)) := by
  set σ2 := ∑' j, a j ^ 2 with hσ2
  have hσ : 0 ≤ σ2 := tsum_nonneg fun _ => sq_nonneg _
  have hFm : AEMeasurable F P := hF.aemeasurable
  have hGk := s21g2_s11a_memLp hg a
  have hGm : ∀ k, AEMeasurable (s21g2_s11a_S g a k) P := fun k => (hGk k).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hu : ∀ k, charFun (P.map (s21g2_s11a_S g a k)) t =
      Complex.exp (t * 0 * Complex.I - ((∑ j ∈ Finset.range k, (a j) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro k
    have hlaw := HRS.HilbertCLTAux.gauss_sum_hasLaw hg hind a k
    have e : s21g2_s11a_S g a k = fun ω => ∑ j ∈ Finset.range k, a j * g j ω := rfl
    rw [e, hlaw.map_eq, charFun_gaussianReal]
    congr 2
    push_cast
    simp
  have hv : Tendsto (fun k => ∑ j ∈ Finset.range k, (a j) ^ 2) atTop (𝓝 σ2) :=
    ha.hasSum.tendsto_sum_nat
  let f : ℝ → ℂ := fun v => Complex.exp (t * 0 * Complex.I - (v : ℂ) * (t : ℂ) ^ 2 / 2)
  have hf : Continuous f := by fun_prop
  have hlim1 : Tendsto (fun k => charFun (P.map (s21g2_s11a_S g a k)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) t)) := by
    simp_rw [hu]
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ]
    exact (hf.tendsto σ2).comp hv
  have hlim2 : Tendsto (fun k => charFun (P.map (s21g2_s11a_S g a k)) t) atTop
      (𝓝 (charFun (P.map F) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun k => |t| * Real.sqrt (∫ ω, (s21g2_s11a_S g a k ω - F ω) ^ 2 ∂P)) atTop
        (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
      rw [Real.sqrt_zero] at this
      simpa using this.const_mul |t|
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hb
    have hL2 : MemLp (fun ω => s21g2_s11a_S g a k ω - F ω) 2 P := (hGk k).sub hF
    have hint : Integrable (fun ω => s21g2_s11a_S g a k ω - F ω) P := hL2.integrable one_le_two
    refine (HRS.HilbertCLTAux.norm_charFun_sub_le (hGm k) hFm hint t).trans ?_
    gcongr
    calc ∫ ω, |s21g2_s11a_S g a k ω - F ω| ∂P
        ≤ Real.sqrt (∫ ω, |s21g2_s11a_S g a k ω - F ω| ^ 2 ∂P) :=
          integral_le_sqrt P hL2.norm
      _ = _ := by simp [sq_abs]
  exact tendsto_nhds_unique hlim2 hlim1

end Series

end HRS.MS.R26T3
