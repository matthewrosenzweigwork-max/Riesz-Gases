import HRS.MS.S21T4ProdE
import HRS.MC.IID4

/-! S2.1(iii): genuine L² membership of the Wick variables, including finite-dimensional centered L². -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

/-- The common product-Gaussian field has the complete covariance/linearity bundle at contraction Λ=1. -/
theorem s21t4_product_eta_bundle (I : ProductGaussian μ) :
    S21LEta μ I.P I.η 1 := by
  letI := I.mΩ
  letI := I.prob
  let ξ' : ℕ → I.Ω → ℝ := fun i => (I.standard.aemeasurable i).mk (I.ξ i)
  have hm' : ∀ i, Measurable (ξ' i) := fun i => (I.standard.aemeasurable i).measurable_mk
  have hae : ∀ i, I.ξ i =ᵐ[I.P] ξ' i := fun i => (I.standard.aemeasurable i).ae_eq_mk
  have hξ'G : HRS.IsStdGaussianSeq I.P ξ' := by
    refine ⟨(ProbabilityTheory.iIndepFun_congr hae).1 I.standard.1, fun i => ?_⟩
    have h1 : I.P.map (I.ξ i) = gaussianReal 0 1 := I.standard.2 i
    show I.P.map (ξ' i) = gaussianReal 0 1
    rw [← Measure.map_congr (hae i)]
    exact h1
  refine s21l_eta_of_contract hξ'G hm' ?_ (s21t4_eta_linear I)
    (s21t4_eta_const I) ?_
  · intro f hf
    exact s21l_first_congr hae (I.first f hf)
  · intro f hf
    simpa only [one_mul] using s21t4_eta_contract I f hf

/-- Every frozen Wick-limit clause is a genuine L² random variable, not a junk-valued integral. -/
theorem s21t4_wick_memLp (I : ProductGaussian μ) (a : ℕ → HRS.Euc d → ℝ)
    (ha : IsR2ZeroMeanONB μ a) (k : HRS.Euc d → HRS.Euc d → ℝ)
    (Q : I.Ω → ℝ)
    (hQ : IsR2WickChaos I.P μ a (fun j => I.η (a j)) k Q) :
    MemLp Q 2 I.P := by
  letI := I.mΩ
  letI := I.prob
  obtain ⟨htest, hon, _⟩ := ha
  have hG : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) htest hon
  have hsec : ∀ n, MemLp
      (s94Sec I.P (fun i ω => I.η (a i) ω)
        (fun i j => r2WickCoeff μ a k i j) n) 2 I.P :=
    fun n => s94_sec_memLp hG _ n
  change HRS.TendstoL2 I.P
    (s94Sec I.P (fun i ω => I.η (a i) ω)
      (fun i j => r2WickCoeff μ a k i j)) Q at hQ
  exact HRS.MC.IID.memLp_of_tendstoL2 hsec hQ

/-- The S13 Gaussian-side finite family with the missing L² clause restored. -/
theorem s21t4_product_wick_finite_L2 (I : ProductGaussian μ) (m : ℕ)
    (h : Fin m → HRS.Euc d → HRS.Euc d → ℝ)
    (hh : ∀ i, MemLp (fun z : HRS.Euc d × HRS.Euc d => h i z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ i x y, h i x y = h i y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ i, MemLp (Q i) 2 I.P) ∧
      (∀ a, IsR2ZeroMeanONB μ a → ∀ i,
        IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ (h i)) (fun ω => 2 * Q i ω)) := by
  classical
  letI := I.mΩ
  letI := I.prob
  by_cases hex : ∃ a, IsR2ZeroMeanONB μ a
  · obtain ⟨a, ha⟩ := hex
    obtain ⟨Q, hsecond, hwick, hbd⟩ := s21t4_product_wick_finite I m h hh hs
    refine ⟨Q, ?_, hwick⟩
    intro i
    have hQi : MemLp (fun ω => 2 * Q i ω) 2 I.P :=
      s21t4_wick_memLp I a ha (r2CenterKernel μ (h i))
        (fun ω => 2 * Q i ω) (hwick a ha i)
    have hhalf := hQi.const_mul (1 / 2 : ℝ)
    convert hhalf using 1
    funext ω
    ring
  · refine ⟨fun _ _ => 0, fun i => MemLp.zero, ?_⟩
    intro a ha
    exact False.elim (hex ⟨a, ha⟩)

end HRS.MS.R26T3
