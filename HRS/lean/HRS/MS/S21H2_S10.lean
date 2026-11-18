import HRS.MS.S21H2_S10B

/-!
# S21H2, packet R26-T3.S10: one initial susceptibility Gaussian field

`InitialGaussian R` is the contract structure (qualified names).  Construction: the coercive symmetric form `b(x,y) = ⟪x, Res y⟫` of `S21H2_S10B` on `L²(μ₀)` gives the Hilbert space `HB`
(`S21H2_S10A`); an isonormal field `W` on `HB` is built from one i.i.d. standard Gaussian sequence along a Parseval sequence of `HB` (`s21g2_s11a_isonormal`, S21G2), and
`η f = W [P f]`.  Covariance `E W(h)W(h') = b(h,h') = susceptibilityCov`.  No square root of the response operator is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.S111X2

structure InitialGaussian {p : Parameters} {δ : ℝ} (R : Trajectory p δ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  ξ : ℕ → Ω → ℝ
  standard : HRS.IsStdGaussianSeq P ξ
  η : (Euc p.d → ℝ) → Ω → ℝ
  meas : ∀ f, MemLp f 2 (r26t3_mu R 0) → Measurable (η f)
  first : ∀ f, MemLp f 2 (r26t3_mu R 0) → HRS.InFirstChaos P ξ 2 (η f)
  gaussian : ∀ n (f : Fin n → Euc p.d → ℝ), (∀ i, MemLp (f i) 2 (r26t3_mu R 0)) →
    HRS.IsCenteredGaussian (HRS.law P (fun ω i => η (f i) ω))
  covariance : ∀ f g, MemLp f 2 (r26t3_mu R 0) → MemLp g 2 (r26t3_mu R 0) →
    ∫ ω, η f ω * η g ω ∂P =
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f g
attribute [instance] InitialGaussian.mΩ InitialGaussian.prob

theorem r26t3_initial_gaussian {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) : Nonempty (InitialGaussian R) := by
  classical
  haveI := s21h2_mu_prob hδ hδh R
  obtain ⟨F, hF⟩ := s21h2_form_of_init hδ hδh R
  obtain ⟨e, he⟩ := s21g2_s11a_parseval F.HB
  obtain ⟨Ω, mΩ, P, hPp, ξ, W, hstd, hξ, hWm, hW2, hWlim, hcomb, hcov⟩ := s21g2_s11a_isonormal e he
  let prj : (Euc p.d → ℝ) → F.HB := fun f =>
    if hf : MemLp f 2 (r26t3_mu R 0) then F.toB (s111x2_cl hf) else 0
  refine ⟨⟨Ω, P, ξ, hstd, fun f => W (prj f), fun f _ => hWm _, fun f _ => ?_, fun n f hf => ?_,
    fun f g hf hg => ?_⟩⟩
  · exact s21g2_s11a_firstChaos ξ hξ (fun i => inner ℝ (e i) (prj f)) (hW2 _) (hWlim _)
  · exact s21g2_s11a_gauss_of_laws (aemeasurable_pi_iff.2 fun i => (hWm _).aemeasurable)
      (fun c => ⟨_, hcomb n c (fun i => prj (f i))⟩)
  · show ∫ ω, W (prj f) ω * W (prj g) ω ∂P = _
    rw [hcov, hF f g hf hg]
    simp only [prj, dif_pos hf, dif_pos hg]
    rfl

end HRS.MS.R26T3
