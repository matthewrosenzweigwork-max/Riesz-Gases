import HRS.MS.Fp81S21RawGauss2
import HRS.MS.Fp81S21RawGauss3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

private theorem fp81s21_series_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (h : GaussianFeatureHilbert) :
    (∫ ω, W h ω ^ 2 ∂P) = ‖h‖ ^ 2 := by
  have hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨hstd.aemeasurable i,
      by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩
  let a : ℕ → ℝ := fun j => inner ℝ (e j) h
  have hasum : Summable (fun j => a j ^ 2) := by
    simpa [a, sq] using (hParseval h h).summable
  have hvar : (∑' j, a j ^ 2) = ‖h‖ ^ 2 := by
    have ht := (hParseval h h).tsum_eq
    simpa [a, sq, real_inner_self_eq_norm_sq] using ht
  have hlaw := s21g2_s11a_law hξlaw hstd.1 a hasum (hW2 h) (hWlim h)
  rw [s21g2_s11a_second (hW2 h).aemeasurable hlaw, hvar,
    Real.coe_toNNReal _ (sq_nonneg _)]

/-- A measurable, simultaneously coordinate-specified raw OscDual family on
the probability space of the supplied common Gaussian series. Negative times
are clamped to zero. -/
theorem fp81s21_rawGaussianFamily (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
          Lp ℝ 2 (r26t3_mu R 0),
        ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
        ∃ V : ℝ,
          (0 ≤ V ∧ ∀ t : ℝ, 0 ≤ t →
            Summable (fun α : MultiIndex p.d =>
              ‖fp81s21_combinedFeature p R hK t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ∧
            (∑' α : MultiIndex p.d,
              ‖fp81s21_combinedFeature p R hK t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ≤ V) ∧
        ∃ (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
          (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
          (hP : IsProbabilityMeasure P)
          (e : ℕ → GaussianFeatureHilbert)
          (ξ : ℕ → Ω → ℝ) (W : GaussianFeatureHilbert → Ω → ℝ)
          (Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ)),
          (∀ h h' : GaussianFeatureHilbert,
            HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h')
              (inner ℝ h h')) ∧
          HRS.IsStdGaussianSeq P ξ ∧
          (∀ h, Measurable (W h)) ∧
          (∀ h, MemLp (W h) 2 P) ∧
          (∀ h, Tendsto (fun m : ℕ =>
            ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
              atTop (𝓝 0)) ∧
          (∀ r t : ℝ, 0 ≤ r → 0 ≤ t →
            ∀ ψ φ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
              IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
              ∫ ω, W (J (fp81s21_combinedFeature p R hK r ψ)) ω *
                  W (J (fp81s21_combinedFeature p R hK t φ)) ω ∂P =
                HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ r t ψ φ) ∧
          (∀ (n : ℕ) (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ),
            (∀ i, 0 ≤ τ i) →
            (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
            HRS.IsCenteredGaussian
              (P.map fun ω i => W (J (fp81s21_combinedFeature p R hK
                (τ i) (φ i))) ω)) ∧
          (∀ t, Measurable (Z0 t)) ∧
          (∀ t, MemLp (Z0 t) 2 P) ∧
          (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ α : MultiIndex p.d,
            OscDual.coord (Z0 t ω) α =
              W (J (fp81s21_combinedFeature p R hK t
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ∧
          (∀ t : ℝ,
            (∫ ω, ‖Z0 t ω‖ ^ 2 ∂P) =
              ∑' α : MultiIndex p.d,
                ∫ ω, (W (J (fp81s21_combinedFeature p R hK (max t 0)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ^ 2 ∂P) := by
  obtain ⟨δ0, hδ0, hδ0half, hTrace⟩ := fp81s21_combinedFeature_trace p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hμ₀
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  obtain ⟨Mg, K, hK, V, hV, hTraceR⟩ := hTrace δ hδ hδle R
  obtain ⟨J, Ω, mΩ, P, hP, e, ξ, W, hParseval, hstd, hWm, hW2,
      hWlim, hCov, hJoint⟩ :=
    fp81s21_combinedFeature_gaussianSeries p hδ
      (hδle.trans hδ0half) R hμ₀ hK
  letI : IsProbabilityMeasure P := hP
  let f : ℝ → MultiIndex p.d → Ω → ℝ := fun u α ω =>
    W (J (fp81s21_combinedFeature p R hK u
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω
  have hcoords : ∀ u : ℝ, 0 ≤ u → ∃ q : Ω → OscDual p.d
      (wholeSpaceIndex p.d : ℝ),
      Measurable q ∧ MemLp q 2 P ∧
        (∀ᵐ ω ∂P, ∀ α, OscDual.coord (q ω) α = f u α ω) ∧
        (∫ ω, ‖q ω‖ ^ 2 ∂P) = ∑' α, ∫ ω, f u α ω ^ 2 ∂P := by
    intro u hu
    have hmem : ∀ α, MemLp (f u α) 2 P := fun α => hW2 _
    have hsecond : ∀ α,
        (∫ ω, f u α ω ^ 2 ∂P) =
          ‖fp81s21_combinedFeature p R hK u
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 := by
      intro α
      rw [fp81s21_series_second_moment e ξ W hParseval hstd hW2 hWlim,
        J.norm_map]
    have hsum : Summable (fun α => ∫ ω, f u α ω ^ 2 ∂P) := by
      apply (hTraceR u hu).1.congr
      intro α
      rw [hsecond]
    exact fp81s21_oscDual_of_coordinates (f u) hmem hsum
  let Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) := fun t =>
    Classical.choose (hcoords (max t 0) (le_max_right t 0))
  have hspec (t : ℝ) := Classical.choose_spec
    (hcoords (max t 0) (le_max_right t 0))
  refine ⟨Mg, K, hK, V, ⟨hV, hTraceR⟩,
    J, Ω, mΩ, P, hP, e, ξ, W, Z0,
    hParseval, hstd, hWm, hW2, hWlim, hCov, hJoint, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hspec t).1
  · intro t
    exact (hspec t).2.1
  · intro t ht
    have htmax : max t 0 = t := max_eq_left ht
    simpa [Z0, f, htmax] using (hspec t).2.2.1
  · intro t
    simpa [Z0, f] using (hspec t).2.2.2

#print axioms fp81s21_rawGaussianFamily

end HRS.Fp81.S21

end
