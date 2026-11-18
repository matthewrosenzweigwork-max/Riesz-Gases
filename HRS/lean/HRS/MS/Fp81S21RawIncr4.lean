import HRS.MS.Fp81S21RawIncr3
import HRS.MS.Fp81S21GaussIncrFull4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Classical Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- On the raw family's retained probability space, G2's summable feature
increment bound transfers to its own KRep witness and yields the local
fourth-moment hypothesis for every positive horizon. -/
theorem fp81s21_rawGaussianFamily_fourth_increment (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)],
          ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
            Lp ℝ 2 (r26t3_mu R 0),
          ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
          ∃ V : ℝ,
            (0 ≤ V ∧ ∀ u : ℝ, 0 ≤ u →
              Summable (fun α : MultiIndex p.d =>
                ‖fp81s21_combinedFeature p R hK u
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2) ∧
              (∑' α : MultiIndex p.d,
                ‖fp81s21_combinedFeature p R hK u
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
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) ω) ^ 2 ∂P) ∧
            ∀ H : ℝ, 0 < H →
              ∃ L : MultiIndex p.d → ℝ,
                (∀ α, 0 ≤ L α) ∧ Summable L ∧
                ∃ C : ℝ, C = 3 * (∑' α : MultiIndex p.d, L α) ^ 2 ∧
                  0 ≤ C ∧
                  ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                    ∫⁻ ω, ‖Z0 t ω - Z0 s ω‖ₑ ^ (4 : ℝ) ∂P ≤
                      ENNReal.ofReal (C * |t - s| ^ 2) := by
  obtain ⟨δRaw, hδRaw, hδRawHalf, hRaw⟩ := fp81s21_rawGaussianFamily p
  obtain ⟨δG2, hδG2, hδG2Half, hG2⟩ :=
    fp81s21_gaussian_combined_feature_increment_bound p
  obtain ⟨δTrace, hδTrace, hδTraceHalf, hTrace⟩ :=
    fp81s21_combinedFeature_trace p
  let δ0 := min δRaw (min δG2 δTrace)
  have hδ0 : 0 < δ0 := lt_min hδRaw (lt_min hδG2 hδTrace)
  have hδ0Half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδRawHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R hμ
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hδRaw' : δ ≤ δRaw := hδle.trans (min_le_left _ _)
  have hδG2' : δ ≤ δG2 :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδTrace' : δ ≤ δTrace :=
    hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨MgR, KR, hKR, VR, hVR, J, Ω, mΩ, P, hP, e, ξ, W, Z0,
      hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
      hZmeas, hZmem, hcoord, hZsecond⟩ := hRaw δ hδ hδRaw' R
  letI : IsProbabilityMeasure P := hP
  obtain ⟨MgG, KG, hKG, B, g, g', c, gN, cN,
      hB, hg, hg', hc, hgN, hcN, hG2H⟩ := hG2 δ hδ hδG2' R
  obtain ⟨MgT, KT, hKT, VT, hVT, hTraceTime⟩ :=
    hTrace δ hδ hδTrace' R
  refine ⟨MgR, KR, hKR, VR, hVR,
    J, Ω, mΩ, P, hP, e, ξ, W, Z0,
    hParseval, hstd, hWmeas, hW2, hWlim, hCov, hJoint,
    hZmeas, hZmem, hcoord, hZsecond, ?_⟩
  intro H hH
  obtain ⟨L, hL0, hLsum, hG2inc⟩ := hG2H H hH
  refine ⟨L, hL0, hLsum, ?_⟩
  let C : ℝ := 3 * (∑' α : MultiIndex p.d, L α) ^ 2
  have hCeq : C = 3 * (∑' α : MultiIndex p.d, L α) ^ 2 := rfl
  have hsumL0 : 0 ≤ ∑' α : MultiIndex p.d, L α :=
    tsum_nonneg fun α => hL0 α
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoord4 : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∀ α : MultiIndex p.d,
        ∫⁻ ω, ‖OscDual.coord (Z0 t ω) α - OscDual.coord (Z0 s ω) α‖ₑ ^
          (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * (L α * |t - s|) ^ 2) := by
    intro s hs t ht α
    let ψ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ :=
      HRS.MS.GenPath.s56_isOscTest _ α
    have hG2bound := hG2inc 0 le_rfl s hs t ht α
    have hRawGram := fp81s21_combinedFeature_increment_sq_cov
      p hδ (hδle.trans hδ0Half) R hKR s t hs.1 ht.1 ψ hψ
    have hG2Gram := fp81s21_combinedFeature_increment_sq_cov
      p hδ (hδle.trans hδ0Half) R hKG s t hs.1 ht.1 ψ hψ
    have hFeatureBound :
        ‖fp81s21_combinedFeature p R hKR t ψ -
          fp81s21_combinedFeature p R hKR s ψ‖ ^ 2 ≤ L α * |t - s| := by
      calc
        ‖fp81s21_combinedFeature p R hKR t ψ -
            fp81s21_combinedFeature p R hKR s ψ‖ ^ 2 =
            HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t ψ ψ +
              HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ s s ψ ψ -
                2 * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t s ψ ψ :=
          hRawGram
        _ = ‖fp81s21_combinedFeature p R hKG t ψ -
              fp81s21_combinedFeature p R hKG s ψ‖ ^ 2 := hG2Gram.symm
        _ ≤ L α * |t - s| := by simpa [ψ] using hG2bound
    have hScalar := fp81s21_raw_scalar_increment_fourth
      p hδ (hδle.trans hδ0Half) R hKR J e ξ W Z0 hParseval hstd
      hWmeas hW2 hWlim hJoint hZmeas hcoord s t H hs ht α L
      (hL0 α) (by simpa [ψ] using hFeatureBound)
    exact hScalar.2.2.2.2
  have hNorm := fp81s21_raw_increment_norm_fourth
    Z0 hZmeas L hL0 hLsum H hH hcoord4
  refine ⟨C, hCeq, hC0, ?_⟩
  intro s hs t ht
  simpa [C] using hNorm s hs t ht

#print axioms fp81s21_rawGaussianFamily_fourth_increment

end HRS.Fp81.S21

end
