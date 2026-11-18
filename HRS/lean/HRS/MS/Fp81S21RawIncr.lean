import HRS.MS.Fp81S21RawGauss4
import HRS.MS.Fp81S21GaussIncrFull4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The squared increment of any combined feature witness is determined by
its covariance Gram entries, so it does not depend on the chosen `KRep`. -/
theorem fp81s21_combinedFeature_increment_sq_cov
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ψ : Euc p.d → ℝ) (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) :
    ‖fp81s21_combinedFeature p R hK t ψ -
        fp81s21_combinedFeature p R hK s ψ‖ ^ 2 =
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t ψ ψ +
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ s s ψ ψ -
          2 * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t s ψ ψ := by
  rw [norm_sub_sq_real,
    ← real_inner_self_eq_norm_sq
      (fp81s21_combinedFeature p R hK t ψ),
    ← real_inner_self_eq_norm_sq
      (fp81s21_combinedFeature p R hK s ψ),
    fp81s21_combinedFeature_gram p hδ hδhalf R hK ht ht hψ hψ,
    fp81s21_combinedFeature_gram p hδ hδhalf R hK hs hs hψ hψ,
    fp81s21_combinedFeature_gram p hδ hδhalf R hK ht hs hψ hψ]
  ring

/-- The raw family's own feature witness inherits the G2 increment estimate.
The outer radius explicitly intersects the raw-family, G2, and trace radii;
G2 chooses the summable mode bound only after the horizon is fixed. -/
theorem fp81s21_raw_feature_increment_bound (p : Parameters) :
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
            ∀ H : ℝ, 0 < H →
              ∃ L : MultiIndex p.d → ℝ,
                (∀ α, 0 ≤ L α) ∧ Summable L ∧
                ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                  ∀ α : MultiIndex p.d,
                    ‖fp81s21_combinedFeature p R hK t
                        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
                      fp81s21_combinedFeature p R hK s
                        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ≤
                      L α * |t - s| := by
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
  obtain ⟨MgR, KR, hKR, VR, hVR, hRawRest⟩ := hRaw δ hδ hδRaw' R
  obtain ⟨MgG, KG, hKG, B, g, g', c, gN, cN,
      hB, hg, hg', hc, hgN, hcN, hG2H⟩ :=
    hG2 δ hδ hδG2' R
  obtain ⟨MgT, KT, hKT, VT, hVT, hTraceTime⟩ :=
    hTrace δ hδ hδTrace' R
  refine ⟨MgR, KR, hKR, VR, hVR, ?_⟩
  intro H hH
  obtain ⟨L, hL0, hLsum, hIncG2⟩ := hG2H H hH
  refine ⟨L, hL0, hLsum, ?_⟩
  intro s hs t ht α
  let ψ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have ht0 : 0 ≤ t := ht.1
  have hs0 : 0 ≤ s := hs.1
  have hG2inc := hIncG2 0 le_rfl s hs t ht α
  have hRawGram := fp81s21_combinedFeature_increment_sq_cov
    p hδ (hδle.trans hδ0Half) R hKR s t hs0 ht0 ψ hψ
  have hG2Gram := fp81s21_combinedFeature_increment_sq_cov
    p hδ (hδle.trans hδ0Half) R hKG
    s t hs0 ht0 ψ hψ
  calc
    ‖fp81s21_combinedFeature p R hKR t ψ -
        fp81s21_combinedFeature p R hKR s ψ‖ ^ 2 =
      HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t t ψ ψ +
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ s s ψ ψ -
          2 * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ t s ψ ψ := by
      simpa [ψ] using hRawGram
    _ = ‖fp81s21_combinedFeature p R hKG t ψ -
          fp81s21_combinedFeature p R hKG s ψ‖ ^ 2 := by
      exact hG2Gram.symm
    _ ≤ L α * |t - s| := by
      simpa [ψ] using hG2inc

#print axioms fp81s21_raw_feature_increment_bound
#print axioms fp81s21_combinedFeature_increment_sq_cov

end HRS.Fp81.S21

end
