import HRS.MS.Fp81S21GaussianCoordChaos
import HRS.MS.Fp81S21GaussTimeRep3
import HRS.MS.Fp81S21WickApprox33

/-! Packet 35, unit 2: testwise weighted source agreement and first chaos of
 the actual selected weak linear field. Charts precede the trajectory radius;
 the retained source, canonical field/payload, and quadratic selectors are explicit.
 No Gaussian35Selection record or new source/operator selection is used.
 The realization-local inputs are exactly `canon.q src.G0` and
 `canon.payload src.G0`; the full realization-indexed family is unnecessary.
 This also avoids the WindowSup/WickFam11 compiled instance-name collision
 incurred by importing VersionGTime2 alongside the Wick operator modules.

 The normalized chart embedding used by the coordinate producer is supplied
 by embedding the canonical strong MomentRep. This avoids assuming that the
 two differently transported embedding definitions are definitionally equal.
 All weighted equalities remain fixed-time, fixed-test almost-everywhere claims.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The selected linear and half-Wick operators represent the physical weak
fields on every weighted test, and the weak linear coordinates lie in first
chaos of the measurable coordinates of the same retained source. -/
theorem fp81s21_gaussian35_source_agreement
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {δ : ℝ} (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    (src : fp81s21_gaussian_source_retained_data p R hμ₀)
    (MUG : ℝ) (εG εB : ℕ → ℝ)
    (qsG : ℝ → src.G0.Ω → r26t6_Coeff)
    (hcanon : fp81s21_gaussian_canonical_time_payload p Es E src.G0.P
      (fun u ω f => OscDual.eval (src.G0.Z u ω) f) MUG qsG
      (fp81s21_gaussian_embedFamily p Es E qsG) εG)
    (S : fp81s21_QuadraticPhysical31 p R Es E εB) :
    let qG := fp81s21_gaussian_embedFamily p Es E qsG
    let μ := HRS.Whole.withDensityReal R.ρβ
    let kf := fun (f : Euc p.d → ℝ) (xy : Euc p.d × Euc p.d) =>
      commutatorKernel p.d p.s (gradient f) xy.1 xy.2
    (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      ∃ hf : MemLp f 2 μ, ∃ hk : MemLp (kf f) 2 (μ.prod μ),
        (fun ω => fp81s21_chartAction E (qG u ω) f) =ᵐ[src.G0.P]
          (S.T src.G0 u (hf.toLp f) : src.G0.Ω → ℝ) ∧
        (fun ω => fp81s21_chartAction E (S.qe src.G0 u ω) f) =ᵐ[src.G0.P]
          (S.W src.G0 u (hk.toLp (kf f)) : src.G0.Ω → ℝ)) ∧
    (∀ u : ℝ, 0 ≤ u → ∀ j : ℕ,
      InFirstChaos src.G0.P (fp81s21_gaussian_source_measurableXi src) 2
        (fun ω => qG u ω j)) := by
  dsimp only
  let qG := fp81s21_gaussian_embedFamily p Es E qsG
  have hG := hcanon.coefficients.weak_momentRep
  have hB := (S.payload src.G0).2.2.2.2.1
  have hTosc : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      (S.T src.G0 u (fp81s21_gaussianSourceSpace_oscTestLp p R φ) :
        src.G0.Ω → ℝ) =ᵐ[src.G0.P]
          (fun ω => OscDual.eval (src.G0.Z u ω) φ.1) := by
    intro u hu φ
    exact (S.payload src.G0).2.1 u hu φ.1 φ.2
      (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ)
  have hcompactG : ∀ u : ℝ, 0 ≤ u → ∀ g : Euc p.d → ℝ,
      IsR2Test g → ∀ hg : MemLp g 2 (HRS.Whole.withDensityReal R.ρβ),
        (fun ω => fp81s21_chartAction E (qG u ω) g) =ᵐ[src.G0.P]
          (S.T src.G0 u (hg.toLp g) : src.G0.Ω → ℝ) := by
    intro u hu g hg hgμ
    have hT := (S.payload src.G0).2.1 u hu g
      (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hg) hgμ
    filter_upwards [(hG.2 u hu).2.2, hT] with ω hω hTω
    exact (hω.1 g hg).trans hTω.symm
  have hcompactB : ∀ u : ℝ, 0 ≤ u → ∀ g : Euc p.d → ℝ,
      IsR2Test g → ∀ hk : MemLp (fun xy : Euc p.d × Euc p.d =>
        commutatorKernel p.d p.s (gradient g) xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
        (fun ω => fp81s21_chartAction E (S.qe src.G0 u ω) g) =ᵐ[src.G0.P]
          (S.W src.G0 u (hk.toLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient g) xy.1 xy.2)) : src.G0.Ω → ℝ) := by
    intro u hu g hg hk
    obtain ⟨hk', hag⟩ := (S.payload src.G0).2.2.2.2.2.1 u hu g hg
    filter_upwards [(hB.2 u hu).2.2, hag] with ω hω hagω
    exact (hω.1 g hg).trans hagω
  constructor
  · intro u hu f hfW
    obtain ⟨hf, hlinear⟩ := fp81s21_linear_weighted_agreement_time
      p R E src.G0.P (S.T src.G0) qG
      (fun v hv => (hG.2 v hv).1) hcompactG u hu f hfW
    obtain ⟨hk, hwick⟩ := fp81s21_wick_weighted_agreement_time
      p R E src.G0.P (S.W src.G0) (S.qe src.G0)
      (fun v hv => (hB.2 v hv).1) hcompactB u hu f hfW
    exact ⟨hf, hk, hlinear, hwick⟩
  · have hweak : fp81s21_MomentRep E src.G0.P
        (fun u ω f => OscDual.eval (src.G0.Z u ω) f)
        (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω))
        MUG :=
      fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
        (by nlinarith) (by nlinarith) Es E src.G0.P
        (fun u ω f => OscDual.eval (src.G0.Z u ω) f) qsG MUG
        hcanon.coefficients.strong_momentRep
    exact fp81s21_gaussian_V2_G_canonical_hcoord p Es E R hμ₀ src
      (S.T src.G0) hTosc qsG MUG hG MUG qsG hweak

#print axioms fp81s21_gaussian35_source_agreement

end HRS.Fp81.S21
end
