import HRS.MS.S82WQ2
import HRS.MS.S82WN2

/-!
# S8.2 A05 (S82W), part 7: the exact identity `scalarForcing = -L(correctedQ) + correctedD`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

section ident
variable {d N : ℕ}

lemma w_gen_const (c a beta : ℝ) (X : EucConfig d N) :
    particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (fun _ : EucConfig d N => c) X = 0 := by
  unfold particleGenerator Phase2S82.configGrad
  simp

lemma w_gen_shift {a beta : ℝ} {φ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ) (c : ℝ)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (fun Y => φ Y - c) X =
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X := by
  rw [HRS.MS.S82W.w_gen_sub (ψ := fun _ => c) hφ contDiffOn_const hX, w_gen_const, sub_zero]

lemma w_hSource_symm (f : Euc d → ℝ) (x y : Euc d) : hSource f x y = hSource f y x := by
  by_cases h : x = y
  · subst h; rfl
  · have hne : x - y ≠ 0 := sub_ne_zero.2 h
    unfold hSource commutatorKernel
    rw [show y - x = -(x - y) by abel, w_rieszGrad_odd (criticalS d) hne, ← neg_sub (gradient f x) (gradient f y),
      inner_neg_neg]

theorem w_forcing_identity (hd : 2 ≤ d) (hN : 2 ≤ N) {a beta : ℝ} {rho : Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)] [IsProbabilityMeasure (canonicalP d N a beta)]
    {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ} {f : Euc d → ℝ}
    (hFcd : ContDiffOn ℝ 2 (fun X : EucConfig d N => Phase2S82.pairStatistic (Psi f) X) (eucCollisionSet d N)ᶜ)
    (hA02 : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Phase2S82.pairStatistic (Psi f)) X =
        -Phase2S82.pairStatistic (HSource (HRS.Whole.withDensityReal rho) f) X +
          errorStatistic (critCoeff d a beta rho) rho (Psi f) X)
    (hErr : Integrable (errorStatistic (critCoeff d a beta rho) rho (Psi f)) (canonicalP d N a beta))
    (hLmem : MemLp (particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
      (correctedQ (N := N) a beta Psi f)) 2 (canonicalP d N a beta))
    (hmean : ∫ X, particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
      (correctedQ (N := N) a beta Psi f) X ∂(canonicalP d N a beta) = 0)
    (haS : Integrable (fun Y : EucConfig d N => ∑ i, aSource (HRS.Whole.withDensityReal rho) f (Y i))
      (canonicalP d N a beta)) :
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      scalarForcing a beta rho f X =
        -particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (correctedQ (N := N) a beta Psi f) X +
          correctedD a beta rho Psi f X := by
  intro X hX
  set P := canonicalP d N a beta with hP
  set μ := HRS.Whole.withDensityReal rho with hμ
  have hN1 : 1 ≤ N := by omega
  have hae : ∀ᵐ Y ∂P, Y ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  set c1 := ∫ Y, Phase2S82.pairStatistic (Psi f) Y ∂P with hc1
  have hcQ : correctedQ (N := N) a beta Psi f = fun Y => Phase2S82.pairStatistic (Psi f) Y - c1 := rfl
  have hLQ : ∀ Y : EucConfig d N, Y ∉ eucCollisionSet d N →
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (correctedQ (N := N) a beta Psi f) Y =
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Phase2S82.pairStatistic (Psi f)) Y := by
    intro Y hY; rw [hcQ]; exact w_gen_shift hFcd c1 hY
  set psHS : EucConfig d N → ℝ := fun Y => Phase2S82.pairStatistic (HSource μ f) Y with hpsHS
  set err := errorStatistic (critCoeff d a beta rho) rho (Psi f) with herr
  have hpsae : psHS =ᵐ[P] fun Y => err Y -
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (correctedQ (N := N) a beta Psi f) Y := by
    filter_upwards [hae] with Y hY
    rw [hLQ Y hY, hA02 Y hY]; ring
  have hpsint : Integrable psHS P :=
    (hErr.sub (hLmem.integrable (by norm_num))).congr hpsae.symm
  have herr_eq : ∫ Y, err Y ∂P = ∫ Y, psHS Y ∂P := by
    rw [integral_congr_ae hpsae, integral_sub hErr (hLmem.integrable (by norm_num)), hmean, sub_zero]
  -- the algebraic identity at every configuration
  set s := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hN1 : (0 : ℝ) < N)
  have hss : s * s = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  set I : ℝ := ∫ x, ∫ y, hSource f x y ∂μ ∂μ with hI
  set S : EucConfig d N → ℝ := fun Y => ∑ i, aSource μ f (Y i) with hSdef
  have key : ∀ Y : EucConfig d N, (s / 2) * centeredPairFunctional (hSource f) Y μ =
      psHS Y - 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * S Y + I / (2 * s) := by
    intro Y
    have := w_deleted_identity d N hN1 μ (hSource f) (w_hSource_symm f) Y
    have e : ∑ i, ∫ y, hSource f (Y i) y ∂μ = 2 * S Y := by
      simp only [hSdef, aSource, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e] at this
    show (s / 2) * centeredPairFunctional (hSource f) Y μ = Phase2S82.pairStatistic (HSource μ f) Y - _ + _
    unfold HSource
    linarith
  set g : EucConfig d N → ℝ := fun Y => centeredPairFunctional (hSource f) Y μ with hg
  have hint : ∫ Y, (s / 2) * g Y ∂P = ∫ Y, psHS Y ∂P - 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∫ Y, S Y ∂P + I / (2 * s) := by
    have e : (fun Y => (s / 2) * g Y) = fun Y => psHS Y - 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * S Y + I / (2 * s) :=
      funext key
    have i1 : Integrable (fun Y => psHS Y - 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * S Y) P :=
      hpsint.sub (haS.const_mul _)
    have h1 := integral_add i1 (integrable_const (I / (2 * s)) (μ := P))
    have h2 := integral_sub hpsint (haS.const_mul (2 * (N : ℝ) ^ (-(3 / 2 : ℝ))))
    rw [e, h1, h2, integral_const_mul, integral_const]
    simp
  have hSc : (fun Y : EucConfig d N => (1 / (N : ℝ)) * ∑ i, aSource μ f (Y i)) = fun Y => (1 / (N : ℝ)) * S Y := rfl
  -- unfold the three sides
  have hLHS : scalarForcing a beta rho f X = (s / 2) * g X - ∫ Y, (s / 2) * g Y ∂P := by
    unfold scalarForcing centerUnder
    rw [integral_const_mul]; ring
  have hD : correctedD (N := N) a beta rho Psi f X = (err X - ∫ Y, err Y ∂P) -
      (2 / (N : ℝ)) * (s * ((1 / (N : ℝ)) * S X - ∫ Y, (1 / (N : ℝ)) * S Y ∂P)) := by
    unfold correctedD zetaActual centerUnder
    rfl
  have hz : ∫ Y, (1 / (N : ℝ)) * S Y ∂P = (1 / (N : ℝ)) * ∫ Y, S Y ∂P := integral_const_mul _ _
  rw [hLHS, hD, hLQ X hX, hA02 X hX, key X, hint, herr_eq, hz]
  have h32 : (N : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((N : ℝ) * s) :=
    HRS.MS.S82N.s82n_rpow_three_half N hN1
  rw [h32]
  have hN' : (N : ℝ) = s * s := hss.symm
  rw [hN']
  field_simp
  ring

end ident

end HRS.MS.S82W
