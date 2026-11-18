import HRS.MS.CritForceNF1
import HRS.MS.S82P2Defs
import HRS.MS.S82WP4

/-!
# S8.2 A05 (S82W), part 5: the skeleton definitions `correctedQ, zetaActual, correctedD` and the deleted-diagonal algebra
(`s82n_deleted_canonical_identity` without its unused integrability hypotheses.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

def correctedQ {d N : ℕ} (a beta : ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) :
    EucConfig d N → ℝ :=
  centerUnder (canonicalP d N a beta) (pairStatistic (Psi f))

def zetaActual {d N : ℕ} (a beta : ℝ) (f : Euc d → ℝ) : EucConfig d N → ℝ :=
  fun X => Real.sqrt N * centerUnder (canonicalP d N a beta)
    (fun Y => (1 / (N : ℝ)) * ∑ i, f (Y i)) X

def correctedD {d N : ℕ} (a beta : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) :
    EucConfig d N → ℝ :=
  fun X => centerUnder (canonicalP d N a beta)
    (errorStatistic (critCoeff d a beta rho) rho (Psi f)) X -
      (2 / (N : ℝ)) * zetaActual a beta (aSource (HRS.Whole.withDensityReal rho) f) X

end HRS.MS.Phase2S82

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

theorem w_deleted_identity (d N : ℕ) (hN : 1 ≤ N) (mu : Measure (Euc d))
    (h : Euc d → Euc d → ℝ) (hsym : ∀ x y, h x y = h y x) (X : EucConfig d N) :
    (Real.sqrt N / 2) * centeredPairFunctional h X mu -
      Phase2S82.pairStatistic (fun x y => (1 / 2) * r2CenterKernel mu h x y) X =
        -(N : ℝ) ^ (-(3 / 2 : ℝ)) * (∑ i, ∫ y, h (X i) y ∂mu) +
          (∫ x, ∫ y, h x y ∂mu ∂mu) / (2 * Real.sqrt N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hpos.le
  set I : ℝ := ∫ x, ∫ y, h x y ∂mu ∂mu with hI
  set hm : Euc d → ℝ := fun x => ∫ y, h x y ∂mu with hhm
  have hcol : ∀ y, ∫ x', h x' y ∂mu = hm y := fun y => by
    simp only [hhm]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsym x y)
  have hPS : Phase2S82.pairSum (fun x y => (1 / 2) * r2CenterKernel mu h x y) X =
      (1 / 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)) -
        (((N : ℝ) - 1)) * ∑ i, hm (X i) + ((N : ℝ) * ((N : ℝ) - 1) / 2) * I := by
    unfold Phase2S82.pairSum r2CenterKernel
    have e : ∀ i j, (1 / 2 : ℝ) * (h (X i) (X j) - ∫ y', h (X i) y' ∂mu -
        ∫ x', h x' (X j) ∂mu + I) =
        (1 / 2) * h (X i) (X j) - (1 / 2) * hm (X i) - (1 / 2) * hm (X j) + (1 / 2) * I := by
      intro i j; rw [hcol]; simp only [hhm]; ring
    have S2 : ∑ i, ∑ _j ∈ Finset.univ.erase i, hm (X i) = ((N : ℝ) - 1) * ∑ i, hm (X i) := by
      simp only [HRS.MS.S82N.s82n_sum_erase_const, Fintype.card_fin]
      rw [← Finset.mul_sum]
    have S3 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, hm (X j) =
        ((N : ℝ) - 1) * ∑ i, hm (X i) := by
      have := HRS.MS.S82N.s82n_double_sum_erase (fun j : Fin N => hm (X j))
      simpa only [Fintype.card_fin] using this
    have S4 : ∑ i : Fin N, ∑ _j ∈ Finset.univ.erase i, I = (N : ℝ) * ((N : ℝ) - 1) * I := by
      simp only [HRS.MS.S82N.s82n_sum_erase_const, Fintype.card_fin]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => e i j))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [S2, S3, S4]
    ring
  unfold Phase2S82.pairStatistic centeredPairFunctional
  rw [hPS, HRS.MS.S82N.s82n_rpow_three_half N hN]
  have e1 : (1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂mu = (1 / (N : ℝ)) * ∑ i, hm (X i) := rfl
  rw [e1]
  set s := Real.sqrt N with hsdef
  rw [← hss]
  field_simp
  ring


end HRS.MS.S82W
