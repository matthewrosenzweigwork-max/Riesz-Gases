import HRS.MS.SA12X3C9C
import HRS.MS.SA12CellC8B
import HRS.MS.MovForceAux2

/-!
# S.A.12 C9 (SA12X3), part D: the jets of `νΔF + ⟨b,∇F⟩ + G`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3_pd_lap {n : ℕ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (ν : ℝ) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ν * Laplacian.laplacian F y) x =
      ν * ∑ i : Fin d, D1 i (D1 i (partialDeriv idx F)) x := by
  have hF2 : ContDiff ℝ 2 F := sa12z3_cd_of_inf hF 2
  have e1 : (fun y => ν * Laplacian.laplacian F y) = fun y => ∑ i ∈ (Finset.univ : Finset (Fin d)),
      (fun _ => ν) i * (fun i y => D1 i (D1 i F) y) i y := by
    funext y; rw [HRS.MS.MovForce.mv1_laplacian_eq hF2, Finset.mul_sum]; rfl
  have hD : ∀ i : Fin d, ContDiff ℝ n (D1 i (D1 i F)) := fun i =>
    sa12z3_cd_of_inf (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff hF i) i) n
  rw [e1, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => D1 i (D1 i F) y) (fun _ => ν) (n := n)
    (fun i _ => hD i) idx x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h1 := sa12z3_pd_D1_comm i n (D1 i F) (sa12z3_cd_of_inf (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff hF i) _) idx x
  rw [h1]
  have h2 : partialDeriv idx (D1 i F) = D1 i (partialDeriv idx F) :=
    funext fun y => sa12z3_pd_D1_comm i n F (sa12z3_cd_of_inf hF _) idx y
  rw [h2]

theorem sa12x3_pd_rate {m n : ℕ} (hn : n ≤ m) {b : Euc d → Euc d} (hbC : ContDiff ℝ (m + 1) b) {F G : Euc d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (ν : ℝ) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x =
      ν * ∑ i : Fin d, D1 i (D1 i (partialDeriv idx F)) x +
        partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x + partialDeriv idx G x := by
  have hbi : ∀ i : Fin d, ContDiff ℝ n (fun y => b y i) := fun i =>
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC).of_le (by exact_mod_cast (by omega : n ≤ m + 1))
  have hD1 : ∀ i : Fin d, ContDiff ℝ n (D1 i F) := fun i => sa12z3_cd_of_inf (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff hF i) n
  have hlap : ContDiff ℝ n (fun y => ν * Laplacian.laplacian F y) := by
    have : (fun y => ν * Laplacian.laplacian F y) = fun y => ν * ∑ i : Fin d, D1 i (D1 i F) y := by
      funext y; rw [HRS.MS.MovForce.mv1_laplacian_eq (sa12z3_cd_of_inf hF 2)]; rfl
    rw [this]
    exact contDiff_const.mul (ContDiff.sum fun i _ =>
      sa12z3_cd_of_inf (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff (HRS.MH.AdjointRd.Phase2SA12Construction.sa12y_D1_contDiff hF i) i) n)
  have hin : ContDiff ℝ n (fun y => inner ℝ (b y) (gradient F y)) := by
    have : (fun y => inner ℝ (b y) (gradient F y)) = fun y => ∑ i : Fin d, b y i * D1 i F y := by
      funext y; rw [sa12x3_inner_grad]
    rw [this]
    exact ContDiff.sum fun i _ => (hbi i).mul (hD1 i)
  have hGn : ContDiff ℝ n G := sa12z3_cd_of_inf hG n
  rw [sa12x3_pd_add (hlap.add hin) hGn, sa12x3_pd_add hlap hin, sa12x3_pd_lap hF ν idx x]

end HRS.MH.AdjointRd.Phase2SA12Near
