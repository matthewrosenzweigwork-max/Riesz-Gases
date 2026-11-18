import HRS.Main.GFB2Aux6
import HRS.Energy.Commutator.Assembly

/-!
# Packet GFB2, part 7: `flucInteraction` is half the commutator quantity (`gf_remainder_pointwise`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_integral_empirical {N : ℕ} (X : Config d N) (f : Torus d → ℝ) :
    ∫ x, f x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.mul_sum]
  · intro i _
    exact integrable_dirac enorm_lt_top

/-- The vector field of the commutator quantity: `v = Mᵀ ∇ψ`. -/
def gfb2_v (M : Matrix (Fin d) (Fin d) ℝ) (ψ : Torus d → ℝ) (x : Torus d) : Euc d :=
  Torus.matVec M.transpose (Torus.grad ψ x)

theorem gfb2_commKernel_eq (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (ψ : Torus d → ℝ) (x y : Torus d) :
    commKernel (periodicRieszGrad d s) (gfb2_v M ψ) x y =
      if x = y then 0 else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
        (Torus.matVec M (periodicRieszGrad d s (x - y))) := by
  unfold commKernel gfb2_v
  by_cases h : x = y
  · simp [h]
  · simp only [h, if_false]
    rw [Duality.inner_matVec_transpose]
    congr 1
    unfold Torus.matVec
    rw [map_sub]

theorem gfb2_commKernel_symm {s : ℝ} (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ψ : Torus d → ℝ)
    (x y : Torus d) :
    commKernel (periodicRieszGrad d s) (gfb2_v M ψ) x y =
      commKernel (periodicRieszGrad d s) (gfb2_v M ψ) y x := by
  rw [gfb2_commKernel_eq, gfb2_commKernel_eq]
  by_cases h : x = y
  · simp [h]
  · have h' : y ≠ x := Ne.symm h
    simp only [h, h', if_false]
    have e : y - x = -(x - y) := by abel
    rw [e, PDE.periodicRieszGrad_neg hsd]
    have : Torus.matVec M (-periodicRieszGrad d s (x - y)) = -Torus.matVec M (periodicRieszGrad d s (x - y)) := by
      unfold Torus.matVec; rw [map_neg]
    rw [this, inner_neg_right, ← inner_neg_left, neg_sub]


theorem gfb2_matVec_continuous (M : Matrix (Fin d) (Fin d) ℝ) : Continuous (Torus.matVec M) :=
  (Matrix.toEuclideanLin M).continuous_of_finiteDimensional

theorem gfb2_v_continuous (M : Matrix (Fin d) (Fin d) ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Continuous (gfb2_v M ψ) :=
  (gfb2_matVec_continuous M.transpose).comp (PDE.MFLinear.continuous_grad (Q54c.isCk_one_of_two hψ))

theorem gfb2_commKernel_measurable {s : ℝ} (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) (x : Torus d) :
    Measurable (commKernel (periodicRieszGrad d s) (gfb2_v M ψ) x) := by
  unfold commKernel
  refine Measurable.ite ?_ measurable_const ?_
  · have : {y : Torus d | x = y} = {x} := Set.ext fun y => eq_comm
    rw [this]; exact measurableSet_singleton x
  · exact ((measurable_const.sub (gfb2_v_continuous M hψ).measurable).inner
      ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_const.sub measurable_id)))


theorem gfb2_flucInteraction_eq (D : DynData d) {N : ℕ} {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ)
    (X : Config d N) (ρ : Torus d → ℝ)
    (hint : ∀ i, Integrable (fun y => commKernel (periodicRieszGrad d D.s) (gfb2_v D.M ψ) (X i) y)
      (withDensityReal ρ)) :
    flucInteraction D ψ X ρ =
      (1 / 2) * commQuantity d D.s (gfb2_v D.M ψ) X (withDensityReal ρ) := by
  set k := commKernel (periodicRieszGrad d D.s) (gfb2_v D.M ψ) with hk
  have hsd := D.hsd
  have hkIP : ∀ x y : Torus d, (if x = y then (0 : ℝ) else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
      (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))) = k x y := fun x y =>
    (gfb2_commKernel_eq D.M D.s ψ x y).symm
  have hsymm : ∀ x y, k x y = k y x := gfb2_commKernel_symm hsd D.M ψ
  have hkm : ∀ x, Measurable (k x) := gfb2_commKernel_measurable hsd D.M hψ
  have hkm' : ∀ y, Measurable (fun x => k x y) := fun y => by
    have : (fun x => k x y) = k y := funext fun x => hsymm x y
    rw [this]; exact hkm y
  have hdiag : ∀ x, k x x = 0 := fun x => by rw [← hkIP]; simp
  have hinner : ∀ x, ∫ y, k x y ∂(empirical X) = (N : ℝ)⁻¹ * ∑ j, k x (X j) :=
    fun x => gfb2_integral_empirical X (k x)
  -- the four interaction pairings
  have hee : interactionPairing D ψ (empirical X) (empirical X) =
      (1 / 2) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)) := by
    unfold interactionPairing
    simp only [hkIP]
    simp only [hinner]
    rw [gfb2_integral_empirical X]
    congr 1
    have e : ∀ i : Fin N, ∑ j, k (X i) (X j) = ∑ j ∈ Finset.univ.erase i, k (X i) (X j) := fun i => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, zero_add]
    simp only [e, ← Finset.mul_sum]
    ring
  have her : interactionPairing D ψ (empirical X) (withDensityReal ρ) =
      (1 / 2) * ((N : ℝ)⁻¹ * ∑ i, ∫ y, k (X i) y ∂(withDensityReal ρ)) := by
    unfold interactionPairing
    simp only [hkIP]
    rw [gfb2_integral_empirical X]
  have hre : interactionPairing D ψ (withDensityReal ρ) (empirical X) =
      (1 / 2) * ((N : ℝ)⁻¹ * ∑ j, ∫ y, k (X j) y ∂(withDensityReal ρ)) := by
    unfold interactionPairing
    simp only [hkIP, hinner]
    have hj : ∀ j, Integrable (fun x => k x (X j)) (withDensityReal ρ) := fun j => by
      have : (fun x => k x (X j)) = k (X j) := funext fun x => hsymm x (X j)
      rw [this]; exact hint j
    rw [integral_const_mul, integral_finset_sum _ fun j _ => hj j]
    congr 3
    funext j
    exact integral_congr_ae (Eventually.of_forall fun x => hsymm x (X j))
  have hrr : interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      (1 / 2) * ∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    unfold interactionPairing
    simp only [hkIP]
  unfold flucInteraction commQuantity commQuantityWith offDiagPairing
  rw [hee, her, hre, hrr]
  ring

end HRS.GF
