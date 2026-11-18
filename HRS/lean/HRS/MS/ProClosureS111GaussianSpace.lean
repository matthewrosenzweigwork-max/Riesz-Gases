import HRS.MS.ProClosureS111GaussianLaw
import HRS.MS.S111BDAux4
import HRS.MC.QRPWickAux1
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The actual common Gaussian observation space for the accepted Wick contraction

The accepted Hilbert--Schmidt contraction `r26t3_kernel_wick_pair` requires
one linear space whose members have the Gaussian fourth moment. This file
constructs that space from the mixed finite-dimensional law, rather than
assuming that separately Gaussian observations are jointly Gaussian.

The physical specialization uses exactly SharedThermalLaw, including mixed
sides and times. The fourth moment and Wick pairing themselves are reused
from the accepted QRPWick source.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T HRS.MS.S111X1
open HRS.MC.QRSpec.Wick

variable {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
  [IsProbabilityMeasure P]

/-- Every finite linear combination of one jointly centered Gaussian family
belongs to one genuine linear subspace with the required fourth moments. -/
theorem gaussian_linear_space_of_finite_laws {J : Type*}
    (Z : J → Omega → ℝ) (hZm : ∀ j, Measurable (Z j))
    (hfinite : ∀ n : ℕ, ∀ j : Fin n → J,
      HRS.IsCenteredGaussian (P.map (fun w =>
        (WithLp.toLp 2 (fun i => Z (j i) w) : EuclideanSpace ℝ (Fin n))))) :
    ∃ G : Submodule ℝ (Omega → ℝ), (∀ j, Z j ∈ G) ∧ QrpwG4 P G := by
  let A : (J →₀ ℝ) →ₗ[ℝ] (Omega → ℝ) := Finsupp.linearCombination ℝ Z
  refine ⟨A.range, ?_, ?_⟩
  · intro j
    refine ⟨Finsupp.single j 1, ?_⟩
    simp [A, Finsupp.linearCombination_single]
  · intro W hW
    obtain ⟨c, rfl⟩ := hW
    let e : c.support ≃ Fin c.support.card := c.support.equivFin
    let j : Fin c.support.card → J := fun i => (e.symm i : c.support)
    let V : Omega → EuclideanSpace ℝ (Fin c.support.card) :=
      fun w => WithLp.toLp 2 (fun i => Z (j i) w)
    let L : EuclideanSpace ℝ (Fin c.support.card) →L[ℝ] ℝ :=
      ∑ i, (c (j i)) • (EuclideanSpace.proj i)
    have hVm : Measurable V :=
      (WithLp.measurable_toLp 2 (Fin c.support.card → ℝ)).comp
        (measurable_pi_iff.2 fun i => hZm (j i))
    have hV := hfinite c.support.card j
    have hLaw : HasGaussianLaw V P := HasGaussianLaw.mk hVm.aemeasurable hV.1
    have hLW : A c = fun w => L (V w) := by
      funext w
      simp only [A, Finsupp.linearCombination_apply, Finsupp.sum,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [L, V, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, PiLp.toLp_apply, smul_eq_mul]
      change (∑ q ∈ c.support, c q * Z q w) =
        ∑ i : Fin c.support.card, c (j i) * Z (j i) w
      rw [← Finset.sum_coe_sort c.support]
      exact (Equiv.sum_comp e.symm
        (fun q : c.support => c q * Z q w)).symm
    have hmean : (∫ w, L (V w) ∂P) = 0 := by
      rw [← integral_map hVm.aemeasurable L.continuous.aestronglyMeasurable]
      exact hV.2 L
    rw [hLW]
    exact qrpw_gauss4 (hLaw.map_fun L) hmean

/-- All physical observations of the paired evolution, at all allowed times,
lie in the same Gaussian linear space used by the accepted kernel contraction.
No independence between time observations is asserted. -/
theorem physical_observation_gaussian_space {d : ℕ} {s a beta gamma H : ℝ}
    {rho : Euc d → ℝ}
    (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z) :
    ∃ G : Submodule ℝ (Omega → ℝ), QrpwG4 P G ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) H,
      ∀ phi : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) phi →
        (fun w => OscDual.eval (Z i t w) phi) ∈ G := by
  let J := Fin 2 × (Set.Icc (0 : ℝ) H × oscSub d (wholeSpaceIndex d))
  let O : J → Omega → ℝ := fun j w =>
    OscDual.eval (Z j.1 j.2.1 w) (j.2.2 : Euc d → ℝ)
  have hOm : ∀ j, Measurable (O j) := by
    intro j
    have heq : O j = fun w => gaussianOscEval j.2.2 (Z j.1 j.2.1 w) := by
      funext w
      exact (gaussianOscEval_apply j.2.2 _).symm
    rw [heq]
    exact (gaussianOscEval j.2.2).continuous.measurable.comp
      ((hZ.evolution j.1).meas j.2.1)
  have hfinite : ∀ n : ℕ, ∀ j : Fin n → J,
      HRS.IsCenteredGaussian (P.map (fun w =>
        (WithLp.toLp 2 (fun i => O (j i) w) : EuclideanSpace ℝ (Fin n)))) := by
    intro n j
    have h := hZ.joint n (fun i => (j i).1) (fun i => (j i).2.1)
      (fun i => ((j i).2.2 : Euc d → ℝ))
      (fun i => (j i).2.1.property) (fun i => (j i).2.2.property)
    change HRS.IsCenteredGaussian (P.map (fun w =>
      (WithLp.toLp 2 (fun i =>
        OscDual.eval (Z (j i).1 (j i).2.1 w) ((j i).2.2 : Euc d → ℝ)) :
          EuclideanSpace ℝ (Fin n))))
    rw [h]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg n _
  obtain ⟨G, hobs, hG⟩ := gaussian_linear_space_of_finite_laws O hOm hfinite
  refine ⟨G, hG, fun i t ht phi hphi => ?_⟩
  exact hobs (i, ⟨t, ht⟩, ⟨phi, hphi⟩)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_observation_gaussian_space
