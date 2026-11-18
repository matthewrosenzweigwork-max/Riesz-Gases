import HRS.MS.R26T8AG00c
import HRS.MS.S82WA04

/-!
# S8.2 observed-time layer, packet T8A.G00 (helper d): pointwise bound of the Gibbs density times the envelope squared

Off the collision set, `exp(-β H_N(X)) · env_M(X)²` is bounded by `K0 · ∏_i (1+‖X_i‖)^k exp(-(βa/2)‖X_i‖²)`,
where the pair factors `(1+‖x_i-x_j‖^(-M))² exp(-(β/2N)‖x_i-x_j‖^(-s))` are bounded by `K` (helper b) and the
confinement is Gaussian.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g00d_exp_split {d N : ℕ} (hN : 2 ≤ N) {s a beta : ℝ} (hs : 0 < s) (X : EucConfig d N) :
    Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (HRS.Whole.confinement a) X) =
      (∏ i, Real.exp (-beta * (a * ‖X i‖ ^ 2 / 2))) *
        ∏ i, ∏ j ∈ Finset.univ.erase i, Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hker : ∀ x y : Euc d, rieszKernel d s (x - y) = ‖x - y‖ ^ (-s) := by
    intro x y
    unfold rieszKernel
    rw [if_neg hs0]
  have hsym : ∀ x y : Euc d, ‖x - y‖ ^ (-s) = ‖y - x‖ ^ (-s) := fun x y => by rw [norm_sub_rev]
  have hid := r26t8a_g00c_sum_erase (fun x y : Euc d => ‖x - y‖ ^ (-s)) hsym X
  have hNpos : (N : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold HRS.Whole.canonicalHamiltonian
  simp only [hker]
  have hexp : -beta * (∑ i, HRS.Whole.confinement a (X i) + (1 / (N : ℝ)) *
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖X i - X j‖ ^ (-s)) =
      ∑ i, (-beta * (a * ‖X i‖ ^ 2 / 2)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) := by
    have hV' : ∑ i, (-beta * (a * ‖X i‖ ^ 2 / 2)) = -beta * ∑ i, HRS.Whole.confinement a (X i) := by
      simp only [HRS.Whole.confinement, Finset.mul_sum]
    have hT' : ∑ i, ∑ j ∈ Finset.univ.erase i, (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) =
        -(beta / (2 * N)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖X i - X j‖ ^ (-s) := by
      simp only [Finset.mul_sum]
    rw [hV', hT', hid]
    field_simp
    ring
  rw [hexp, Real.exp_add, Real.exp_sum]
  congr 1
  simp only [Real.exp_sum]

end HRS.MS.R26T8A

end
