import HRS.MS.PROS13FamilyMoment
import HRS.MS.S21T4ProdAJ
import HRS.MS.S21T4ProdBY
import HRS.MS.S21T4ProdJ

/-!
# Uniform product-law L² error for arbitrary symmetric pair kernels

The bound compares the actual finite-particle energies of two arbitrary
symmetric product-L² kernels under every Borel probability reference law.
It is not restricted to bounded kernels or nonatomic laws. The comparison
is an almost-everywhere identity of the original energies, not a substitution
by an artificially measurable random variable.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_particle_pair_L2_bound
    {N n : ℕ} (hN : 2 ≤ N)
    (h h' : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hm' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x)
    (hs' : ∀ x y, h' x y = h' y x) :
    (∫⁻ X : EucConfig d N,
      ‖(((0 : Fin n → ℝ),
        (N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
          (1 / 2 : ℝ) * ∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ))‖ₑ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ)) ≤
      ENNReal.ofReal (18 * ∫ z : Euc d × Euc d,
        (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let Δ : Euc d → Euc d → ℝ := fun x y => h x y - h' x y
  let u : EucConfig d N → ℝ := fun X =>
    (N : ℝ) * pairEnergy Δ X μ +
      (1 / 2 : ℝ) * ∫ x, ∫ y, Δ x y ∂μ ∂μ
  let v : EucConfig d N → ℝ := fun X =>
    (N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
      (1 / 2 : ℝ) * ∫ x, ∫ y, Δ x y ∂μ ∂μ
  have hΔm : MemLp (fun z : Euc d × Euc d => Δ z.1 z.2) 2 (μ.prod μ) :=
    hm.sub hm'
  have hΔs : ∀ x y, Δ x y = Δ y x := by
    intro x y
    simp only [Δ, hs x y, hs' x y]
  have hu : MemLp u 2 ν :=
    s21t4_generic_particle_centered_memLp hN Δ hΔm hΔs
  have he : u =ᵐ[ν] v := by
    filter_upwards [s21t4_pairEnergy_sub_ae μ h h' hm hm'] with X hX
    simp only [u, v, Δ, hX]
  have hv : MemLp v 2 ν := (memLp_congr_ae he).1 hu
  have hvar := s21l_s13_variance μ hN Δ hΔm hΔs
  have hsq : (∫ X, (v X) ^ 2 ∂ν) ≤
      18 * ∫ z : Euc d × Euc d,
        (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    have heq : (∫ X, (v X) ^ 2 ∂ν) = (∫ X, (u X) ^ 2 ∂ν) := by
      apply integral_congr_ae
      filter_upwards [he] with X hX
      rw [hX]
    simpa only [heq, u, Δ, ν] using hvar
  change (∫⁻ X : EucConfig d N,
    ‖(((0 : Fin n → ℝ), v X))‖ₑ ^ 2 ∂ν) ≤ _
  rw [s21t4_pair_second_lintegral v hv]
  exact ENNReal.ofReal_le_ofReal hsq

end HRS.MS.R26T3
