import HRS.MC.S7PIF10A
import HRS.MC.S7PIF5
import HRS.MC.S7PIF1Brk
import HRS.MC.S7PIM1
import HRS.MC.S7PIM2
import HRS.MC.S7PIM3
import HRS.MC.S7PIDSAsm

/-!
# Packet piF10, part B: pathwise facts for the Riemann-Stieltjes clauses of `s7_PIF_cyl_concl_proof`

* `S7PIF10_eta_pair_int`: a.s. the pairing `r ↦ η_N^r(∇obsTest_i·∇obsTest_j)` is integrable on `[0,T]` (bracket identity `F3` and the
  local square integrability of the diffusion integrand `Φc` of `F5`);
* `S7PIF10_hJ`: a.s. the `𝒥`-tensors of `η_N(ω)` exist on every interval (PI-D with the bounded `E_r` representative of `M2`);
* `S7PIF10_cylA_int`, `S7PIF10_cylJ_int`: a.s. the densities `cylA`, `cylJ` are integrable on `(0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3 HRS.MC.Sec7.S7PIF5

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- a.s. the pairings of `η_N` with the products of the gradients of the test functions are integrable on `[0,T]` -/
theorem S7PIF10_eta_pair_int {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ᵐ ω ∂P, ∀ i j, IntegrableOn (fun r => NegSobolev.eval (etaE m (X r.toNNReal ω) (withDensityReal (R.ρ r)))
        (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))
      (Set.Icc 0 T) := by
  have hΦ := S7PIF5_Phi_L2E R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  have hβ : 0 < R.D.invβ := S7PIS3_invβ_pos R
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  filter_upwards [hΦ.sq T] with ω hω i j
  have hcross := S7PIF10_cross_integrable (T := T) (fun s => S7PIF5_Phi R X t φ s ω)
    (S7PIF5_sec_aemeas hΦ.prog ω T) hω i j
  have hh := S7PIS3_h_intOn R t φ ht hφ i j
  have hRHS : IntegrableOn (fun s => (Real.sqrt N / (2 * R.D.invβ)) *
      ((∑ k, S7PIF5_Phi R X t φ s ω k i * S7PIF5_Phi R X t φ s ω k j) -
        2 * R.D.invβ * S7PIS3_h R t φ i j s)) (Set.Icc 0 T) :=
    (hcross.sub (hh.const_mul _)).const_mul _
  refine hRHS.congr_fun (fun s hs => ?_) measurableSet_Icc
  have hbr := HRS.MC.Sec7.S7PIF1.s7_PIF_bracket_proof R m hm T N hN X ω t φ ht hφ i j s hs
  have hor := S7PIS3_obsRate_eq R t φ i j hs.1
  have e1 : (∑ k, S7PIF5_Phi R X t φ s ω k i * S7PIF5_Phi R X t φ s ω k j) =
      obsRate R.D R.ρ t φ s i j + (Real.sqrt N)⁻¹ * (2 * R.D.invβ *
        NegSobolev.eval (etaE m (X s.toNNReal ω) (withDensityReal (R.ρ s)))
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i s) y) (Torus.grad (obsTest R.D R.ρ t φ j s) y))) := hbr
  beta_reduce
  rw [e1, hor]
  field_simp
  ring

/-- a.s. the `𝒥`-tensors of `η_N(ω)` exist on every interval of `[0,T]` -/
theorem S7PIF10_hJ :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      ∃ J, IsJValue R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b) J := by
  obtain ⟨M, hM⟩ := HRS.MC.Sec7.S7PIM.s7_PIM_eta_bdd_proof R m hm T hT N hN P X₀ W X hreal
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIDS.s7_PI_D_J_exists_assembly_proof R (2 * (d : ℝ) + 6) rfl m hm T hT
  filter_upwards [hM] with ω hω a b ha hab hbT
  obtain ⟨zr, hzm, hzb, hze⟩ := hω
  obtain ⟨J, hJ, -⟩ := hC zr hzm M hzb a b ha hab hbT
  refine ⟨J, S7PIF10_isJValue_congr R.D R.ρ m T measurableSet_Ioc (fun u hu => ?_) hJ⟩
  exact hze u hu.2

end Prob

end HRS.MC.Sec7.S7PIF10

end
