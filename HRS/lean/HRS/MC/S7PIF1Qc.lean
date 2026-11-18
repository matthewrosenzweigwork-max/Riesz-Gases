import HRS.MC.S7PIF1Qb

/-!
# Packet piF1 (F2), part c: `flucInteraction = - F^{h_ψ}`

For gradient dynamics `D.M = -1` and any configuration `X` (`N ≥ 1`), `μ = ρ dx` with bounded density and `ψ` smooth:
`flucInteraction D ψ X ρ = - modulatedEnergy (hTransport d D.s ψ) X μ`.  The four pairings of `flucInteraction`
are `-1/2` times the four integrals of `h_ψ` against `μ_N`, `μ`; the diagonal terms vanish since `h_ψ(x,x) = 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS

variable {d N : ℕ}

/-- `interactionPairing` for gradient dynamics is `-1/2` times the integral of the transport kernel. -/
theorem S7PIF1_ip_eq (D : DynData d) (hM : D.M = -1) (ψ : Torus d → ℝ) (ν ν' : Measure (Torus d)) :
    interactionPairing D ψ ν ν' = -(1 / 2) * ∫ x, ∫ y, hTransport d D.s ψ x y ∂ν' ∂ν := by
  unfold interactionPairing
  have hpt : ∀ x y : Torus d, (if x = y then (0 : ℝ) else
      inner ℝ (Torus.grad ψ x - Torus.grad ψ y) (Torus.matVec D.M (periodicRieszGrad d D.s (x - y))))
      = -hTransport d D.s ψ x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp [hTransport]
    · rw [if_neg hxy, hM]
      unfold hTransport Torus.matVec
      simp
  simp_rw [hpt, integral_neg]
  ring

/-- The sum over `j ≠ i` can be replaced by the full sum since `h(x,x) = 0`. -/
theorem S7PIF1_erase_sum {h : Torus d → Torus d → ℝ} (hself : ∀ x, h x x = 0) (X : Config d N) (i : Fin N) :
    ∑ j ∈ Finset.univ.erase i, h (X i) (X j) = ∑ j, h (X i) (X j) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  simp [hself]

/-- Abstract form of the identity: a symmetric pair kernel `h` vanishing on the diagonal and dominated by
`A ‖G(x - y)‖` which represents `interactionPairing`. -/
theorem S7PIF1_fluc_eq_abs (D : DynData d) {ψ : Torus d → ℝ} {G : Torus d → Euc d}
    {h : Torus d → Torus d → ℝ}
    (hip : ∀ ν ν' : Measure (Torus d), interactionPairing D ψ ν ν' = -(1 / 2) * ∫ x, ∫ y, h x y ∂ν' ∂ν)
    (hself : ∀ x, h x x = 0) (hsymm : ∀ x y, h x y = h y x)
    {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B) (hG : Integrable G) {A : ℝ} (hA : 0 ≤ A)
    (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2))
    (hb : ∀ x y, |h x y| ≤ A * ‖G (x - y)‖)
    (hN : 0 < N) (X : Config d N) :
    flucInteraction D ψ X ρ = -modulatedEnergy h X (withDensityReal ρ) := by
  obtain ⟨hf1, hf2, -⟩ := S7PIF1_fibre hB hB0 hG hA hm hb
  have e1 : ∀ x, ∫ y, h x y ∂(empirical X) = (N : ℝ)⁻¹ * ∑ j, h x (X j) := fun x =>
    pair_empirical hN X (fun y => h x y)
  have hQ11 : ∫ x, ∫ y, h x y ∂(empirical X) ∂(empirical X)
      = (N : ℝ)⁻¹ * ∑ i, ((N : ℝ)⁻¹ * ∑ j, h (X i) (X j)) := by
    simp_rw [e1]
    exact pair_empirical hN X (fun x => (N : ℝ)⁻¹ * ∑ j, h x (X j))
  have hQ12 : ∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(empirical X)
      = (N : ℝ)⁻¹ * ∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ) :=
    pair_empirical hN X (fun x => ∫ y, h x y ∂(withDensityReal ρ))
  have hQ21 : ∫ x, ∫ y, h x y ∂(empirical X) ∂(withDensityReal ρ)
      = (N : ℝ)⁻¹ * ∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ) := by
    simp_rw [e1]
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hf2 (X j))]
    have : ∀ j, ∫ x, h x (X j) ∂(withDensityReal ρ) = ∫ y, h (X j) y ∂(withDensityReal ρ) := fun j =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => hsymm _ _)
    simp_rw [this]
  unfold flucInteraction modulatedEnergy
  simp only [hip]
  rw [hQ11, hQ12, hQ21]
  simp only [S7PIF1_erase_sum hself]
  rw [← Finset.mul_sum]
  ring

theorem S7PIF1_fluc_eq (D : DynData d) (hM : D.M = -1) (hsd : D.s < d) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B)
    (hG : Integrable (periodicRieszGrad d D.s)) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ x y, |hTransport d D.s ψ x y| ≤ A * ‖periodicRieszGrad d D.s (x - y)‖)
    (hN : 0 < N) (X : Config d N) :
    flucInteraction D ψ X ρ = -modulatedEnergy (hTransport d D.s ψ) X (withDensityReal ρ) :=
  S7PIF1_fluc_eq_abs D (S7PIF1_ip_eq D hM ψ) (fun x => HRS.LocalDivAux.hTransport_self x ψ)
    (fun x y => HRS.LocalDivAux.hTransport_symm hsd hψ x y) hB hB0 hG hA
    (HRS.LocalDivAux.measurable_hTransport hsd hψ) hb hN X

end HRS.MC.Sec7.S7PIF1

end
