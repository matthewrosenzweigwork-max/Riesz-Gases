import HRS.MC.S7S7eAux1
import HRS.MC.Sec7Vocab
import HRS.PDE.EnergyR2Fn

/-!
# Packet `s7_S7e_pairing_identification`, helper 2: identification of `responseRep` with the mode data
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7e

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7e_kop_const_mul (g : Torus d → ℝ) (μ : Measure (Torus d)) (c : ℝ) (f : Torus d → ℝ)
    (x : Torus d) : Kop g μ (fun y => c * f y) x = c * Kop g μ f x := by
  rw [HRS.Q66.q66_kop_eq, HRS.Q66.q66_kop_eq]
  have e1 : ∀ z, ∫ y, g (z - y) * (c * f y) ∂μ = c * ∫ y, g (z - y) * f y ∂μ := fun z => by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  simp_rw [e1]
  unfold pair
  rw [integral_const_mul]
  ring

theorem s7e_kop_congr_ae (g : Torus d → ℝ) (μ : Measure (Torus d)) {f f' : Torus d → ℝ}
    (h : f =ᵐ[μ] f') (x : Torus d) : Kop g μ f x = Kop g μ f' x := by
  rw [HRS.Q66.q66_kop_eq, HRS.Q66.q66_kop_eq]
  have e1 : ∀ z, ∫ y, g (z - y) * f y ∂μ = ∫ y, g (z - y) * f' y ∂μ := fun z =>
    integral_congr_ae (by filter_upwards [h] with y hy; rw [hy])
  simp_rw [e1]

theorem s7e_responseRep_eq_of_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ}
    (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ h : Torus d → ℝ}
    (hψ : MemLp ψ 2 (withDensityReal ρ)) (hh : Continuous h) (hmean : pair (withDensityReal ρ) h = 0)
    (heq : ∀ x, h x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) h x =
      projMean (withDensityReal ρ) ψ x) (x : Torus d) :
    responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x = h x := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨Λ, hΛ'⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
  have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ h :=
    ⟨hh.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), hmean,
      Eventually.of_forall fun x => heq x⟩
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ h := ⟨h, hresp⟩
  obtain ⟨h₀, -, huniq⟩ := exists_unique_response hd hs0 hsd ρ hρ.density Λ
    (fun x => (le_abs_self _).trans (hΛ' x)) γ hγ ψ hψ
  have hchoose := hex.choose_spec
  have hri : responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ = hex.choose := by
    unfold responseInverse
    rw [dif_pos hex]
  have hae : responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ =ᵐ[withDensityReal ρ] h := by
    rw [hri]
    exact (huniq _ hchoose).trans (huniq h hresp).symm
  unfold responseRep
  rw [s7e_kop_congr_ae _ _ hae x]
  have := heq x
  linarith

end HRS.MC.Sec7.S7e

end
