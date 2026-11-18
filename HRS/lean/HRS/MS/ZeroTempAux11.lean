import HRS.MS.ZeroTempAux10
import HRS.MP.RdRemainder
import HRS.MS.GenPathAux12
import HRS.MH.DualityRdFinal

/-!
# SA11, packet C2b: the particle field on the weak jet of a continuous function; time-integrated energy

* `sa11_Xi_eq`, `sa11_Xi_weak`: `Ξ(G) = σ(N⁻¹ ∑ u(x_i) - ∫ u ρ)` when `G` is a weak jet of the continuous function `u`.
* `sa11_path_bound`: the pathwise bound of `∫_0^t Comm_N dr` by the time integral of the corrected energy.
* `sa11_time_moment`: `E ∫_0^T (F + oNΛ + c e) dr ≤ T (𝔈 + c e)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

section XiWeak

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

theorem sa11_Xi_eq {N : ℕ} (σ : ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)] :
    sa11_Xi (m := m) (p := p) σ X ρ hρ =
      σ • ((N : ℝ)⁻¹ • ∑ i, sa11_ev (m := m) (p := p) (X i) -
        sa11_evMeas (m := m) (p := p) (HRS.Whole.withDensityReal ρ)) := by
  refine sa11_clm_ext fun φ => ?_
  rw [sa11_Xi_apply hd hm]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    sa11_ev_apply hd hm, sa11_evMeas_apply hd hm, smul_eq_mul]
  rfl

theorem sa11_Xi_weak {N : ℕ} (hN : 0 < N) (σ : ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) (G : WmpSpace d m p) {u : Euc d → ℝ} (hu : Continuous u)
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) :
    sa11_Xi (m := m) (p := p) σ X ρ hρ G =
      σ * ((N : ℝ)⁻¹ * ∑ i, u (X i) - ∫ x, u x ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := sa11_isProb hρ
  have e := sa11_Xi_eq hd hm σ X ρ hρ
  rw [e]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    sa11_ev_weak hd hm G hu hG, sa11_evMeas_weak hd hm _ G hu hG, smul_eq_mul]

end XiWeak

/-! ### The pathwise bound of the time integral of a commutator -/

theorem sa11_path_bound {Kb t T : ℝ} (hKb : 0 ≤ Kb) (ht : t ∈ Set.Icc (0 : ℝ) T) (f E : ℝ → ℝ)
    (hbound : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), |f r| ≤ Kb * E r) :
    ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, f r| ≤
      ENNReal.ofReal Kb * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (E r) := by
  calc ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, f r| = ‖∫ r in Set.Icc (0 : ℝ) t, f r‖ₑ :=
        (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ‖f r‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal Kb * ENNReal.ofReal (E r) := by
        refine lintegral_mono_ae (hbound.mono fun r hr => ?_)
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hKb]
        exact ENNReal.ofReal_le_ofReal hr
    _ = ENNReal.ofReal Kb * ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (E r) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Kb * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (E r) := by
        gcongr
        exact ht.2

end HRS.MS.ZeroTemp
