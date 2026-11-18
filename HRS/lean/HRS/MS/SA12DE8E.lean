import HRS.MS.SA12DE8D
import HRS.MS.SA12X3Final

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part E: helper lemmas for the tie

`sa12de8_sobolev_ae`: `H^m` membership and norm depend only on the a.e. class.  `sa12de8_locInt_of_ball`: local integrability from
`L²` on every ball.  `sa12de8_limit_bound`: the per-time bound `‖u‖_{H^m} ≤ e^{Λτ}‖φ‖_{H^m}` for a distributional limit `u` of smooth
periodic `F k` with `boxEnergy (F k) ≤ e^{2Λτ} boxEnergy (D k)` and `boxEnergy (D k) ≤ (‖φ‖ + δ)²` eventually, for all `δ > 0`
(no prefactor loss: `δ' = δ e^{-Λτ}`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12C HRS.MS.SA12DE7

variable {d : ℕ}

theorem sa12de8_sobolev_ae {u v : Euc d → ℝ} (h : u =ᵐ[volume] v) (r : ℝ) :
    (HRS.PDE.ToolboxRd.MemSobolev r u ↔ HRS.PDE.ToolboxRd.MemSobolev r v) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq r u = HRS.PDE.ToolboxRd.sobolevNormSq r v := by
  have hf := HRS.PDE.ToolboxRd.FourierAux.fourierL2_congr_ae h
  refine ⟨?_, ?_⟩
  · unfold HRS.PDE.ToolboxRd.MemSobolev
    rw [hf]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.ae_eq h, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.ae_eq h.symm, h2⟩
  · unfold HRS.PDE.ToolboxRd.sobolevNormSq
    rw [hf]

theorem sa12de8_locInt_of_ball {g : Euc d → ℝ}
    (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (Metric.ball (0 : Euc d) R))) :
    LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Euc d)
  have hR1 : K ⊆ Metric.ball (0 : Euc d) (max R 1) :=
    hR.trans (Metric.ball_subset_ball (le_max_left _ _))
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Euc d) (max R 1))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hint : Integrable g (volume.restrict (Metric.ball (0 : Euc d) (max R 1))) :=
    (hg (max R 1) (lt_of_lt_of_le one_pos (le_max_right _ _))).integrable one_le_two
  exact hint.mono_measure (Measure.restrict_mono hR1 le_rfl)

theorem sa12de8_limit_bound {m : ℕ} (F D : ℕ → Euc d → ℝ) (L : ℕ → ℝ) (u : Euc d → ℝ) {lam τ n0 : ℝ}
    (hn0 : 0 ≤ n0) (hL : ∀ n, 0 < L n) (hLt : Tendsto L atTop atTop)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hper : ∀ n (x : Euc d) (k : Fin d → ℤ), F n (x + L n • latticePt k) = F n x)
    (hbound : ∀ n, boxEnergy m (L n) (F n) ≤ Real.exp (2 * lam * τ) * boxEnergy m (L n) (D n))
    (hdat : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, boxEnergy m (L n) (D n) ≤ (n0 + δ) ^ 2)
    (hu : LocallyIntegrable u volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧
      sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal (Real.exp (lam * τ) * n0) := by
  set E : ℝ := Real.exp (lam * τ) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (2 * lam * τ) = E ^ 2 := by
    rw [hE, show 2 * lam * τ = lam * τ + lam * τ by ring, Real.exp_add]; ring
  refine sa12de8_Hm_of_box_energy_lim F L u (mul_nonneg hEpos.le hn0) hL hLt hF hper ?_ hu hconv
  intro δ hδ
  have hδ' : 0 < δ / E := div_pos hδ hEpos
  filter_upwards [hdat (δ / E) hδ'] with n hn
  calc boxEnergy m (L n) (F n) ≤ Real.exp (2 * lam * τ) * boxEnergy m (L n) (D n) := hbound n
    _ ≤ E ^ 2 * (n0 + δ / E) ^ 2 := by
        rw [hE2]
        exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ = (E * n0 + δ) ^ 2 := by
        have : E * (δ / E) = δ := mul_div_cancel₀ δ hEpos.ne'
        calc E ^ 2 * (n0 + δ / E) ^ 2 = (E * (n0 + δ / E)) ^ 2 := by ring
          _ = (E * n0 + δ) ^ 2 := by rw [mul_add, this]

end HRS.MS.SA12DE8
