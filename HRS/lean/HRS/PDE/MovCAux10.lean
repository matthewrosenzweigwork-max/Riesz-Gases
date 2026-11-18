import HRS.PDE.MovCAux9
import HRS.Appendix.B15EAux1

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_regSeq_exists {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (M : ℕ → ℝ) (Y₀ : Ω → Fin N → Euc d)
      (Y : ℕ → ℝ → Ω → (Fin N → Euc d)), MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y := by
  obtain ⟨ℱ, W', hF⟩ := h.filtered
  have hV : Torus.IsCk 2 D.V := h.traj.V_reg
  have hW'' : IsBrownianFiltration P (b15e_shiftFil ℱ) W' := b15e_shiftFil_brownian hF.brownian
  have hY₀ : ∀ t : ℝ, Measurable[b15e_shiftFil ℱ t] (b15e_initLift X) :=
    b15e_initLift_measurable (hF.adapted 0)
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (b15e_initLift X ω i)) = X₀ ω := by
    filter_upwards [h.sol.init] with ω h0
    rw [b15e_mk_initLift, h0]
  set M : ℕ → ℝ := fun n => (n : ℝ) with hMdef
  have hMt : Tendsto M atTop atTop := tendsto_natCast_atTop_atTop
  choose Y hY using fun n => b15e_exists_regularised hW'' D hV (M n) (b15e_initLift X) hY₀
  have hev := b15c_regularised_eq_strong_proof D hV h.brownian h.sol hF.coords hY₀ae hMt hY
  exact ⟨b15e_shiftFil ℱ, W', M, b15e_initLift X, Y,
    { levels := hMt
      levels_nonneg := fun n => Nat.cast_nonneg n
      brownian := hW''
      coords := hF.coords
      init_adapted := hY₀
      init_lift := hY₀ae
      sol := hY
      eventually_eq := hev }⟩

end HRS
