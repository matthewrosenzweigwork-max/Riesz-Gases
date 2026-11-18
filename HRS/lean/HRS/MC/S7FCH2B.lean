import HRS.MC.S7FCH2A
import HRS.MC.S7FCG

/-!
# H2, part B: row bounds and linearity of the modulated energy for the kernels of `FCKernelData`

* `S7FCH2_isProb`: `μ_t = ρ^t dx` is a probability measure (`t ≥ 0`);
* `S7FCH2_rowOK_hT`, `S7FCH2_rowOK_fr`: the pair kernels `h_{∇e_k}` (transport) and the smooth finite-rank `K k L` have
  bounded integrable rows against `μ_t`;
* `S7FCH2_me_sub`: `F^{K-h} = F^{K} - F^{h}` (linearity of `modulatedEnergy` on `RowOK` kernels).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

theorem S7FCH2_isProb (R : Regime d) {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (withDensityReal (R.ρ t)) :=
  isProb_withDensityReal ((alltime_traj R t).mf.density t ⟨ht, le_rfl⟩)

/-- Row bounds from a domination `|k x y| ≤ W (x - y)` with `W` integrable. -/
theorem S7FCH2_rowOK_dom (R : Regime d) {t : ℝ} (ht : 0 ≤ t) {W : Torus d → ℝ} (hW : Integrable W)
    {k : Torus d → Torus d → ℝ} (hk : Measurable (Function.uncurry k)) (hdom : ∀ x y, |k x y| ≤ W (x - y)) :
    RowOK (withDensityReal (R.ρ t)) k := by
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  have hM : 0 ≤ M₀ := le_trans hm₀.le ((hbd t ht 0).1.trans (hbd t ht 0).2)
  exact (rowOK_of_dom hM (fun x => (hbd t ht x).2) hW hk hdom).1

/-- The transport kernel `h_{∇e_k}` has bounded integrable rows against `μ_t`. -/
theorem S7FCH2_rowOK_hT (R : Regime d) {t : ℝ} (ht : 0 ≤ t) {c : ℝ} (hc : EnvelopeConst (d := d) R.D.s c)
    (k : NonzeroLattice d) :
    RowOK (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode k)) := by
  have hφ := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨Bh, hBh0, hBh⟩ := HRS.MC.Sec7.FCG.fcg_hT_env R.hd R.D.hs0 R.hs hc hφ
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hgi : Integrable (periodicRiesz d R.D.s) :=
    HRS.CoercAux.integrable_periodicRiesz_one hd1 R.D.hs0 R.D.hsd
  refine S7FCH2_rowOK_dom R ht (W := fun z => Bh * (|periodicRiesz d R.D.s z| + |c|)) ?_
    (HRS.MC.Sec7.FCG.fcg_hT_meas_symm R.D.hsd hφ).1 ?_
  · exact (hgi.abs.add (integrable_const _)).const_mul Bh
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      have h0 : hTransport d R.D.s (Torus.realMode k) x x = 0 := by unfold hTransport; simp
      rw [h0, abs_zero]
      exact mul_nonneg hBh0 (add_nonneg (abs_nonneg _) (abs_nonneg _))
    · calc |hTransport d R.D.s (Torus.realMode k) x y|
          ≤ Bh * (periodicRiesz d R.D.s (x - y) + c) := hBh x y hxy
        _ ≤ Bh * (|periodicRiesz d R.D.s (x - y)| + |c|) := by
          exact mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) (le_abs_self _)) hBh0

theorem S7FCH2_fr_cont (K : FRKernel d) : Continuous (fun p : Torus d × Torus d => K.toFun p.1 p.2) := by
  have hfc : ∀ i, Continuous (K.f i) := fun i => HRS.MC.Sec7.S7FCW12.s7fcw12_continuous_of_smooth (K.smooth i)
  unfold FRKernel.toFun
  fun_prop

/-- A smooth finite-rank kernel has bounded integrable rows against `μ_t`. -/
theorem S7FCH2_rowOK_fr (R : Regime d) {t : ℝ} (ht : 0 ≤ t) (K : FRKernel d) :
    RowOK (withDensityReal (R.ρ t)) K.toFun := by
  have hcont := S7FCH2_fr_cont K
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn hcont.continuousOn
  exact S7FCH2_rowOK_dom R ht (W := fun _ => M) (integrable_const M) hcont.measurable
    (fun x y => by simpa using hM (x, y) (Set.mem_univ _))

/-- Linearity: `F^{K - h_{∇e_k}} = F^K - F^{h_{∇e_k}}` at the time `t ≥ 0`. -/
theorem S7FCH2_me_sub (R : Regime d) {t : ℝ} (ht : 0 ≤ t) {c : ℝ} (hc : EnvelopeConst (d := d) R.D.s c)
    (k : NonzeroLattice d) (K : FRKernel d) {N : ℕ} (x : Config d N) :
    modulatedEnergy (fun a b => K.toFun a b - hTransport d R.D.s (Torus.realMode k) a b) x
        (withDensityReal (R.ρ t)) =
      modulatedEnergy K.toFun x (withDensityReal (R.ρ t)) -
        modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) x (withDensityReal (R.ρ t)) := by
  have := S7FCH2_isProb R ht
  exact modulatedEnergy_sub (S7FCH2_rowOK_fr R ht K) (S7FCH2_rowOK_hT R ht hc k) x

end HRS.MC.Sec7.S7FCH2

end
