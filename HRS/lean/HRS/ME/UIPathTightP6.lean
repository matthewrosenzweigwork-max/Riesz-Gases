import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue
import HRS.ME.UIPathTightP3b
import HRS.ME.UIPathTightP5
import HRS.MD.EQLawFlow

/-! Packet UP6: `p6_assembly`. -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- arithmetic: `L * (ε / (2 L)) ≤ ε / 2` in `ℝ≥0∞` for `L > 0`. -/
theorem p_up6_mul_div (ε : ℝ≥0∞) {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal L * (ε / (2 * ENNReal.ofReal L)) ≤ ε / 2 := by
  have h0 : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
  have ht : ENNReal.ofReal L ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  calc ENNReal.ofReal L * (ε * (2⁻¹ * (ENNReal.ofReal L)⁻¹))
      = ε * 2⁻¹ * (ENNReal.ofReal L * (ENNReal.ofReal L)⁻¹) := by ring
    _ = ε * 2⁻¹ := by rw [ENNReal.mul_inv_cancel h0 ht, mul_one]
    _ ≤ ε * 2⁻¹ := le_rfl

theorem p6_assembly (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) :
    IsTightMeasureSet {μ : Measure (PathSpace d m T) | ∃ (n : ℕ) (u : ℝ), 0 ≤ u ∧
      μ = (S.P n).map (windowGibbs m T u
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n))} := by
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hev : ∀ᶠ L in atTop,
      uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ ε / 2 ∧ 1 ≤ L :=
    (ENNReal.tendsto_nhds_zero.1 hUI (ε / 2) (ENNReal.half_pos hε.ne')).and
      (eventually_ge_atTop 1)
  obtain ⟨L, hLt, hL1⟩ := hev.exists
  have hLpos : 0 < L := by linarith
  have hε' : 0 < ε / (2 * ENNReal.ofReal L) := by
    refine ENNReal.div_pos hε.ne' ?_
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  obtain ⟨K, hKc, hK⟩ := stationary_window_tight_uniform hd hs0 hsd hβ V hV ρβ hρβ m hm T hT _ hε'
  refine ⟨K, hKc, ?_⟩
  rintro μ ⟨n, u, hu, rfl⟩
  obtain ⟨Ω₂, _, P₂, _, X₀₂, W₂, X₂, h₂⟩ :=
    HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ (N := n + 2) (by omega) (u + T)
      (by linarith)
  have hP5 := ret_window_tail hd hs0 hsd hβ V hV hm2 T hT u hu (N := n + 2) (by omega)
    (S.P n) (S.X₀ n) (S.W n) (S.X n) (hS (u + T) (by linarith) n) (hSF n) (hν n)
    P₂ X₀₂ W₂ X₂ h₂ Kᶜ hKc.isClosed.isOpen_compl.measurableSet L hLpos.le
  have hP3 := hK n u hu P₂ X₀₂ W₂ X₂ h₂
  have htail : (law (S.P n) (S.X₀ n)) {x | ENNReal.ofReal L <
        (law (S.P n) (S.X₀ n)).rnDeriv (canonicalGibbs (periodicRiesz d s) V (n + 2) β) x} ≤
      uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L :=
    le_iSup (fun n => (S.P n).map (S.X₀ n) {X | ENNReal.ofReal L <
      ((S.P n).map (S.X₀ n)).rnDeriv (canonicalGibbs (periodicRiesz d s) V (n + 2) β) X}) n
  calc _ ≤ _ := hP5
    _ ≤ ε / 2 + ENNReal.ofReal L * (ε / (2 * ENNReal.ofReal L)) := by
        gcongr
        exact htail.trans hLt
    _ ≤ ε / 2 + ε / 2 := by gcongr; exact p_up6_mul_div ε hLpos
    _ = ε := ENNReal.add_halves ε

end HRS.ME.UIPathTight
