import HRS.MH.WpP5a
import HRS.MH.WpP5b
import HRS.Uniform.Comparison

/-!
# Packet P6: `HRS.Uniform.general_fluctuation_Wp`

Assembly of the two bounds `gff_core_Wp_trace` (P5a) and `gff_core_Wp_transport` (P5b).  If the energy term `En` is infinite, both right
sides are infinite, because `σ = sigmaScale > 0` (`gfwp_sigN_pos`) and the constant is positive; otherwise each bound is one of P5a, P5b,
with the constant enlarged to the maximum of the two.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform

theorem general_fluctuation_Wp_proof : type_of% @HRS.Uniform.general_fluctuation_Wp := by
  intro d b p hp
  obtain ⟨C₀a, hA⟩ := gff_core_Wp_trace_proof b p hp
  obtain ⟨C₀b, hB⟩ := gff_core_Wp_transport_proof b p hp
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  obtain ⟨Ca, hCa, hA'⟩ := hA C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨Cb, hCb, hB'⟩ := hB C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨max Ca Cb, lt_max_of_lt_left hCa, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF η₀ hη hind Y hY
  have hσ : 0 < sigmaScale N (S.κ N) (S.invβ N) := gfwp_sigN_pos_proof S N (by omega)
  have hC : (0 : ℝ) < max Ca Cb := lt_max_of_lt_left hCa
  have h1 := hA' S hS hMF hPos N hN P X₀ W hW X hX hF η₀ hη hind Y hY
  have h2 := hB' S hS hMF hPos N hN P X₀ W hW X hX hF η₀ hη hind Y hY
  intro σ A q Ξ YN ε En Cv Wt
  by_cases hEn : En = ⊤
  · have hσ' : ENNReal.ofReal σ ≠ 0 := (ENNReal.ofReal_pos.2 hσ).ne'
    have hC' : ENNReal.ofReal (max Ca Cb) ≠ 0 := (ENNReal.ofReal_pos.2 hC).ne'
    have hsum1 : ENNReal.ofReal A * ε + ENNReal.ofReal σ * En + Cv = ⊤ := by
      rw [hEn, ENNReal.mul_top hσ']; simp
    have hsum2 : ENNReal.ofReal A * ε + ENNReal.ofReal σ * En +
        ENNReal.ofReal (Real.sqrt q) * Wt = ⊤ := by
      rw [hEn, ENNReal.mul_top hσ']; simp
    rw [hsum1, hsum2, ENNReal.mul_top hC']
    exact ⟨le_top, le_top⟩
  · have e1 := h1 hEn
    have e2 := h2 hEn
    refine ⟨e1.trans ?_, e2.trans ?_⟩
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl

end HRS.MH.WpP
