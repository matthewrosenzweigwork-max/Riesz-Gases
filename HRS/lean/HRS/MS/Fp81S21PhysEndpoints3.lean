import HRS.MS.Fp81S21PhysEndpoints2
import HRS.MS.Fp81S21InitRecon

/-! Transfer of the genuine initial window through the preparation law. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21

/-- Every continuous observable of the transported initial window transfers
from the particle's actual initial configuration to its preparation law. -/
theorem fp81s21_physical_initial_window_integral (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ g : Window p → ℝ, Continuous g →
        (∫ ω, g (initialWindow R N a (A.X₀ ω)) ∂A.P) =
          ∫ X, g (initialWindow R N a X) ∂(r26t3_Q R N) := by
  obtain ⟨δpath, hδpath, hδpathhalf, hpath⟩ := fp81s21_initRecon_path p
  obtain ⟨δcos, hδcos, hδcoshalf, hcos⟩ := fp81s21_cosRecon_radius p
  let δ0 := min δpath δcos
  have hδ0 : 0 < δ0 := lt_min hδpath hδcos
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδpathhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R a ha N hN A g hg
  have hδpath' : δ ≤ δpath := hδle.trans (min_le_left _ _)
  have hδcos' : δ ≤ δcos := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  have hγ : 0 < p.γ ∨ p.γ = 0 := (lt_or_eq_of_le p.hγ).imp id Eq.symm
  obtain ⟨Cobs, hCobs, hcosR⟩ := hcos δ hδ hδcos' R
  obtain ⟨hq, _hbound, _hobs, _hshift⟩ := hcosR a ha
  have hN1 : 1 ≤ N := by omega
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rcases hγ with hpos | hzero
    · exact (r26t3_static_pressure hδ hδhalf R hpos).1 N hN
    · have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
      letI : IsProbabilityMeasure (r26t3_mu R 0) :=
        s11iid_prob hdens.1.nonneg hdens.1.integral_one
      rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      infer_instance
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  haveI : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  have hWmeas : Measurable
      (r26t3_W R (r26t3_qwin R a) N : EucConfig p.d N → SeqL2) := by
    unfold r26t3_W
    exact S45.s45_feature_measurable hN1 hq
  have hSynthMeas : Measurable (fun X : EucConfig p.d N =>
      s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N X)) :=
    (s21gPhi (r26t3_feature_enum p.d) p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ)).continuous.measurable.comp hWmeas
  have hInitMeas : Measurable (initialWindow R N a) := by
    have heq : initialWindow R N a = fun X =>
        s21gPhi (r26t3_feature_enum p.d) p.hT
          ((wholeSpaceIndex p.d : ℕ) : ℝ)
          (r26t3_W R (r26t3_qwin R a) N X) := by
      funext X
      exact (hpath δ hδ hδpath' R hγ N hN a ha X).symm
    rw [heq]
    exact hSynthMeas
  have hX₀ : AEMeasurable A.X₀ A.P :=
    ((A.strong 0).adapted 0).aemeasurable.congr (A.strong 0).init
  have hobs : AEStronglyMeasurable (fun X => g (initialWindow R N a X))
      (r26t3_Q R N) := (hg.measurable.comp hInitMeas).aestronglyMeasurable
  have hlaw : A.P.map A.X₀ = r26t3_Q R N := A.initial
  have hobsMap : AEStronglyMeasurable (fun X => g (initialWindow R N a X))
      (A.P.map A.X₀) := by rw [hlaw]; exact hobs
  have hmap := integral_map hX₀ hobsMap
  simpa only [Function.comp_def, hlaw] using hmap.symm

#print axioms HRS.Fp81.S21.fp81s21_physical_initial_window_integral
end HRS.Fp81.S21
end
