import HRS.Commutator.Torus.TSAMPAux32

/-!
# T-SAMP helpers, part 33: `usample_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform Convolution

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- Reproducing formula for band-limited continuous functions, everywhere. -/
lemma tsamp_repro_everywhere (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {f : Torus d → ℝ}
    (hfc : Continuous f)
    (hsupp : ∀ k : Lattice d, 2 < η * Lattice.enorm k → Torus.fcoef f k = 0) (x : Torus d) :
    f x = ∫ y, perio (Whole.psiL (d := d) (η / 2)⁻¹) (x - y) * f y := by
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd
  have hη' : 0 < η / 2 := by positivity
  obtain ⟨hKint, hKb, hK1, hKcoef, -⟩ := hker (η / 2) hη' (by linarith)
  set K : Torus d → ℝ := perio (Whole.psiL (d := d) (η / 2)⁻¹) with hK
  have hKc : Continuous K := tkr_perio_psi_continuous (inv_pos.2 hη')
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (textConv K f) := text_integrable_conv hKint hfi
  have hae : f =ᵐ[volume] textConv K f := by
    have := text_ae_eq_zero_of_fcoef (g := fun x => f x - textConv K f x) (hfi.sub hci) (fun k => by
      rw [text_fcoef_sub hfi hci, text_fcoef_conv hKint hfi, hKcoef k]
      by_cases h : 2 < η * Lattice.enorm k
      · rw [hsupp k h]; simp
      · have hc : Whole.chi ((η / 2) • Lattice.toEuc k) = 1 := by
          apply Whole.cmxFB_chi_one
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη']
          unfold Lattice.enorm at h
          push Not at h
          nlinarith
        rw [hc]; simp)
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx
  have hcont : Continuous (textConv K f) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
    have hbdd : BddAbove (Set.range fun x : Torus d => ‖K x‖) :=
      ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x (Set.mem_univ x)⟩
    have := BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ) hbdd
      hfi hKc (μ := (volume : Measure (Torus d)))
    have e : textConv K f = fun x => (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] K) x := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.mul_apply', textConv]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    rw [e]; exact this
  have heq := (Continuous.ae_eq_iff_eq (volume : Measure (Torus d)) hfc hcont).1 hae
  exact congrFun heq x

end HRS.Commutator.TorusNote
