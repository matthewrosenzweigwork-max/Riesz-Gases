import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.LOWVAux3
import HRS.Commutator.Whole.Local

/-!
# Packet CMX-HIGH auxiliary 1: the force `u = ∇g_{≤1} * ν`

For a finite signed measure `σ`, `u = σ.convForce (gloForce s)` is continuous and bounded, and its
components have Fourier support in `B̄(0,2)` (`gloForce` does, `lowv_gloForce_fsupp`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.UHIGH

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem uhigh_conv_cont {B : ℝ} {F : Euc d → Euc d} (hF : Continuous F) (hB : ∀ z, ‖F z‖ ≤ B)
    (m : Measure (Euc d)) [IsFiniteMeasure m] :
    Continuous (fun x => ∫ y, F (x - y) ∂m) := by
  refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_)
    (fun x => ae_of_all _ fun y => hB _) (integrable_const _) (ae_of_all _ fun y => ?_)
  · exact (hF.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact hF.comp (continuous_id.sub continuous_const)

theorem uhigh_gloForce_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ B : ℝ, ∀ z : Euc d, ‖gloForce s z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (gloForce_props hd hs0 hsd).2.2.2 0
  exact ⟨B, fun z => by simpa [norm_iteratedFDeriv_zero] using hB z⟩

theorem uhigh_u_cont (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (σ : SMeas d)
    [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg] :
    Continuous (fun x => σ.convForce (gloForce s) x) := by
  obtain ⟨B, hB⟩ := uhigh_gloForce_bound hd hs0 hsd
  have hc := (gloForce_props hd hs0 hsd).1.continuous
  unfold SMeas.convForce SMeas.intV
  exact (uhigh_conv_cont hc hB σ.pos).sub (uhigh_conv_cont hc hB σ.neg)

/-- Fourier support is preserved by convolution with a finite measure. -/
theorem uhigh_fs_conv {R B : ℝ} {G : Euc d → ℝ} (hG : FourierSuppIn R G) (hGc : Continuous G)
    (hB : ∀ x, |G x| ≤ B) (m : Measure (Euc d)) [IsFiniteMeasure m] :
    FourierSuppIn R (fun x => ∫ y, G (x - y) ∂m) := by
  intro θ hθ
  have hθi : Integrable (fun x => ‖θ x‖) volume := θ.integrable.norm
  have hint : Integrable (fun p : Euc d × Euc d => ((G (p.1 - p.2) : ℝ) : ℂ) * θ p.1)
      (volume.prod m) := by
    refine ((hθi.mul_prod (integrable_const (1 : ℝ)) (ν := m)).const_mul B).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous fun p : Euc d × Euc d => ((G (p.1 - p.2) : ℝ) : ℂ) * θ p.1 := by
        have := Complex.continuous_ofReal
        fun_prop
      exact h1.aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hB (p.1 - p.2)
      calc |G (p.1 - p.2)| * ‖θ p.1‖ ≤ B * ‖θ p.1‖ := by gcongr
        _ = B * (‖θ p.1‖ * 1) := by ring
  have hsec : ∀ y : Euc d, ∫ x, ((G (x - y) : ℝ) : ℂ) * θ x = 0 := fun y =>
    lowv_fs_translate hG y θ hθ
  have e : ∀ x : Euc d, ((∫ y, G (x - y) ∂m : ℝ) : ℂ) * θ x =
      ∫ y, ((G (x - y) : ℝ) : ℂ) * θ x ∂m := by
    intro x
    rw [← integral_complex_ofReal, ← integral_mul_const]
  simp_rw [e]
  rw [integral_integral_swap hint]
  simp_rw [hsec]
  simp

theorem uhigh_conv_int {B : ℝ} {G : Euc d → ℝ} (hGc : Continuous G) (hB : ∀ x, |G x| ≤ B)
    (m : Measure (Euc d)) [IsFiniteMeasure m] (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => ((∫ y, G (x - y) ∂m : ℝ) : ℂ) * φ x) := by
  have hcont : Continuous (fun x => ∫ y, G (x - y) ∂m) := by
    refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_)
      (fun x => ae_of_all _ fun y => ?_) (integrable_const _) (ae_of_all _ fun y => ?_)
    · exact (hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · simpa [Real.norm_eq_abs] using hB _
    · exact hGc.comp (continuous_id.sub continuous_const)
  have hbd : ∀ x, ‖((∫ y, G (x - y) ∂m : ℝ) : ℂ)‖ ≤ B * m.real Set.univ := by
    intro x
    rw [Complex.norm_real]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun y => by
      simpa [Real.norm_eq_abs] using hB _)
  exact φ.integrable.bdd_mul (c := B * m.real Set.univ)
    (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable (ae_of_all _ hbd)

theorem uhigh_u_fsupp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (σ : SMeas d)
    [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg] (i : Fin d) :
    FourierSuppIn 2 (fun x => σ.convForce (gloForce s) x i) := by
  obtain ⟨B, hB⟩ := uhigh_gloForce_bound hd hs0 hsd
  have hc := (gloForce_props hd hs0 hsd).1.continuous
  have hGc : Continuous (fun x : Euc d => gloForce s x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hc
  have hGB : ∀ x : Euc d, |gloForce s x i| ≤ B := fun x =>
    (by simpa using PiLp.norm_apply_le (gloForce s x) i : |gloForce s x i| ≤ ‖gloForce s x‖).trans
      (hB x)
  have hint : ∀ (m : Measure (Euc d)) [IsFiniteMeasure m] (x : Euc d),
      Integrable (fun y => gloForce s (x - y)) m := fun m _ x =>
    (Integrable.of_bound (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable B
      (ae_of_all _ fun y => hB _))
  have hcomp : ∀ x, σ.convForce (gloForce s) x i =
      (∫ y, gloForce s (x - y) i ∂σ.pos) + (-1) * ∫ y, gloForce s (x - y) i ∂σ.neg := by
    intro x
    unfold SMeas.convForce SMeas.intV
    have h1 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm (hint σ.pos x)
    have h2 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm (hint σ.neg x)
    have h1' : (∫ y, gloForce s (x - y) ∂σ.pos) i = ∫ y, gloForce s (x - y) i ∂σ.pos := by
      simpa using h1.symm
    have h2' : (∫ y, gloForce s (x - y) ∂σ.neg) i = ∫ y, gloForce s (x - y) i ∂σ.neg := by
      simpa using h2.symm
    rw [PiLp.sub_apply, h1', h2']
    ring
  have hfun : (fun x => σ.convForce (gloForce s) x i) = fun x =>
      (∫ y, gloForce s (x - y) i ∂σ.pos) + (-1) * ∫ y, gloForce s (x - y) i ∂σ.neg :=
    funext hcomp
  rw [hfun]
  exact lowv_fs_add (uhigh_fs_conv (lowv_gloForce_fsupp hd hs0 hsd i) hGc hGB σ.pos)
    (lowv_fs_smul (uhigh_fs_conv (lowv_gloForce_fsupp hd hs0 hsd i) hGc hGB σ.neg) (-1))
    (uhigh_conv_int hGc hGB σ.pos)
    (fun φ => by
      have := uhigh_conv_int hGc hGB σ.neg φ
      have e : ∀ x : Euc d, (((-1 * ∫ y, gloForce s (x - y) i ∂σ.neg : ℝ)) : ℂ) * φ x =
          (-1 : ℂ) * (((∫ y, gloForce s (x - y) i ∂σ.neg : ℝ) : ℂ) * φ x) := fun x => by
        push_cast; ring
      simp_rw [e]
      exact this.const_mul _)

end HRS.Commutator.Whole.UHIGH
