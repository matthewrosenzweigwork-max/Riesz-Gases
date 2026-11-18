import HRS.Equilibrium.LocalDivRadial
open MeasureTheory Set Metric
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

theorem eucDist_shift (x z : Torus d) : Torus.eucDist x (x + z) = Torus.eucDist z 0 := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : x i - (x + z) i = -(z i - (0 : Torus d) i) := by simp
  rw [this, norm_neg]

theorem integral_torus_cube (G : Torus d → ℝ) (hG : Measurable G) :
    ∫ z, G z = ∫ w in cube d, G (Torus.mk w) := by
  have hmp := mk_measurePreserving (d := d)
  rw [← hmp.map_eq]
  exact integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable

theorem integral_shift_cube (x : Torus d) (G : Torus d → ℝ) (hG : Measurable G) :
    ∫ y, G y = ∫ w in cube d, G (x + Torus.mk w) := by
  have h1 : ∫ y, G y = ∫ z, G (x + z) := (integral_add_left_eq_self (μ := (volume : Measure (Torus d))) G x).symm
  rw [h1]
  exact integral_torus_cube (fun z => G (x + z)) (hG.comp (measurable_const_add x))

theorem lip_shift {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : Torus d) (w : Euc d), |f (x + Torus.mk w) - f x| ≤ L * ‖w‖ := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  obtain ⟨L, hL⟩ := HRS.rem_exists_lipschitz_of_periodic (Torus.lift f)
    (hF.of_le (by norm_cast)) (fun w n => Torus.lift_periodic f w n)
  refine ⟨L, L.2, fun x w => ?_⟩
  have := hL.dist_le_mul (Torus.rep x + w) (Torus.rep x)
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
  have e : Torus.lift f (Torus.rep x + w) = f (x + Torus.mk w) := by
    simp [Torus.lift, mk_add', Torus.mk_rep]
  have e2 : Torus.lift f (Torus.rep x) = f x := by simp [Torus.lift, Torus.mk_rep]
  rw [e, e2] at this
  exact this

theorem measurable_hTransport {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) := by
  have e : (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) = fun p =>
      ∑ i, (Torus.partialDeriv i f p.1 - Torus.partialDeriv i f p.2) *
        (periodicRieszGrad d s (p.1 - p.2)) i := by
    funext p; exact hTransport_eq s f hf p.1 p.2
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hc : Continuous (Torus.partialDeriv i f) :=
    StaticLimitsAux.continuous_partialDeriv (isCk_one_of_smooth hf) i
  refine ((hc.measurable.comp measurable_fst).sub (hc.measurable.comp measurable_snd)).mul ?_
  exact ((EuclideanSpace.proj i).continuous.measurable.comp
    ((HRS.KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)))

theorem measurable_eucDist : Measurable (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => ?_)
  have h1 : Continuous fun p : Torus d × Torus d => ‖p.1 i - p.2 i‖ ^ 2 :=
    (continuous_norm.comp (((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd))).pow 2
  exact h1.measurable

theorem hTransport_self {s : ℝ} (x : Torus d) (f : Torus d → ℝ) : hTransport d s f x x = 0 := by
  simp [hTransport]

end HRS.LocalDivAux
