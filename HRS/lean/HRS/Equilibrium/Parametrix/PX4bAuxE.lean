import HRS.Equilibrium.Parametrix.PX4bAuxD

/-!
# Packet PX4b auxiliaries E: calculus along coordinate lines of the torus

Translation `T i t x = x + t e_i`, the fundamental theorem of calculus along a line avoiding a
point, the a.e. avoidance of lines, and the integration by parts formula for functions that are
`C¹` off a single point (the lines trick: no flux through a point in `d ≥ 2`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The `i`-th coordinate direction in `ℝ^d`. -/
abbrev px4b_e (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

/-- Translation by `t e_i` on the torus. -/
def px4b_T (i : Fin d) (t : ℝ) (x : Torus d) : Torus d := x + Torus.mk (t • px4b_e i)

lemma px4b_mk_rep_add (i : Fin d) (t : ℝ) (x : Torus d) :
    Torus.mk (Torus.rep x + t • px4b_e i) = px4b_T i t x := by
  unfold px4b_T
  rw [mk_add_eq, Torus.mk_rep]

lemma px4b_T_zero (i : Fin d) (x : Torus d) : px4b_T i 0 x = x := by
  unfold px4b_T
  rw [zero_smul, mk_isLat isLat_zero, add_zero]

lemma px4b_T_one (i : Fin d) (x : Torus d) : px4b_T i 1 x = x := by
  unfold px4b_T
  have : Torus.mk ((1 : ℝ) • px4b_e i) = 0 := by
    rw [one_smul]
    exact mk_isLat (fun j => by
      by_cases h : j = i
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h, EuclideanSpace.single_apply]⟩)
  rw [this, add_zero]


lemma px4b_T_add (i : Fin d) (s t : ℝ) (x : Torus d) :
    px4b_T i s (px4b_T i t x) = px4b_T i (s + t) x := by
  unfold px4b_T
  rw [add_smul, mk_add_eq]
  abel

/-- FTC along the line through `x` in direction `e_i`, for a function that is `C¹` at every point
of the line. -/
lemma px4b_line_ftc (i : Fin d) (u : Torus d → ℝ) (x : Torus d)
    (hu : ∀ t : ℝ, ContDiffAt ℝ 1 (Torus.lift u) (Torus.rep x + t • px4b_e i)) (a b : ℝ) :
    u (px4b_T i b x) - u (px4b_T i a x) =
      ∫ s in a..b, Torus.partialDeriv i u (px4b_T i s x) := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Torus.lift u (Torus.rep x + s • px4b_e i))
      (fderiv ℝ (Torus.lift u) (Torus.rep x + t • px4b_e i) (px4b_e i)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Torus.rep x + s • px4b_e i) (px4b_e i) t := by
      simpa using ((hasDerivAt_id t).smul_const (px4b_e i)).const_add (Torus.rep x)
    have h2 := ((hu t).differentiableAt (by norm_num)).hasFDerivAt
    exact h2.comp_hasDerivAt t h1
  have hder : ∀ s : ℝ, Torus.partialDeriv i u (px4b_T i s x) =
      fderiv ℝ (Torus.lift u) (Torus.rep x + s • px4b_e i) (px4b_e i) := by
    intro s
    have := px4b_lift_partialDeriv u i (Torus.rep x + s • px4b_e i)
    simp only [Torus.lift, Function.comp] at this
    rw [px4b_mk_rep_add] at this
    exact this
  have hcont : Continuous (fun s : ℝ => fderiv ℝ (Torus.lift u) (Torus.rep x + s • px4b_e i)
      (px4b_e i)) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have h1 : ContinuousAt (fderiv ℝ (Torus.lift u)) (Torus.rep x + t • px4b_e i) :=
      ((hu t).fderiv_right (m := 0) (by norm_num)).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => Torus.rep x + s • px4b_e i) t :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    exact (ContinuousAt.comp (g := fderiv ℝ (Torus.lift u)) (f := fun s : ℝ => Torus.rep x + s • px4b_e i)
      h1 h2).clm_apply continuousAt_const
  simp_rw [hder]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun s : ℝ => Torus.lift u (Torus.rep x + s • px4b_e i))
    (f' := fun s => fderiv ℝ (Torus.lift u) (Torus.rep x + s • px4b_e i) (px4b_e i))
    (fun t _ => hline t) (hcont.intervalIntegrable _ _)
  rw [this]
  simp only [Torus.lift, Function.comp, px4b_mk_rep_add]


lemma px4b_T_apply_ne (i k : Fin d) (hk : k ≠ i) (t : ℝ) (x : Torus d) :
    px4b_T i t x k = x k := by
  unfold px4b_T Torus.mk
  simp [PiLp.single_apply, hk]

/-- The set of points whose `e_i`-line passes through `y` is null (`d ≥ 2`). -/
lemma px4b_null_line (hd : 2 ≤ d) (i : Fin d) (y : Torus d) :
    (volume : Measure (Torus d)) {x : Torus d | ∃ t : ℝ, px4b_T i t x = y} = 0 := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨k, hk⟩ := exists_ne i
  haveI : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨fun y => volume_singleton_circle y⟩
  have h := MeasureTheory.Measure.pi_hyperplane (μ := fun _ : Fin d => (volume : Measure UnitAddCircle))
    k (y k)
  refine measure_mono_null (fun x hx => ?_) h
  obtain ⟨t, ht⟩ := hx
  show x k = y k
  rw [← ht, px4b_T_apply_ne i k hk]

lemma px4b_measurePreserving_T (i : Fin d) (t : ℝ) :
    MeasurePreserving (px4b_T i t) (volume : Measure (Torus d)) volume := by
  unfold px4b_T
  exact measurePreserving_add_right volume _


lemma px4b_continuous_T (i : Fin d) : Continuous (fun p : ℝ × Torus d => px4b_T i p.1 p.2) := by
  unfold px4b_T
  refine continuous_snd.add ?_
  refine continuous_pi fun k => ?_
  simp only [Torus.mk]
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply k).comp
    ((continuous_fst.smul continuous_const)))

/-- A function integrated over the torus equals the integral of its averages over the lines in
direction `e_i`. -/
lemma px4b_integral_eq_line_avg (i : Fin d) {A : Torus d → ℝ} (hA : Integrable A) :
    ∫ x, A x = ∫ x, ∫ s in (0 : ℝ)..1, A (px4b_T i s x) := by
  set μa : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμa
  haveI : IsProbabilityMeasure μa := ⟨by simp [hμa]⟩
  have hshear : MeasurePreserving (fun p : ℝ × Torus d => (p.1, px4b_T i p.1 p.2))
      (μa.prod volume) (μa.prod volume) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id μa) ?_ ?_
    · exact (px4b_continuous_T i).measurable
    · exact Eventually.of_forall fun s => (px4b_measurePreserving_T i s).map_eq
  have hAint : Integrable (fun p : ℝ × Torus d => A (px4b_T i p.1 p.2)) (μa.prod volume) :=
    hshear.integrable_comp_of_integrable
      ((measurePreserving_snd (μ := μa) (ν := volume)).integrable_comp_of_integrable hA)
  have e1 := integral_integral_swap (f := fun (s : ℝ) (x : Torus d) => A (px4b_T i s x)) hAint
  have e2 : ∀ s : ℝ, ∫ x, A (px4b_T i s x) = ∫ x, A x := fun s => by
    unfold px4b_T
    exact integral_add_right_eq_self A _
  simp only [e2] at e1
  rw [integral_const, hμa] at e1
  simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul] at e1
  rw [e1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [intervalIntegral.integral_of_le zero_le_one]

/-- If the line averages vanish off a null set, the integral vanishes. -/
lemma px4b_integral_eq_zero_of_line (hd : 2 ≤ d) (i : Fin d) (y : Torus d) {A : Torus d → ℝ}
    (hA : Integrable A)
    (hl : ∀ x : Torus d, (∀ t : ℝ, px4b_T i t x ≠ y) → ∫ s in (0 : ℝ)..1, A (px4b_T i s x) = 0) :
    ∫ x, A x = 0 := by
  rw [px4b_integral_eq_line_avg i hA]
  have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ t : ℝ, px4b_T i t x ≠ y := by
    have := px4b_null_line hd i y
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) this
    simpa using hx
  have : (fun x : Torus d => ∫ s in (0 : ℝ)..1, A (px4b_T i s x)) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hae] with x hx using hl x hx
  rw [integral_congr_ae this]
  simp


/-- Pointwise product rule for `partialDeriv` at a point where both factors are differentiable. -/
lemma px4b_partialDeriv_mul (i : Fin d) {ψ h : Torus d → ℝ} {v : Euc d}
    (hψ : DifferentiableAt ℝ (Torus.lift ψ) v) (hh : DifferentiableAt ℝ (Torus.lift h) v) :
    Torus.partialDeriv i (fun w => ψ w * h w) (Torus.mk v) =
      ψ (Torus.mk v) * Torus.partialDeriv i h (Torus.mk v) +
        Torus.partialDeriv i ψ (Torus.mk v) * h (Torus.mk v) := by
  have e1 : Torus.partialDeriv i (fun w => ψ w * h w) (Torus.mk v) =
      fderiv ℝ (Torus.lift fun w => ψ w * h w) v (px4b_e i) := px4b_lift_partialDeriv _ i v
  have e2 : Torus.partialDeriv i h (Torus.mk v) = fderiv ℝ (Torus.lift h) v (px4b_e i) :=
    px4b_lift_partialDeriv _ i v
  have e3 : Torus.partialDeriv i ψ (Torus.mk v) = fderiv ℝ (Torus.lift ψ) v (px4b_e i) :=
    px4b_lift_partialDeriv _ i v
  have hm := hψ.hasFDerivAt.mul hh.hasFDerivAt
  have hm' : HasFDerivAt (Torus.lift (fun w => ψ w * h w))
      (Torus.lift ψ v • fderiv ℝ (Torus.lift h) v + Torus.lift h v • fderiv ℝ (Torus.lift ψ) v) v := hm
  rw [e1, e2, e3, hm'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Torus.lift, Function.comp_apply]
  ring

/-- Integration by parts for a function that is `C¹` off a point (with integrable derivative):
there is no flux through a point in dimension `d ≥ 2`. -/
theorem px4b_ibp (hd : 2 ≤ d) (i : Fin d) {y : Torus d} {h ψ : Torus d → ℝ}
    (hh : ∀ v : Euc d, Torus.mk v ≠ y → ContDiffAt ℝ 1 (Torus.lift h) v)
    (hψ : Torus.IsCk 1 ψ) (hhi : Integrable h) (hdh : Integrable (Torus.partialDeriv i h)) :
    ∫ x, ψ x * Torus.partialDeriv i h x = - ∫ x, Torus.partialDeriv i ψ x * h x := by
  have hψc : Continuous ψ := KernelGrad.continuous_of_lift hψ.continuous
  have hψ'c : Continuous (Torus.partialDeriv i ψ) := PDE.continuous_partialDeriv i ψ hψ
  obtain ⟨C1, hC1⟩ := PDE.MFSchauder.exists_bound_of_cont hψc
  obtain ⟨C2, hC2⟩ := PDE.MFSchauder.exists_bound_of_cont hψ'c
  have I1 : Integrable (fun x => ψ x * Torus.partialDeriv i h x) :=
    hdh.bdd_mul (c := C1) hψc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC1 x)
  have I2 : Integrable (fun x => Torus.partialDeriv i ψ x * h x) :=
    hhi.bdd_mul (c := C2) hψ'c.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC2 x)
  have hA := I1.add I2
  have hz := px4b_integral_eq_zero_of_line hd i y hA (fun x hx => by
    set u : Torus d → ℝ := fun w => ψ w * h w with hu
    have hcd : ∀ t : ℝ, ContDiffAt ℝ 1 (Torus.lift u) (Torus.rep x + t • px4b_e i) := by
      intro t
      have hne : Torus.mk (Torus.rep x + t • px4b_e i) ≠ y := by
        rw [px4b_mk_rep_add]; exact hx t
      have h1 : ContDiffAt ℝ 1 (Torus.lift ψ) (Torus.rep x + t • px4b_e i) :=
        (show ContDiff ℝ 1 (Torus.lift ψ) from hψ).contDiffAt
      exact h1.mul (hh _ hne)
    have hf := px4b_line_ftc i u x hcd 0 1
    rw [px4b_T_one, px4b_T_zero, sub_self] at hf
    have hf' : ∫ s in (0 : ℝ)..1, Torus.partialDeriv i u (px4b_T i s x) = 0 := hf.symm
    refine Eq.trans (intervalIntegral.integral_congr (fun s _ => ?_)) hf'
    have hne : Torus.mk (Torus.rep x + s • px4b_e i) ≠ y := by
      rw [px4b_mk_rep_add]; exact hx s
    have hψd : Differentiable ℝ (Torus.lift ψ) :=
      (show ContDiff ℝ 1 (Torus.lift ψ) from hψ).differentiable one_ne_zero
    have := px4b_partialDeriv_mul i (ψ := ψ) (h := h) (v := Torus.rep x + s • px4b_e i)
      (hψd _) (((hh _ hne).differentiableAt one_ne_zero))
    rw [px4b_mk_rep_add] at this
    exact this.symm ▸ rfl)
  have hz' : ∫ x, (ψ x * Torus.partialDeriv i h x + Torus.partialDeriv i ψ x * h x) = 0 := hz
  rw [integral_add I1 I2] at hz'
  linarith

end HRS.Parx
end
