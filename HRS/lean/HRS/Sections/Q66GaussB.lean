import HRS.Sections.Q66GaussA

/-!
# Packet Q66: Gaussian integration by parts on `EuclideanSpace ℝ (Fin n)`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

variable {n : ℕ}

theorem q66_insertNth_path {m : ℕ} (j : Fin (m + 1)) (η' : Fin m → ℝ) (t : ℝ) :
    (WithLp.toLp 2 (Fin.insertNth j t η') : EuclideanSpace ℝ (Fin (m + 1))) =
      WithLp.toLp 2 (Fin.insertNth j (0 : ℝ) η') + t • EuclideanSpace.single j (1 : ℝ) := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨i', h⟩
  · subst h; simp
  · subst h; simp [Fin.insertNth_apply_succAbove, EuclideanSpace.single_apply,
      Fin.succAbove_ne]

theorem q66_stdGaussian_integrable_growth {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hm : AEStronglyMeasurable h (stdGaussian (EuclideanSpace ℝ (Fin n)))) (K : ℝ)
    (hK : ∀ x, |h x| ≤ K * (1 + ‖x‖)) (i : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * h x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_two_id
  have i1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := (h2.integrable one_le_two).norm
  have i2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := h2.integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((i1.add i2).const_mul |K|) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((measurable_pi_apply i).comp (PiLp.continuous_ofLp 2 _).measurable).aestronglyMeasurable.mul hm
  · rw [Real.norm_eq_abs, abs_mul]
    have hxi : |x i| ≤ ‖x‖ := by
      have := PiLp.norm_apply_le x i
      simpa using this
    calc |x i| * |h x| ≤ ‖x‖ * (|K| * (1 + ‖x‖)) :=
          mul_le_mul hxi ((hK x).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)))
            (abs_nonneg _) (norm_nonneg _)
      _ = |K| * (‖x‖ + ‖x‖ ^ 2) := by ring

theorem q66_std_integrable_of_growth {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (K : ℝ)
    (hfK : ∀ x, |f x| ≤ K * (1 + ‖x‖)) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_two_id
  have i1' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := (h2.integrable one_le_two).norm
  refine Integrable.mono' (((integrable_const (1 : ℝ)).add i1').const_mul |K|) hf.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (hfK x).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))

theorem q66_stdGaussian_ibp {m : ℕ} (i : Fin (m + 1)) {h : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hh : ContDiff ℝ 1 h) (K : ℝ) (hK : ∀ x, |h x| ≤ K * (1 + ‖x‖))
    (hK' : ∀ x, ‖fderiv ℝ h x‖ ≤ K * (1 + ‖x‖)) :
    ∫ x, x i * h x ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) =
      ∫ x, fderiv ℝ h x (EuclideanSpace.single i 1)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) := by
  have htl : Measurable (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) :=
    (PiLp.continuous_toLp 2 _).measurable
  have hmap : (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1).map
      (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) =
      stdGaussian (EuclideanSpace ℝ (Fin (m + 1))) := map_pi_eq_stdGaussian
  have hhc : Continuous h := hh.continuous
  have hdc : Continuous (fun x => fderiv ℝ h x (EuclideanSpace.single i 1)) :=
    (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdK : ∀ x, |fderiv ℝ h x (EuclideanSpace.single i 1)| ≤ K * (1 + ‖x‖) := by
    intro x
    refine (le_trans ?_ (hK' x))
    have := (fderiv ℝ h x).le_opNorm (EuclideanSpace.single i 1)
    simpa [Real.norm_eq_abs] using this
  have hxi : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x i * h x) :=
    ((PiLp.continuous_apply 2 _ i).mul hhc)
  have i1 := q66_stdGaussian_integrable_growth hhc.aestronglyMeasurable K hK i
  have i2 := q66_std_integrable_of_growth hdc K hdK
  have i3 := q66_std_integrable_of_growth hhc K hK
  have e1 := integral_map (μ := Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) htl.aemeasurable
    (f := fun x : EuclideanSpace ℝ (Fin (m + 1)) => x i * h x) hxi.aestronglyMeasurable
  have e2 := integral_map (μ := Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) htl.aemeasurable
    (f := fun x : EuclideanSpace ℝ (Fin (m + 1)) => fderiv ℝ h x (EuclideanSpace.single i 1))
    hdc.aestronglyMeasurable
  rw [hmap] at e1 e2
  rw [e1, e2]
  rw [← hmap] at i1 i2 i3
  have j1 := (integrable_map_measure hxi.aestronglyMeasurable htl.aemeasurable).1 i1
  have j2 := (integrable_map_measure hdc.aestronglyMeasurable htl.aemeasurable).1 i2
  have j3 := (integrable_map_measure hhc.aestronglyMeasurable htl.aemeasurable).1 i3
  refine q66_gaussN_ibp i (H := fun η => h (WithLp.toLp 2 η))
    (dH := fun η => fderiv ℝ h (WithLp.toLp 2 η) (EuclideanSpace.single i 1)) (fun η' t => ?_)
    (hhc.measurable.comp htl) (hdc.measurable.comp htl) j1 j2 j3
  have hpath : HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (Fin.insertNth i t η') : EuclideanSpace ℝ (Fin (m + 1))))
      (EuclideanSpace.single i (1 : ℝ)) t := by
    have e : (fun t : ℝ => (WithLp.toLp 2 (Fin.insertNth i t η') : EuclideanSpace ℝ (Fin (m + 1)))) =
        fun t : ℝ => (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) η') : EuclideanSpace ℝ (Fin (m + 1))) +
          t • EuclideanSpace.single i (1 : ℝ) := funext fun t => q66_insertNth_path i η' t
    rw [e]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
      (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) η') : EuclideanSpace ℝ (Fin (m + 1)))
  have hd := ((hh.differentiable one_ne_zero) (WithLp.toLp 2 (Fin.insertNth i t η'))).hasFDerivAt
  exact hd.comp_hasDerivAt t hpath

end HRS.Q66

end
