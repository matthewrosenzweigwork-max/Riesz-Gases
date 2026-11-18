import HRS.MS.S113X2A1a

/-!
# S11.3 X2 part A1b: regularity of the drift and of the generator on test functions supported off collisions
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_isClosed_collision (d N : ℕ) : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {x : EucConfig d N | x i = x j} := by
    ext x; simp [eucCollisionSet]
  rw [this]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem s113a_isOpen_free (d N : ℕ) : IsOpen (eucCollisionSet d N)ᶜ :=
  (s113a_isClosed_collision d N).isOpen_compl

theorem s113a_gradient_conf_contDiff (q : ℝ) : ContDiff ℝ ∞ (gradient (confinement (d := d) q)) := by
  have h1 : ContDiff ℝ ∞ (confinement (d := d) q) := by
    unfold confinement
    exact (contDiff_const.mul (contDiff_norm_sq ℝ)).div_const _
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (confinement (d := d) q)) := h1.fderiv_right (by simp)
  have : gradient (confinement (d := d) q) =
      (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (confinement (d := d) q) := by
    funext x; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h2

theorem s113a_rkg_contDiffOn (s : ℝ) :
    ContDiffOn ℝ ∞ (rieszKernelGrad d s) {x : Euc d | x ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (rieszKernel d s)) {x : Euc d | x ≠ 0} :=
    (rieszKernel_contDiffOn (d := d) (s := s)).fderiv_of_isOpen isOpen_ne (by simp)
  have : rieszKernelGrad d s =
      (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (rieszKernel d s) := by
    funext x; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp_contDiffOn h1

/-- The physical drift is smooth on the collision-free set. -/
theorem s113a_drift_contDiffOn (s q β : ℝ) :
    ContDiffOn ℝ ∞ (fun x : EucConfig d N => fun i => particleDriftW (quadraticGradientDyn d s q β) x i)
      (eucCollisionSet d N)ᶜ := by
  refine contDiffOn_pi.2 fun i => ?_
  have hMv : ContDiff ℝ ∞ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (-1 : Matrix (Fin d) (Fin d) ℝ))).contDiff
  have hV : ContDiff ℝ ∞ (fun x : EucConfig d N => gradient (confinement (d := d) q) (x i)) :=
    (s113a_gradient_conf_contDiff q).comp (contDiff_apply ℝ (Euc d) i)
  have e : (fun x : EucConfig d N => particleDriftW (quadraticGradientDyn d s q β) x i) = fun x =>
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (x i - x j))
        - gradient (confinement (d := d) q) (x i) := by
    funext x
    simp only [particleDriftW, quadraticGradientDyn]
  show ContDiffOn ℝ ∞ (fun x : EucConfig d N => particleDriftW (quadraticGradientDyn d s q β) x i)
    (eucCollisionSet d N)ᶜ
  rw [e]
  refine ContDiffOn.sub (ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)) hV.contDiffOn
  have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
  refine hMv.comp_contDiffOn ((s113a_rkg_contDiffOn (d := d) s).comp
    (f := fun x : EucConfig d N => x i - x j) ?_ ?_)
  · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
  · intro x hx h
    exact hx ⟨i, j, hij, sub_eq_zero.1 h⟩

theorem s113a_drift_continuousAt (s q β : ℝ) {x : EucConfig d N} (hx : x ∉ eucCollisionSet d N) :
    ContinuousAt (fun x : EucConfig d N => fun i => particleDriftW (quadraticGradientDyn d s q β) x i) x :=
  ((s113a_drift_contDiffOn (N := N) s q β).continuousOn.continuousAt
    ((s113a_isOpen_free d N).mem_nhds hx))

/-- A smooth space-time function vanishing for `x ∉ K` (`K` compact, collision-free): its derivatives vanish there. -/
theorem s113a_fderiv_eventually_zero {Phi : ℝ × EucConfig d N → ℝ} {K : Set (EucConfig d N)}
    (hK : IsClosed K) (hsupp : ∀ r x, x ∉ K → Phi (r, x) = 0) {p : ℝ × EucConfig d N} (hp : p.2 ∉ K) :
    Phi =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hp] with q hq
  exact hsupp q.1 q.2 hq

/-- First and second derivatives of a smooth function vanishing for `x ∉ K` vanish there. -/
theorem s113a_fderiv_zero_off {Phi : ℝ × EucConfig d N → ℝ} {K : Set (EucConfig d N)}
    (hK : IsClosed K) (hsupp : ∀ r x, x ∉ K → Phi (r, x) = 0) (p : ℝ × EucConfig d N) (hp : p.2 ∉ K) :
    fderiv ℝ Phi p = 0 ∧ fderiv ℝ (fderiv ℝ Phi) p = 0 := by
  have h0 := s113a_fderiv_eventually_zero hK hsupp hp
  have h1 : fderiv ℝ Phi =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [h0.eventuallyEq_nhds] with q hq
    simpa using hq.fderiv_eq
  exact ⟨by simpa using h0.fderiv_eq, by simpa using h1.fderiv_eq⟩

/-- The generator of a smooth test function vanishing off a compact collision-free `K` is continuous and vanishes
off `K`. -/
theorem s113a_gen_continuous (s q β : ℝ) {Phi : ℝ × EucConfig d N → ℝ} (hPhi : ContDiff ℝ ∞ Phi)
    {K : Set (EucConfig d N)} (hK : IsClosed K) (hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N)
    (hsupp : ∀ r x, x ∉ K → Phi (r, x) = 0) :
    Continuous (s113a_gen d s q β N Phi) ∧ ∀ r x, x ∉ K → s113a_gen d s q β N Phi (r, x) = 0 := by
  have hD1 : Continuous (fderiv ℝ Phi) := hPhi.continuous_fderiv (by simp)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ Phi)) :=
    (hPhi.fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)
  have hzero := s113a_fderiv_zero_off (Phi := Phi) hK hsupp
  have hgen0 : ∀ r x, x ∉ K → s113a_gen d s q β N Phi (r, x) = 0 := by
    intro r x hx
    obtain ⟨h1, h2⟩ := hzero (r, x) hx
    simp [s113a_gen, HRS.MC.CepP3.Lop, h1, h2]
  refine ⟨?_, hgen0⟩
  unfold s113a_gen HRS.MC.CepP3.Lop
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : EucConfig d N))).continuous.comp hD1
  · refine continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)
    exact (hD2.clm_apply continuous_const).clm_apply continuous_const
  · rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.2 ∈ K
    · have hb : ContinuousAt (s113a_drift d s q β N) p :=
        (s113a_drift_continuousAt s q β (hKfree _ hp)).comp (f := Prod.snd) continuousAt_snd
      exact (hD1.continuousAt (x := p)).clm_apply (continuousAt_const.prodMk hb)
    · have hz : ∀ᶠ r in 𝓝 p, fderiv ℝ Phi r (0, s113a_drift d s q β N r) = 0 := by
        filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hp] with r hr
        simp [(hzero r hr).1]
      exact continuousAt_const.congr (hz.mono fun r hr => hr.symm)

/-- A continuous space-time function vanishing off a compact `K` is bounded on `[0,T] × E`. -/
theorem s113a_bound_on_strip {F' : Type*} [NormedAddCommGroup F'] {K : Set (EucConfig d N)}
    (hK : IsCompact K) {F : ℝ × EucConfig d N → F'} (hF : Continuous F)
    (h0 : ∀ r x, x ∉ K → F (r, x) = 0) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc 0 T, ∀ x, ‖F (r, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := T)).prod hK).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r hr x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (r, x) ⟨hr, hx⟩).trans (le_max_left _ _)
  · rw [h0 r x hx]; simp

end HRS.MS.S113X2

end
