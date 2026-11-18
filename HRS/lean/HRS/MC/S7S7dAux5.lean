import HRS.MC.S7S7dAux4
import HRS.MC.SEdgeB13c

/-!
# Packet `s7_S7d_uniform_limits`, helper 5: the finite-dimensional test functions

For `f` in the class `s7d_Cl` on a normed space `E`, a continuous linear `ι : R^p → E` and `u, u' ∈ E`:
`Ψ(z) = D²f(ι z)[u,u']` is bounded by `‖u‖‖u'‖`, `C^1` with `‖DΨ‖ ≤ ‖ι‖‖u‖‖u'‖`, and
`DΨ(z)[e_c] = D³f(ι z)[u,u',ι e_c]`.  Likewise `Ψ₁(z) = Df(ι z)[u]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

section Psi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}

/-- `Ψ(z) = D²f(ι z)[u,u']`. -/
def s7d_Psi2 (f : E → ℝ) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u u' : E)
    (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  iteratedFDeriv ℝ 2 f (ι z) ![u, u']

/-- `Ψ₁(z) = Df(ι z)[u]`. -/
def s7d_Psi1 (f : E → ℝ) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E)
    (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  fderiv ℝ f (ι z) u

theorem s7d_D3_cyc {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z x y w : E) :
    iteratedFDeriv ℝ 3 f z ![w, x, y] = iteratedFDeriv ℝ 3 f z ![x, y, w] := by
  rw [HRS.MC.SEdge.B13c.b13c_D3, HRS.MC.SEdge.B13c.b13c_D3]
  exact HRS.MC.SEdge.B13c.b13c_perm hf z x y w

theorem s7d_D3_bound {f : E → ℝ} {z : E} (h : ‖iteratedFDeriv ℝ 3 f z‖ ≤ 1) (x y w : E) :
    |iteratedFDeriv ℝ 3 f z ![x, y, w]| ≤ ‖x‖ * ‖y‖ * ‖w‖ := by
  have := (iteratedFDeriv ℝ 3 f z).le_opNorm ![x, y, w]
  rw [Real.norm_eq_abs] at this
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons] at this
  calc _ ≤ _ := this
    _ ≤ 1 * (‖x‖ * ‖y‖ * ‖w‖) := by
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := one_mul _

theorem s7d_D2_bound {f : E → ℝ} {z : E} (h : ‖iteratedFDeriv ℝ 2 f z‖ ≤ 1) (x y : E) :
    |iteratedFDeriv ℝ 2 f z ![x, y]| ≤ ‖x‖ * ‖y‖ := by
  have := (iteratedFDeriv ℝ 2 f z).le_opNorm ![x, y]
  rw [Real.norm_eq_abs] at this
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
  calc _ ≤ _ := this
    _ ≤ 1 * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := one_mul _

/-- the derivative of `x ↦ D²f(x)[u,u']`. -/
theorem s7d_hasFDerivAt_D2 {f : E → ℝ} (hf : ContDiff ℝ 3 f) (u u' : E) (x : E) :
    HasFDerivAt (fun x => iteratedFDeriv ℝ 2 f x ![u, u'])
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, u']).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 f) x)) x := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    (hf.differentiable_iteratedFDeriv (m := 2) (by norm_num)) x
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, u']).hasFDerivAt.comp x
    hd.hasFDerivAt

theorem s7d_fderiv_D2_apply {f : E → ℝ} (hf : ContDiff ℝ 3 f) (u u' : E) (x v : E) :
    fderiv ℝ (fun x => iteratedFDeriv ℝ 2 f x ![u, u']) x v = iteratedFDeriv ℝ 3 f x ![v, u, u'] := by
  rw [(s7d_hasFDerivAt_D2 hf u u' x).fderiv]
  rw [iteratedFDeriv_succ_apply_left]
  simp

theorem s7d_Psi2_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 3 f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E)
    (u u' : E) (z : EuclideanSpace ℝ (Fin p)) :
    HasFDerivAt (s7d_Psi2 f ι u u')
      (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, u']).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 f) (ι z))).comp ι) z :=
  (s7d_hasFDerivAt_D2 hf u u' (ι z)).comp z ι.hasFDerivAt

theorem s7d_Psi2_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u u' : E) (z v : EuclideanSpace ℝ (Fin p)) :
    fderiv ℝ (s7d_Psi2 f ι u u') z v = iteratedFDeriv ℝ 3 f (ι z) ![ι v, u, u'] := by
  rw [(s7d_Psi2_hasFDerivAt hf ι u u' z).fderiv]
  have := s7d_fderiv_D2_apply hf u u' (ι z) (ι v)
  rw [(s7d_hasFDerivAt_D2 hf u u' (ι z)).fderiv] at this
  simpa using this

theorem s7d_Psi2_std {f : E → ℝ} (hf : ContDiff ℝ 3 f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E)
    (u u' : E) (z : EuclideanSpace ℝ (Fin p)) (c : Fin p) :
    fderiv ℝ (s7d_Psi2 f ι u u') z (stdVec c) = iteratedFDeriv ℝ 3 f (ι z) ![u, u', ι (stdVec c)] := by
  rw [s7d_Psi2_fderiv_apply hf]
  exact s7d_D3_cyc hf _ _ _ _

theorem s7d_Psi2_bdd {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u u' : E)
    (z : EuclideanSpace ℝ (Fin p)) : |s7d_Psi2 f ι u u' z| ≤ ‖u‖ * ‖u'‖ :=
  s7d_D2_bound (hf.2 2 (by norm_num) (by norm_num) _) u u'

theorem s7d_Psi2_contDiff {f : E → ℝ} (hf : ContDiff ℝ 4 f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E)
    (u u' : E) : ContDiff ℝ 1 (s7d_Psi2 f ι u u') := by
  have h2 : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 f) := hf.iteratedFDeriv_right (i := 2) (m := 1) (by norm_num)
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, u']).contDiff.comp h2
  exact this.comp ι.contDiff

theorem s7d_Psi2_fderiv_norm {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E)
    (u u' : E) (z : EuclideanSpace ℝ (Fin p)) :
    ‖fderiv ℝ (s7d_Psi2 f ι u u') z‖ ≤ ‖ι‖ * (‖u‖ * ‖u'‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [s7d_Psi2_fderiv_apply (hf.1.of_le (by norm_num))]
  rw [Real.norm_eq_abs]
  refine (s7d_D3_bound (hf.2 3 (by norm_num) (by norm_num) _) _ _ _).trans ?_
  have : ‖ι v‖ ≤ ‖ι‖ * ‖v‖ := ι.le_opNorm v
  calc ‖ι v‖ * ‖u‖ * ‖u'‖ ≤ (‖ι‖ * ‖v‖) * ‖u‖ * ‖u'‖ := by gcongr
    _ = _ := by ring

theorem s7d_Psi2_lip {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u u' : E) :
    LipschitzWith (‖ι‖₊ * (‖u‖₊ * ‖u'‖₊)) (s7d_Psi2 f ι u u') := by
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z => ?_) (fun z => ?_)
  · exact ((s7d_Psi2_contDiff hf.1 ι u u').differentiable one_ne_zero) z
  · have := s7d_Psi2_fderiv_norm hf ι u u' z
    rw [← NNReal.coe_le_coe]
    simpa using this

theorem s7d_Psi2_memCb {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u u' : E) :
    MemCb 1 (s7d_Psi2 f ι u u') := by
  refine ⟨s7d_Psi2_contDiff hf.1 ι u u', fun j hj => ?_⟩
  interval_cases j
  · refine ⟨‖u‖ * ‖u'‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using s7d_Psi2_bdd hf ι u u' z
  · refine ⟨‖ι‖ * (‖u‖ * ‖u'‖), ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [norm_iteratedFDeriv_one] using s7d_Psi2_fderiv_norm hf ι u u' z

end Psi

section Psi1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℕ}

theorem s7d_g_iter_norm {f : E → ℝ} (hf : s7d_Cl f) (u : E) {j : ℕ} (hj : j ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ f y u) x‖ ≤ ‖u‖ := by
  have hg : ContDiff ℝ 3 (fderiv ℝ f) := hf.1.fderiv_right (m := 3) (by norm_num)
  refine (norm_iteratedFDeriv_clm_apply_const (hg.contDiffAt) (N := 3) (n := j)
    (by exact_mod_cast hj)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have : ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ 1 := hf.2 (j + 1) (by omega) (by omega) x
  nlinarith [norm_nonneg u]

theorem s7d_Psi1_contDiff {f : E → ℝ} (hf : ContDiff ℝ 4 f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E)
    (u : E) : ContDiff ℝ 2 (s7d_Psi1 f ι u) :=
  ((hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).comp ι.contDiff

theorem s7d_Psi1_iter_norm {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E)
    {j : ℕ} (hj : j ≤ 2) (z : EuclideanSpace ℝ (Fin p)) :
    ‖iteratedFDeriv ℝ j (s7d_Psi1 f ι u) z‖ ≤ ‖u‖ * ‖ι‖ ^ j := by
  have hg : ContDiff ℝ 2 (fun y => fderiv ℝ f y u) :=
    (hf.1.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have e : s7d_Psi1 f ι u = (fun y => fderiv ℝ f y u) ∘ ι := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right ι hg z (by exact_mod_cast hj)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (s7d_g_iter_norm hf u (by omega) _) le_rfl (by positivity) (norm_nonneg _)

theorem s7d_Psi1_memCb {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E) :
    MemCb 2 (s7d_Psi1 f ι u) :=
  ⟨s7d_Psi1_contDiff hf.1 ι u, fun j hj => ⟨‖u‖ * ‖ι‖ ^ j, by
    rintro _ ⟨z, rfl⟩
    exact s7d_Psi1_iter_norm hf ι u hj z⟩⟩

theorem s7d_Psi1_bdd {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E)
    (z : EuclideanSpace ℝ (Fin p)) : |s7d_Psi1 f ι u z| ≤ ‖u‖ := by
  have := s7d_Psi1_iter_norm hf ι u (j := 0) (by norm_num) z
  simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this

theorem s7d_Psi1_lip {f : E → ℝ} (hf : s7d_Cl f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E) :
    LipschitzWith (‖ι‖₊ * ‖u‖₊) (s7d_Psi1 f ι u) := by
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z => ?_) (fun z => ?_)
  · exact ((s7d_Psi1_contDiff hf.1 ι u).differentiable (by norm_num)) z
  · have := s7d_Psi1_iter_norm hf ι u (j := 1) (by norm_num) z
    rw [norm_iteratedFDeriv_one] at this
    rw [← NNReal.coe_le_coe]
    simpa [mul_comm] using this

theorem s7d_Psi1_iter2 {f : E → ℝ} (hf : ContDiff ℝ 3 f) (ι : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (u : E)
    (z b c : EuclideanSpace ℝ (Fin p)) :
    iteratedFDeriv ℝ 2 (s7d_Psi1 f ι u) z ![b, c] = iteratedFDeriv ℝ 3 f (ι z) ![u, ι b, ι c] := by
  have hg : ContDiff ℝ 2 (fun y => fderiv ℝ f y u) :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have e : s7d_Psi1 f ι u = (fun y => fderiv ℝ f y u) ∘ ι := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right ι hg z (le_refl _)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have := HRS.MC.SEdge.B13c.b13c_shuffle hf (ι z) u (ι b) (ι c)
  rw [← this]
  congr 1
  ext i; fin_cases i <;> rfl

end Psi1

end HRS.MC.Sec7.S7d

end
