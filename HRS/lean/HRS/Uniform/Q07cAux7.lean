import HRS.Uniform.Q07cAux6

/-!
# Q07c, part 7: nonnegativity and measurability of `bures2`, the rank-one fallback
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Bures

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma hsCovForm_sqrt_cols {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H)
    {C : H →L[ℝ] H →L[ℝ] ℝ} {R : H →L[ℝ] H} (hR : IsSqrtOfForm R C)
    (hs : Summable fun k => ‖R (e k)‖ ^ 2) : hsCovForm (fun k => R (e k)) = C := by
  refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
  rw [hsCovForm_apply hs]
  have h := e.hasSum_inner_mul_inner (R x) (R y)
  rw [hR.sq] at h
  rw [← h.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [hR.symm (e k) x, hR.symm (e k) y, real_inner_comm (R x) (e k)]

theorem bures2_nonneg {C D : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C)
    (hD : IsTraceClassCov D) : 0 ≤ Uniform.bures2 C D := by
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have hR := Uniform.RelCov.formSqrt_spec hC
  have hSb := Uniform.RelCov.formSqrt_spec hD
  set R := Uniform.formSqrt C
  set Sb := Uniform.formSqrt D
  have hΦs : Summable fun k => ‖R (e k)‖ ^ 2 := Uniform.RelCov.summable_sqrt_diag e hR hC
  have hCΦ : hsCovForm (fun k => R (e k)) = C := hsCovForm_sqrt_cols e hR hΦs
  let ℱ0 : Filtration ℝ (inferInstance : MeasurableSpace PUnit.{1}) :=
    ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  obtain ⟨S, ψ, hSsq, -, -, hψo, hψe, -, -⟩ := exists_polar_family (ℱ := ℱ0) e
    (fun (_ : ℝ) (_ : PUnit.{1}) k => Sb (R (e k))) (fun k => by
      intro i
      exact measurable_const)
    (fun _ _ => summable_norm_sq_comp (Sb := Sb) hΦs)
  have h := sum_norm_ZVec_eq_bures2 (e := e) (Sb := Sb) (Φ := fun k => R (e k))
    (ψ := fun j => ψ j 0 PUnit.unit) hD hSb hΦs (hSsq 0 PUnit.unit)
    (fun i j => hψo 0 PUnit.unit i j) (fun x a => hψe x 0 PUnit.unit a)
  rw [hCΦ] at h
  exact h.nonneg fun a => sq_nonneg _

omit [BorelSpace H] [SecondCountableTopology H] in
lemma form_eq_zero_of_subsingleton [Subsingleton H] (C : H →L[ℝ] H →L[ℝ] ℝ) : C = 0 :=
  ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => by
    rw [Subsingleton.elim x 0]; simp

section MeasB

variable {ι : Type*} [Countable ι] {α : Type*} {mα : MeasurableSpace α}

theorem exists_opMeas_sqrt (e : HilbertBasis ι ℝ H) (C : α → H →L[ℝ] H →L[ℝ] ℝ)
    (hC : ∀ a, IsTraceClassCov (C a)) (hm : ∀ x y, Measurable fun a => C a x y) :
    ∃ S : α → H →L[ℝ] H, (∀ a, IsSqrtOfForm (S a) (C a)) ∧ OpMeas S := by
  classical
  have hAp : ∀ a, IsPSDOp (HilbertCLTAux.formOp (C a)) := fun a => formOp_isPSD' (hC a)
  have hcpos : ∀ a, 0 < trBound e (C a) := fun a => trBound_pos e (hC a)
  have hAc : ∀ a x, inner ℝ (HilbertCLTAux.formOp (C a) x) x ≤ trBound e (C a) * ‖x‖ ^ 2 :=
    fun a x => by rw [HilbertCLTAux.inner_formOp]; exact le_trBound e (hC a) x
  refine ⟨fun a => sqrtOp (trBound e (C a)) (HilbertCLTAux.formOp (C a)), fun a => ?_, ?_⟩
  · have hspec := sqrtOp_spec (hAp a) (hcpos a) (hAc a)
    refine ⟨hspec.1.symm, hspec.1.nonneg, fun x y => ?_⟩
    rw [hspec.1.symm x (sqrtOp (trBound e (C a)) (HilbertCLTAux.formOp (C a)) y)]
    have : sqrtOp (trBound e (C a)) (HilbertCLTAux.formOp (C a))
        (sqrtOp (trBound e (C a)) (HilbertCLTAux.formOp (C a)) y) =
        HilbertCLTAux.formOp (C a) y := by
      have := congrArg (fun T : H →L[ℝ] H => T y) hspec.2
      simpa using this
    rw [this, real_inner_comm, HilbertCLTAux.inner_formOp, (hC a).symm]
  · have hAm : OpMeas (fun a => HilbertCLTAux.formOp (C a)) := by
      intro x
      refine measurable_of_inner_basis e (fun j => ?_)
      have : (fun a => inner ℝ (e j) (HilbertCLTAux.formOp (C a) x)) = fun a => C a x (e j) := by
        funext a; rw [real_inner_comm]; simp [HilbertCLTAux.inner_formOp]
      rw [this]
      exact hm x (e j)
    have hcm : Measurable fun a => trBound e (C a) :=
      measurable_const.add (Measurable.tsum fun j => hm (e j) (e j))
    exact OpMeas.sqrtOp hAm hcm hAp hcpos hAc

theorem measurable_bures2 (e : HilbertBasis ι ℝ H) {C D : α → H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ a, IsTraceClassCov (C a)) (hD : ∀ a, IsTraceClassCov (D a))
    (hmC : ∀ x y, Measurable fun a => C a x y) (hmD : ∀ x y, Measurable fun a => D a x y) :
    Measurable fun a => Uniform.bures2 (C a) (D a) := by
  obtain ⟨S₁, h1, m1⟩ := exists_opMeas_sqrt e C hC hmC
  obtain ⟨S₂, h2, m2⟩ := exists_opMeas_sqrt e D hD hmD
  have e1 : ∀ a, Uniform.formSqrt (C a) = S₁ a := fun a =>
    sqrt_unique (Uniform.RelCov.formSqrt_spec (hC a)) (h1 a)
  have e2 : ∀ a, Uniform.formSqrt (D a) = S₂ a := fun a =>
    sqrt_unique (Uniform.RelCov.formSqrt_spec (hD a)) (h2 a)
  have : (fun a => Uniform.bures2 (C a) (D a)) = fun a => traceNormForm (C a) + traceNormForm (D a) -
      2 * traceNormForm ((innerSL ℝ).comp ((S₂ a).comp (S₁ a))) := by
    funext a; simp only [Uniform.bures2, e1, e2]
  rw [this]
  refine ((measurable_traceNormForm C hmC).add (measurable_traceNormForm D hmD)).sub
    (measurable_const.mul (measurable_traceNormForm _ ?_))
  intro x y
  have : Measurable fun a => inner ℝ (S₂ a (S₁ a x)) y :=
    (m2.apply (m1 x)).inner measurable_const
  simpa using this

variable (e : HilbertBasis ι ℝ H)

/-- The regularisation of a form: the form with the same matrix entries along `e` if the matrix is
a trace-class covariance matrix, and `0` otherwise.  It is trace class, and equal to `C` if `C` is. -/
def regForm (C : H →L[ℝ] H →L[ℝ] ℝ) : H →L[ℝ] H →L[ℝ] ℝ := matForm e (fun i j => C (e i) (e j))

lemma regForm_tc (C : H →L[ℝ] H →L[ℝ] ℝ) : IsTraceClassCov (regForm e C) := by
  unfold regForm
  by_cases hg : GoodMat (fun i j => C (e i) (e j))
  · exact isTraceClassCov_matForm hg
  · rw [matForm_of_not hg]; exact isTraceClassCov_zero

lemma regForm_eq {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) : regForm e C = C :=
  matForm_matrix e hC

lemma measurable_regForm {C : α → H →L[ℝ] H →L[ℝ] ℝ} (hm : ∀ x y, Measurable fun a => C a x y)
    (x y : H) : Measurable fun a => regForm e (C a) x y :=
  measurable_matForm_apply e (a := fun i j a => C a (e i) (e j)) (fun i j => hm _ _) x y

end MeasB

section Fallback

open Classical

/-- A fixed unit vector (or `0` if `H` is trivial). -/
def unitVec (H : Type*) [NormedAddCommGroup H] : H := if h : ∃ v : H, ‖v‖ = 1 then h.choose else 0

/-- The rank-one form of trace norm `c` (for `c ≥ 0`). -/
def fbForm (c : ℝ) : H →L[ℝ] H →L[ℝ] ℝ := hsCovForm (fun _ : Unit => Real.sqrt c • unitVec H)

lemma fbForm_apply (c : ℝ) (x y : H) :
    fbForm c x y = (Real.sqrt c) ^ 2 * (inner ℝ (unitVec H) x * inner ℝ (unitVec H) y) := by
  unfold fbForm
  rw [hsCovForm_apply (Summable.of_finite)]
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, real_inner_smul_left]
  ring

lemma fbForm_tc (c : ℝ) : IsTraceClassCov (fbForm (H := H) c) :=
  isTraceClassCov_hsCovForm (Summable.of_finite)

lemma measurable_fbForm (x y : H) : Measurable fun c : ℝ => fbForm c x y := by
  simp_rw [fbForm_apply]
  exact (measurable_id.sqrt.pow_const 2).mul measurable_const

lemma traceNormForm_fbForm {c : ℝ} (hc : 0 ≤ c) (h : c = 0 ∨ Nontrivial H) :
    traceNormForm (fbForm c : H →L[ℝ] H →L[ℝ] ℝ) = c := by
  unfold fbForm
  rw [traceNormForm_hsCovForm_eq (Summable.of_finite)]
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  rcases h with h | h
  · subst h; simp
  · haveI := h
    have hex : ∃ v : H, ‖v‖ = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)
    have hu : ‖unitVec H‖ = 1 := by
      unfold unitVec
      rw [dite_cond_eq_true (eq_true hex)]
      exact hex.choose_spec
    simp [tsum_fintype, norm_smul, hu, mul_pow, sq_abs, hsq]

end Fallback

end Bures

end HRS.Uniform.Q07c
