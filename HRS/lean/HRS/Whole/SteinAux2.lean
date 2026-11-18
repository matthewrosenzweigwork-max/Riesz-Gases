import HRS.Whole.SteinAux1

/-!
# Packet STEIN, auxiliary file 2: extension of the Stein-type identity

The identity `SId` (a copy of `HRS.Whole.SteinIdentity`, which is defined later) holds for every
`C²` test function with bounded `f`, `Df`, `D²f`: mollify and pass to the limit.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Same body as `HRS.Whole.SteinIdentity`. -/
def SId {n : ℕ} (X R : Ω → EuclideanSpace ℝ (Fin n))
    (T : Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∃ Cf, ∀ x, |f x| ≤ Cf) →
    (∃ Cf, ∀ x, ‖fderiv ℝ f x‖ ≤ Cf) → ∀ i : Fin n,
      ∫ w, X w i * f (X w) ∂P =
        ∫ w, R w i * f (X w) ∂P +
          ∑ j : Fin n, ∫ w, T w i j * fderiv ℝ f (X w) (EuclideanSpace.single j 1) ∂P

lemma abs_entry_le_traceNorm {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) :
    |Q a b| ≤ traceNormMatrix Q := by
  classical
  have h := HRS.LindebergAux.trace_dual
    (Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0) Q 1 zero_le_one
    (fun u v => by
      have e : u ⬝ᵥ ((Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0).mulVec v) =
          u a * v b := by
        simp [dotProduct, Matrix.mulVec, ite_and]
      rw [e, abs_mul]
      have s1 : |u a| ≤ Real.sqrt (u ⬝ᵥ u) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by
          simp only [dotProduct]
          calc u a ^ 2 = u a * u a := sq _
            _ ≤ _ := Finset.single_le_sum (f := fun i => u i * u i)
              (fun i _ => mul_self_nonneg _) (Finset.mem_univ a))
      have s2 : |v b| ≤ Real.sqrt (v ⬝ᵥ v) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by
          simp only [dotProduct]
          calc v b ^ 2 = v b * v b := sq _
            _ ≤ _ := Finset.single_le_sum (f := fun i => v i * v i)
              (fun i _ => mul_self_nonneg _) (Finset.mem_univ b))
      calc |u a| * |v b| ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
            mul_le_mul s1 s2 (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = 1 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring)
  have e : ∑ i, ∑ j, (Matrix.of fun i j => if i = a ∧ j = b then (1 : ℝ) else 0) i j * Q i j
      = Q a b := by
    simp [ite_and]
  rw [e, one_mul] at h
  exact h

lemma integrable_coord {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)} (hX : Integrable X P) (i : Fin n) :
    Integrable (fun w => X w i) P :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integrable_comp hX

lemma integrable_entry {n : ℕ} {T : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (i j : Fin n) :
    Integrable (fun w => T w i j) P :=
  hT.mono' (hTm i j) (Eventually.of_forall fun w => by
    rw [Real.norm_eq_abs]; exact abs_entry_le_traceNorm _ _ _)

lemma norm_single_one {n : ℕ} (j : Fin n) :
    ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simp

lemma sid_ext {n : ℕ} (X R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SId P X R T)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    (Cf : ℝ) (hCf : ∀ x, |f x| ≤ Cf) (C1 : ℝ) (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (C2 : ℝ) (hC2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C2) (i : Fin n) :
    ∫ w, X w i * f (X w) ∂P =
      ∫ w, R w i * f (X w) ∂P +
        ∑ j : Fin n, ∫ w, T w i j * fderiv ℝ f (X w) (EuclideanSpace.single j 1) ∂P := by
  have hfc : Continuous f := hf.continuous
  have hDi : ∀ j, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ (if j = 1 then C1 else C2) := by
    intro j h1 hj x
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · simpa [norm_iteratedFDeriv_one] using hC1 x
    · simpa using hC2 x
  have hmd := fun k => mol_deriv (bumpSeq n k) f 2 (by norm_num) hf Cf hCf
    (fun j => if j = 1 then C1 else C2) hDi
  have hsm : ∀ k, ContDiff ℝ ∞ (mol ((bumpSeq n k).normed volume) f) := by
    intro k
    rw [contDiff_infty]
    intro N
    exact (mol_smooth (bumpSeq n k) f hfc Cf hCf N).1
  have hbd : ∀ k x, |mol ((bumpSeq n k).normed volume) f x| ≤ Cf := fun k x =>
    mol_abs_le (bumpSeq n k) f Cf hCf x
  have hd1 : ∀ k x, ‖fderiv ℝ (mol ((bumpSeq n k).normed volume) f) x‖ ≤ C1 := by
    intro k x
    have := (hmd k).2.2 1 le_rfl (by norm_num) x
    simpa [norm_iteratedFDeriv_one] using this
  have hidk := fun k => hid _ (hsm k) ⟨Cf, hbd k⟩ ⟨C1, hd1 k⟩ i
  have hlim0 : ∀ x, Tendsto (fun k => mol ((bumpSeq n k).normed volume) f x) atTop (𝓝 (f x)) :=
    fun x => mol_tendsto (bumpSeq n) (bumpSeq_rOut_tendsto n) f hfc x
  have hlim1 : ∀ x (j : Fin n), Tendsto
      (fun k => fderiv ℝ (mol ((bumpSeq n k).normed volume) f) x (EuclideanSpace.single j 1))
      atTop (𝓝 (fderiv ℝ f x (EuclideanSpace.single j 1))) := by
    intro x j
    have hc : Continuous (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have := mol_tendsto (bumpSeq n) (bumpSeq_rOut_tendsto n)
      (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) hc x
    refine this.congr fun k => ?_
    rw [mol_fderiv_apply (bumpSeq n k) f (hf.of_le (by norm_num)) Cf hCf C1 hC1]
    rfl
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hXi := integrable_coord P hX i
  have hRi := integrable_coord P hR i
  have L1 : Tendsto (fun k => ∫ w, X w i * mol ((bumpSeq n k).normed volume) f (X w) ∂P) atTop
      (𝓝 (∫ w, X w i * f (X w) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => |X w i| * Cf) (fun k => ?_)
      (hXi.abs.mul_const _) (fun k => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => (hlim0 (X w)).const_mul _)
    · exact hXi.aestronglyMeasurable.mul
        (((hsm k).continuous).comp_aestronglyMeasurable hXm)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbd k _) (abs_nonneg _)
  have L2 : Tendsto (fun k => ∫ w, R w i * mol ((bumpSeq n k).normed volume) f (X w) ∂P) atTop
      (𝓝 (∫ w, R w i * f (X w) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => |R w i| * Cf) (fun k => ?_)
      (hRi.abs.mul_const _) (fun k => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => (hlim0 (X w)).const_mul _)
    · exact hRi.aestronglyMeasurable.mul
        (((hsm k).continuous).comp_aestronglyMeasurable hXm)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbd k _) (abs_nonneg _)
  have L3 : ∀ j : Fin n, Tendsto (fun k => ∫ w, T w i j *
      fderiv ℝ (mol ((bumpSeq n k).normed volume) f) (X w) (EuclideanSpace.single j 1) ∂P) atTop
      (𝓝 (∫ w, T w i j * fderiv ℝ f (X w) (EuclideanSpace.single j 1) ∂P)) := by
    intro j
    have hTij := integrable_entry P hTm hT i j
    refine tendsto_integral_of_dominated_convergence (fun w => |T w i j| * C1) (fun k => ?_)
      (hTij.abs.mul_const _) (fun k => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => (hlim1 (X w) j).const_mul _)
    · exact (hTm i j).mul
        ((((hsm k).continuous_fderiv (by simp)).clm_apply continuous_const).comp_aestronglyMeasurable hXm)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |fderiv ℝ (mol ((bumpSeq n k).normed volume) f) (X w) (EuclideanSpace.single j 1)|
          ≤ ‖fderiv ℝ (mol ((bumpSeq n k).normed volume) f) (X w)‖ * ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ := by
            rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ C1 * 1 := by
            rw [norm_single_one]
            exact mul_le_mul_of_nonneg_right (hd1 k _) zero_le_one
        _ = C1 := mul_one _
  have L4 := L2.add (tendsto_finset_sum Finset.univ fun j _ => L3 j)
  refine tendsto_nhds_unique L1 ?_
  simp_rw [hidk]
  exact L4

end HRS.Whole.Stein
