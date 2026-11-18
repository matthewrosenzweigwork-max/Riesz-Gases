import HRS.MS.QsfAsm6

/-!
# S4.5 packet B5 (assembly), part 7: the finite-dimensional data `R_n, T_n` and their bounds
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s45_phi_facts {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : HRS.Whole.IsSummableFeatureFamily J φ) :
    (∀ i, ContDiff ℝ 1 (φ i)) ∧ (∀ i x, |φ i x| ≤ cbNorm J (φ i)) ∧
      (∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ cbNorm J (φ i)) :=
  ⟨fun i => (hφ.1 i).1.of_le (by exact_mod_cast hJ), fun i x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 i) x
    rwa [Real.norm_eq_abs] at this, fun i x => s45_cb_deriv_le hJ (hφ.1 i) x⟩

theorem s45_nu_prob {s a β : ℝ} (hN : 2 ≤ N) (hP : IsProbabilityMeasure (s45_P d s a β N)) :
    IsProbabilityMeasure (s45_nu d s a β N) := by
  have : s45_nu d s a β N = (s45_P d s a β N).map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
    unfold s45_nu firstMarginal; rw [dif_pos (by omega)]
  rw [this]
  constructor
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
  simp

theorem s45_inner_grad_le {χ ψ : Euc d → ℝ} {B D : ℝ} (h1 : ∀ x, ‖gradient χ x‖ ≤ B)
    (hD : ∀ x, ‖fderiv ℝ ψ x‖ ≤ D) (x : Euc d) : |⟪gradient χ x, gradient ψ x⟫| ≤ B * D := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [s45_norm_gradient ψ]
  exact mul_le_mul (h1 x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))

/-- The remainder vector `R_n`. -/
def s45_Rvec (d : ℕ) (s a β : ℝ) (N n : ℕ) (χ : ℕ → Euc d → ℝ) {γ : Type*}
    (w : EucConfig d N × γ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (s45_nu d s a β N) (s45_P d s a β N)
    (commutatorKernel d s (gradient (χ i))) w.1) • EuclideanSpace.single i (1 : ℝ)

/-- The matrix `T_n`. -/
def s45_Tmat (d : ℕ) (β : ℝ) (N n : ℕ) (φ χ : ℕ → Euc d → ℝ) {γ : Type*}
    (w : EucConfig d N × γ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => β⁻¹ * pair (empirical w.1) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)

section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β Cs C c BU KR KT : ℝ}
  (ha : 0 < a) (hβ : 0 < β) (hsu : S45Setup d s a β Cs C c BU KR KT) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S45Feat d s a β (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {γ : Measure SeqL2} [IsProbabilityMeasure γ]

include hd hs0 hsd hsu hN hfeat

theorem s45_Rvec_integrable (n : ℕ) :
    Integrable (s45_Rvec d s a β N n χ : EucConfig d N × SeqL2 → EuclideanSpace ℝ (Fin n))
      ((s45_P d s a β N).prod γ) := by
  haveI : IsProbabilityMeasure (s45_P d s a β N) := (hsu.hS N hN).prob
  unfold s45_Rvec
  refine integrable_finsetSum _ fun i _ => ?_
  have h1 := s45_Rp_integrable hd hs0 hsd hsu.hT hN (hsu.hS N hN) (hfeat i).smooth (hfeat i).B2
  exact (s45_integrable_fst (γ := γ) (h1.const_mul (Real.sqrt N))).smul_const _

theorem s45_Rvec_bound (n : ℕ) :
    ∫ w, ‖(s45_Rvec d s a β N n χ w : EuclideanSpace ℝ (Fin n))‖ ∂((s45_P d s a β N).prod γ) ≤
      KR * Cc * (∑ i : Fin n, cbNorm J (φ i)) * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (s45_P d s a β N) := (hsu.hS N hN).prob
  set P := s45_P d s a β N with hPdef
  set δ := Real.sqrt (HRS.deltaN d s N) with hδ
  set rr : Fin n → EucConfig d N → ℝ := fun i X => s45_Rp (thermalMeasure d s a β)
    (s45_nu d s a β N) P (commutatorKernel d s (gradient (χ i))) X with hrr
  have hri : ∀ i, Integrable (rr i) P := fun i =>
    s45_Rp_integrable hd hs0 hsd hsu.hT hN (hsu.hS N hN) (hfeat i).smooth (hfeat i).B2
  have hpt : ∀ w : EucConfig d N × SeqL2, ‖s45_Rvec d s a β N n χ w‖ ≤
      ∑ i : Fin n, |Real.sqrt N * rr i w.1| := by
    intro w
    unfold s45_Rvec
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, EuclideanSpace.norm_single]
    simp
    exact le_rfl
  have hint : ∀ i : Fin n, Integrable (fun w : EucConfig d N × SeqL2 => |Real.sqrt N * rr i w.1|)
      (P.prod γ) := fun i =>
    (s45_integrable_fst (γ := γ) ((hri i).const_mul (Real.sqrt N))).abs
  calc ∫ w, ‖s45_Rvec d s a β N n χ w‖ ∂(P.prod γ)
      ≤ ∫ w, ∑ i : Fin n, |Real.sqrt N * rr i w.1| ∂(P.prod γ) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (integrable_finsetSum _ fun i _ => hint i) (Filter.Eventually.of_forall hpt)
    _ = ∑ i : Fin n, ∫ w, |Real.sqrt N * rr i w.1| ∂(P.prod γ) :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i : Fin n, Real.sqrt N * ∫ X, |rr i X| ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [s45_integral_fst (γ := γ) (g := fun X => |Real.sqrt N * rr i X|)
          ((hri i).const_mul _).abs.aestronglyMeasurable]
        simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))]
        rw [integral_const_mul]
    _ ≤ ∑ i : Fin n, KR * (Cc * cbNorm J (φ i)) * δ := Finset.sum_le_sum fun i _ =>
        hsu.hR N hN (hfeat i).smooth (hfeat i).B2
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end Ctx

end S45

end
