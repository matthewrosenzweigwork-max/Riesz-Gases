import Mathlib

/-!
# S8.2 A04 (S82W), part 1: calculus helpers (jets of products and compositions, zero extension)
All statements are on a real normed space `E`; no project dependencies.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.S82W

section jets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma w_j1 (f : E → ℝ) (x : E) : ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := norm_iteratedFDeriv_one f

lemma w_j2 (f : E → ℝ) (x : E) : ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1)
  rw [norm_iteratedFDeriv_one] at this
  exact this.symm

/-- a function that is smooth on an open set and vanishes off a closed subset of it is smooth -/
lemma w_contDiff_of_tsupport {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E → V} {U : Set E}
    (hU : IsOpen U) {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f U) (hs : tsupport f ⊆ U) : ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hx' : x ∉ tsupport f := fun h => hx (hs h)
    have : f =ᶠ[𝓝 x] fun _ => (0 : V) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (contDiffAt_const).congr_of_eventuallyEq this

/-- Leibniz bounds for a product of a function that is `C²` on an open set with another one. -/
lemma w_prod_jets {U : Set E} (hU : IsOpen U) {G F : E → ℝ} (hG : ContDiffOn ℝ 2 G U)
    (hF : ContDiffOn ℝ 2 F U) {x : E} (hx : x ∈ U) :
    ‖fderiv ℝ (fun y => G y * F y) x‖ ≤ |G x| * ‖fderiv ℝ F x‖ + ‖fderiv ℝ G x‖ * |F x| ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => G y * F y)) x‖ ≤ |G x| * ‖fderiv ℝ (fderiv ℝ F) x‖ +
      2 * ‖fderiv ℝ G x‖ * ‖fderiv ℝ F x‖ + ‖fderiv ℝ (fderiv ℝ G) x‖ * |F x| := by
  have h1 := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hG hF hU.uniqueDiffOn hx (n := 1) (by norm_num)
  have h2 := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hG hF hU.uniqueDiffOn hx (n := 2) le_rfl
  have e : ∀ (k : ℕ) (f : E → ℝ), iteratedFDerivWithin ℝ k f U x = iteratedFDeriv ℝ k f x :=
    fun k f => iteratedFDerivWithin_of_isOpen k hU hx
  simp only [e] at h1 h2
  simp [Finset.sum_range_succ, Nat.choose, norm_iteratedFDeriv_zero, w_j1, w_j2] at h1 h2
  constructor
  · linarith
  · linarith

/-- Chain rule bounds for `c ∘ u` with `c : ℝ → ℝ` and `u : E → ℝ`. -/
lemma w_comp_jets {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    ‖fderiv ℝ (fun y => c (u y)) x‖ ≤ |deriv c (u x)| * ‖fderiv ℝ u x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => c (u y))) x‖ ≤
      |deriv (deriv c) (u x)| * ‖fderiv ℝ u x‖ ^ 2 + |deriv c (u x)| * ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  have hcd : ∀ t, HasDerivAt c (deriv c t) t := fun t => (hc.differentiable (by norm_num) t).hasDerivAt
  have hc1 : ContDiff ℝ 1 (deriv c) := by
    have : ContDiff ℝ (1 + 1) c := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
    exact (contDiff_succ_iff_deriv.1 this).2.2
  have hc'd : ∀ t, HasDerivAt (deriv c) (deriv (deriv c) t) t := fun t =>
    (hc1.differentiable one_ne_zero t).hasDerivAt
  have hu1 : ∀ y, HasFDerivAt u (fderiv ℝ u y) y := fun y => (hu.differentiable (by norm_num) y).hasFDerivAt
  have hfd : fderiv ℝ (fun y => c (u y)) = fun y => deriv c (u y) • fderiv ℝ u y := by
    funext y
    exact ((hcd (u y)).comp_hasFDerivAt y (hu1 y)).fderiv
  have hu2 : Differentiable ℝ (fderiv ℝ u) := by
    have : ContDiff ℝ (1 + 1) u := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
    exact (contDiff_succ_iff_fderiv.1 this).2.2.differentiable one_ne_zero
  constructor
  · rw [hfd, norm_smul, Real.norm_eq_abs]
  · have hA : HasFDerivAt (fun y => deriv c (u y)) (deriv (deriv c) (u x) • fderiv ℝ u x) x :=
      (hc'd (u x)).comp_hasFDerivAt x (hu1 x)
    have hB : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x := (hu2 x).hasFDerivAt
    have hAB : HasFDerivAt (fun y => deriv c (u y) • fderiv ℝ u y)
        (deriv c (u x) • fderiv ℝ (fderiv ℝ u) x +
          (deriv (deriv c) (u x) • fderiv ℝ u x).smulRight (fderiv ℝ u x)) x := hA.smul hB
    rw [hfd, hAB.fderiv]
    refine le_trans (norm_add_le (deriv c (u x) • fderiv ℝ (fderiv ℝ u) x)
      ((deriv (deriv c) (u x) • fderiv ℝ u x).smulRight (fderiv ℝ u x))) ?_
    have e1 : ‖deriv c (u x) • fderiv ℝ (fderiv ℝ u) x‖ ≤ |deriv c (u x)| * ‖fderiv ℝ (fderiv ℝ u) x‖ := by
      have := ContinuousLinearMap.opNorm_smul_le (deriv c (u x)) (fderiv ℝ (fderiv ℝ u) x)
      rwa [Real.norm_eq_abs] at this
    have e2 : ‖(deriv (deriv c) (u x) • fderiv ℝ u x).smulRight (fderiv ℝ u x)‖ ≤
        |deriv (deriv c) (u x)| * ‖fderiv ℝ u x‖ ^ 2 := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      have := norm_smul_le (deriv (deriv c) (u x)) (fderiv ℝ u x)
      rw [Real.norm_eq_abs] at this
      nlinarith [norm_nonneg (fderiv ℝ u x)]
    linarith

lemma w_prod_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (φ : ι → E → ℝ)
    (hφ : ∀ a, ContDiff ℝ 2 (φ a)) (h01 : ∀ a y, 0 ≤ φ a y ∧ φ a y ≤ 1) (b1 b2 : ι → ℝ) (x : E)
    (hb1 : ∀ a ∈ s, ‖fderiv ℝ (φ a) x‖ ≤ b1 a) (hb2 : ∀ a ∈ s, ‖fderiv ℝ (fderiv ℝ (φ a)) x‖ ≤ b2 a) :
    ‖fderiv ℝ (fun y => ∏ a ∈ s, φ a y) x‖ ≤ ∑ a ∈ s, b1 a ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => ∏ a ∈ s, φ a y)) x‖ ≤ ∑ a ∈ s, b2 a + (∑ a ∈ s, b1 a) ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, fderiv_fun_const, Pi.zero_apply, norm_zero]
    have h0 : fderiv ℝ (0 : E → (E →L[ℝ] ℝ)) = 0 := by
      funext y; exact fderiv_const_apply _
    rw [h0, Pi.zero_apply, ContinuousLinearMap.opNorm_zero]
    norm_num
  | insert a s ha ih =>
    have ih' := ih (fun c hc => hb1 c (Finset.mem_insert_of_mem hc)) (fun c hc => hb2 c (Finset.mem_insert_of_mem hc))
    have hP : ContDiff ℝ 2 (fun y => ∏ c ∈ s, φ c y) := contDiff_prod (fun c _ => hφ c)
    have hP01 : ∀ y, 0 ≤ ∏ c ∈ s, φ c y ∧ ∏ c ∈ s, φ c y ≤ 1 := fun y =>
      ⟨Finset.prod_nonneg fun c _ => (h01 c y).1, Finset.prod_le_one₀ (fun c _ => (h01 c y).1) fun c _ => (h01 c y).2⟩
    have hfun : (fun y => ∏ c ∈ insert a s, φ c y) = fun y => φ a y * ∏ c ∈ s, φ c y := by
      funext y; rw [Finset.prod_insert ha]
    have hpj := w_prod_jets (U := Set.univ) isOpen_univ (G := φ a) (F := fun y => ∏ c ∈ s, φ c y)
      (hφ a).contDiffOn hP.contDiffOn (Set.mem_univ x)
    have hb1a := hb1 a (Finset.mem_insert_self a s)
    have hb2a := hb2 a (Finset.mem_insert_self a s)
    have hb1n : ∀ c ∈ s, 0 ≤ b1 c := fun c hc =>
      (norm_nonneg _).trans (hb1 c (Finset.mem_insert_of_mem hc))
    have hB1 : 0 ≤ ∑ c ∈ s, b1 c := Finset.sum_nonneg hb1n
    have hb1a0 : 0 ≤ b1 a := (norm_nonneg _).trans hb1a
    rw [hfun]
    simp only [Finset.sum_insert ha]
    obtain ⟨i1, i2⟩ := ih'
    obtain ⟨p1, p2⟩ := hpj
    have ga : |φ a x| ≤ 1 := by rw [abs_of_nonneg (h01 a x).1]; exact (h01 a x).2
    have gP : |∏ c ∈ s, φ c x| ≤ 1 := by rw [abs_of_nonneg (hP01 x).1]; exact (hP01 x).2
    have n1 := norm_nonneg (fderiv ℝ (φ a) x)
    have n2 := norm_nonneg (fderiv ℝ (fun y => ∏ c ∈ s, φ c y) x)
    have n3 := norm_nonneg (fderiv ℝ (fderiv ℝ (φ a)) x)
    have n4 := norm_nonneg (fderiv ℝ (fderiv ℝ (fun y => ∏ c ∈ s, φ c y)) x)
    constructor
    · nlinarith [mul_le_mul ga i1 n2 zero_le_one, mul_le_mul hb1a gP (abs_nonneg _) hb1a0]
    · nlinarith [mul_le_mul ga i2 n4 zero_le_one, mul_le_mul hb2a gP (abs_nonneg _) (n3.trans hb2a),
        mul_le_mul hb1a i1 n2 hb1a0, mul_le_mul gP hb2a n3 zero_le_one]

end jets

end HRS.MS.S82W
