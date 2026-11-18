import HRS.MP.SelfSimP5Spec

/-!
# MPP5A (4): the truncated chamber potential `ss5_trunc_props`

`HRS.MP.SelfSimP5Impl.ss5_trunc_props_proof` has the statement of `HRS.MP.SelfSimP5.ss5_trunc_props`.
Scalar calculus of `φ_ε` (`ss5t_`), explicit gradients of pair-sum potentials, and the four properties.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Scalar calculus -/

/-- `φ_ε'`. -/
def ss5t_d1 (ε g : ℝ) : ℝ := if ε ≤ g then -(g⁻¹) else -(ε⁻¹) + (g - ε) / ε ^ 2

/-- `φ_ε''`. -/
def ss5t_d2 (ε g : ℝ) : ℝ := if ε ≤ g then (g ^ 2)⁻¹ else (ε ^ 2)⁻¹

theorem ss5t_glue {F A B A' B' : ℝ → ℝ} {a : ℝ} (hF : ∀ x, F x = if a ≤ x then A x else B x)
    (hA : ∀ x, a ≤ x → HasDerivAt A (A' x) x) (hB : ∀ x, x ≤ a → HasDerivAt B (B' x) x)
    (h0 : A a = B a) (h1 : A' a = B' a) (x : ℝ) :
    HasDerivAt F (if a ≤ x then A' x else B' x) x := by
  rcases lt_trichotomy x a with hx | hx | hx
  · have hev : F =ᶠ[𝓝 x] B := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [hF, if_neg (not_le.2 hy)]
    rw [if_neg (not_le.2 hx)]
    exact (hB x hx.le).congr_of_eventuallyEq hev
  · subst hx
    rw [if_pos le_rfl]
    have hU : HasDerivWithinAt F (A' x) (Ici x) x :=
      (hA x le_rfl).hasDerivWithinAt.congr (fun y (hy : x ≤ y) => by rw [hF, if_pos hy])
        (by rw [hF, if_pos le_rfl])
    have hL : HasDerivWithinAt F (A' x) (Iic x) x := by
      rw [h1]
      refine (hB x le_rfl).hasDerivWithinAt.congr (fun y hy => ?_) (by rw [hF, if_pos le_rfl, h0])
      rcases eq_or_lt_of_le (show y ≤ x from hy) with h | h
      · rw [h, hF, if_pos le_rfl, h0]
      · rw [hF, if_neg (not_le.2 h)]
    have := hL.union hU
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · have hev : F =ᶠ[𝓝 x] A := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hF, if_pos (le_of_lt hy)]
    rw [if_pos hx.le]
    exact (hA x hx.le).congr_of_eventuallyEq hev

theorem ss5t_hasDerivAt_phi {ε : ℝ} (hε : 0 < ε) (g : ℝ) :
    HasDerivAt (ss5_phiTr ε) (ss5t_d1 ε g) g := by
  refine ss5t_glue (a := ε)
    (A := fun g => -Real.log g) (B := fun g => -Real.log ε - (g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2))
    (A' := fun g => -(g⁻¹)) (B' := fun g => -(ε⁻¹) + (g - ε) / ε ^ 2)
    (fun x => rfl) ?_ ?_ ?_ ?_ g
  · intro x hx
    exact (Real.hasDerivAt_log (lt_of_lt_of_le hε hx).ne').neg
  · intro x _
    have h1 : HasDerivAt (fun g : ℝ => g - ε) 1 x := (hasDerivAt_id x).sub_const ε
    have h2 := (h1.div_const ε)
    have h3 := ((h1.pow 2).div_const (2 * ε ^ 2))
    have h4 := ((h2.const_sub (-Real.log ε)).add h3)
    convert h4 using 1
    field_simp
    ring
  · simp
  · simp

theorem ss5t_hasDerivAt_d1 {ε : ℝ} (hε : 0 < ε) (g : ℝ) :
    HasDerivAt (ss5t_d1 ε) (ss5t_d2 ε g) g := by
  refine ss5t_glue (a := ε)
    (A := fun g => -(g⁻¹)) (B := fun g => -(ε⁻¹) + (g - ε) / ε ^ 2)
    (A' := fun g => (g ^ 2)⁻¹) (B' := fun _ => (ε ^ 2)⁻¹)
    (fun x => rfl) ?_ ?_ ?_ ?_ g
  · intro x hx
    have := (hasDerivAt_inv (𝕜 := ℝ) (lt_of_lt_of_le hε hx).ne').fun_neg
    simpa using this
  · intro x _
    have h1 : HasDerivAt (fun g : ℝ => g - ε) 1 x := (hasDerivAt_id x).sub_const ε
    have h4 := (h1.div_const (ε ^ 2)).const_add (-(ε⁻¹))
    simpa using h4
  · simp
  · simp

theorem ss5t_d2_nonneg (ε g : ℝ) : 0 ≤ ss5t_d2 ε g := by
  unfold ss5t_d2; split_ifs <;> positivity

theorem ss5t_d2_le {ε : ℝ} (hε : 0 < ε) (g : ℝ) : ss5t_d2 ε g ≤ (ε ^ 2)⁻¹ := by
  unfold ss5t_d2
  split_ifs with h
  · exact inv_anti₀ (by positivity) (by nlinarith)
  · exact le_rfl

theorem ss5t_continuous_d2 {ε : ℝ} (hε : 0 < ε) : Continuous (ss5t_d2 ε) := by
  have := continuous_if_le (f := fun _ : ℝ => ε) (g := fun x : ℝ => x)
    (f' := fun x : ℝ => (x ^ 2)⁻¹) (g' := fun _ : ℝ => (ε ^ 2)⁻¹) continuous_const continuous_id
    ((continuousOn_id.pow 2).inv₀ (fun x (hx : ε ≤ x) => pow_ne_zero 2 (lt_of_lt_of_le hε hx).ne')) continuousOn_const (fun x hx => by rw [← hx])
  exact this

theorem ss5t_deriv_phi {ε : ℝ} (hε : 0 < ε) : deriv (ss5_phiTr ε) = ss5t_d1 ε :=
  funext fun g => (ss5t_hasDerivAt_phi hε g).deriv

theorem ss5t_deriv_d1 {ε : ℝ} (hε : 0 < ε) : deriv (ss5t_d1 ε) = ss5t_d2 ε :=
  funext fun g => (ss5t_hasDerivAt_d1 hε g).deriv

theorem ss5t_contDiff_d1 {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (ss5t_d1 ε) := by
  rw [contDiff_one_iff_deriv, ss5t_deriv_d1 hε]
  exact ⟨fun g => (ss5t_hasDerivAt_d1 hε g).differentiableAt, ss5t_continuous_d2 hε⟩

theorem ss5t_contDiff_phi {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (ss5_phiTr ε) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_deriv]
  refine ⟨fun g => (ss5t_hasDerivAt_phi hε g).differentiableAt, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · rw [ss5t_deriv_phi hε]; exact ss5t_contDiff_d1 hε

theorem ss5t_d1_mono {ε : ℝ} (hε : 0 < ε) : Monotone (ss5t_d1 ε) :=
  monotone_of_deriv_nonneg (fun g => (ss5t_hasDerivAt_d1 hε g).differentiableAt)
    (fun g => by rw [ss5t_deriv_d1 hε]; exact ss5t_d2_nonneg ε g)

theorem ss5t_d1_lip {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal ((ε ^ 2)⁻¹)) (ss5t_d1 ε) := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun g => (ss5t_hasDerivAt_d1 hε g).differentiableAt) ?_
  intro g
  rw [ss5t_deriv_d1 hε]
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_of_nonneg (ss5t_d2_nonneg ε g),
    Real.coe_toNNReal _ (by positivity)]
  exact ss5t_d2_le hε g

theorem ss5t_phi_ge {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (g : ℝ) : -|g| ≤ ss5_phiTr ε g := by
  unfold ss5_phiTr
  split_ifs with h
  · have hg : 0 < g := lt_of_lt_of_le hε h
    have := Real.log_le_sub_one_of_pos hg
    rw [abs_of_pos hg]; linarith
  · have hl : 0 ≤ -Real.log ε := by
      have := Real.log_nonpos hε.le hε1; linarith
    have hs : 0 ≤ -(g - ε) / ε := div_nonneg (by linarith [not_le.1 h]) hε.le
    have : -(g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2) ≥ 0 := by
      have h2 : 0 ≤ (g - ε) ^ 2 / (2 * ε ^ 2) := by positivity
      linarith [show -(g - ε) / ε = -((g - ε) / ε) by ring]
    have : -Real.log ε - (g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2) ≥ 0 := by
      have e : -Real.log ε - (g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2) =
          -Real.log ε + (-(g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2)) := by ring
      rw [e]; linarith
    linarith [abs_nonneg g]

/-! ### Pair-sum potentials and their gradients -/

/-- The vector `e_l - e_k`. -/
def ss5t_v {N : ℕ} (k l : Fin N) : Ch5 N := EuclideanSpace.single l 1 - EuclideanSpace.single k 1

theorem ss5t_inner_v {N : ℕ} (k l : Fin N) (z : Ch5 N) :
    inner ℝ (ss5t_v k l) z = z l - z k := by
  simp [ss5t_v, inner_sub_left, EuclideanSpace.inner_single_left]

theorem ss5t_norm_v {N : ℕ} (k l : Fin N) : ‖ss5t_v k l‖ ≤ 2 := by
  unfold ss5t_v
  calc ‖(EuclideanSpace.single l 1 - EuclideanSpace.single k 1 : Ch5 N)‖
      ≤ ‖(EuclideanSpace.single l 1 : Ch5 N)‖ + ‖(EuclideanSpace.single k 1 : Ch5 N)‖ := norm_sub_le _ _
    _ = 2 := by simp; norm_num

/-- `z ↦ (1/N) ∑_{k<l} f(z_l - z_k)`. -/
def ss5t_pairSum (N : ℕ) (f : ℝ → ℝ) (z : Ch5 N) : ℝ :=
  (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N, if k < l then f (z l - z k) else 0

/-- The candidate gradient `(1/N) ∑_{k<l} f'(z_l - z_k) (e_l - e_k)`. -/
def ss5t_pairGrad (N : ℕ) (f' : ℝ → ℝ) (z : Ch5 N) : Ch5 N :=
  (1 / (N : ℝ)) • ∑ k : Fin N, ∑ l : Fin N, if k < l then f' (z l - z k) • ss5t_v k l else 0

theorem ss5t_hasGradientAt_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {α : Type*} (s : Finset α) {F : α → E → ℝ} {F' : α → E} {z : E}
    (h : ∀ i ∈ s, HasGradientAt (F i) (F' i) z) :
    HasGradientAt (fun w => ∑ i ∈ s, F i w) (∑ i ∈ s, F' i) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have := HasFDerivAt.sum (u := s) (fun i hi => (hasGradientAt_iff_hasFDerivAt.1 (h i hi)))
  rw [map_sum]
  convert this using 1
  funext w
  simp

theorem ss5t_hasGradientAt_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {F' z : E} (c : ℝ) (h : HasGradientAt F F' z) :
    HasGradientAt (fun w => c * F w) (c • F') z := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  rw [map_smul]
  exact h.const_mul c

theorem ss5t_hasGradientAt_term {N : ℕ} (f f' : ℝ → ℝ) (z : Ch5 N) (k l : Fin N)
    (h : HasDerivAt f (f' (z l - z k)) (z l - z k)) :
    HasGradientAt (fun w : Ch5 N => f (w l - w k)) (f' (z l - z k) • ss5t_v k l) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hL : HasFDerivAt (fun w : Ch5 N => w l - w k) (innerSL ℝ (ss5t_v k l)) z := by
    have := (innerSL ℝ (ss5t_v k l)).hasFDerivAt (x := z)
    convert this using 1
    funext w
    simp [ss5t_inner_v]
  have := h.comp_hasFDerivAt z hL
  have e : InnerProductSpace.toDual ℝ (Ch5 N) (f' (z l - z k) • ss5t_v k l) =
      f' (z l - z k) • innerSL ℝ (ss5t_v k l) := by
    ext w
    simp [InnerProductSpace.toDual_apply_apply, inner_smul_left]
  rw [e]
  exact this

theorem ss5t_hasGradientAt_pair (N : ℕ) (f f' : ℝ → ℝ) (z : Ch5 N)
    (h : ∀ k l : Fin N, k < l → HasDerivAt f (f' (z l - z k)) (z l - z k)) :
    HasGradientAt (ss5t_pairSum N f) (ss5t_pairGrad N f' z) z := by
  have hin : ∀ k l : Fin N, HasGradientAt
      (fun w : Ch5 N => if k < l then f (w l - w k) else 0)
      (if k < l then f' (z l - z k) • ss5t_v k l else 0) z := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      exact ss5t_hasGradientAt_term f f' z k l (h k l hkl)
    · simp only [hkl, if_false]
      exact hasGradientAt_const _ _
  have h1 : ∀ k : Fin N, HasGradientAt
      (fun w : Ch5 N => ∑ l : Fin N, if k < l then f (w l - w k) else 0)
      (∑ l : Fin N, if k < l then f' (z l - z k) • ss5t_v k l else 0) z :=
    fun k => ss5t_hasGradientAt_sum Finset.univ (fun l _ => hin k l)
  have h2 := ss5t_hasGradientAt_sum Finset.univ (fun k (_ : k ∈ Finset.univ) => h1 k)
  exact ss5t_hasGradientAt_mul (1 / (N : ℝ)) h2

theorem ss5t_hasGradientAt_normsq {N : ℕ} (z : Ch5 N) :
    HasGradientAt (fun w : Ch5 N => (1 / 4 : ℝ) * ‖w‖ ^ 2) ((1 / 2 : ℝ) • z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul (1 / 4 : ℝ)
  have e : InnerProductSpace.toDual ℝ (Ch5 N) ((1 / 2 : ℝ) • z) =
      (1 / 4 : ℝ) • (2 • innerSL ℝ z) := by
    ext w
    simp [InnerProductSpace.toDual_apply_apply, inner_smul_left]
    ring
  rw [e]
  exact this

theorem ss5t_hasGradientAt_U {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Ch5 N) :
    HasGradientAt (ss5_U N ε) (ss5t_pairGrad N (ss5t_d1 ε) z + (1 / 2 : ℝ) • z) z := by
  have h1 : HasGradientAt (ss5_PhiTr N ε) (ss5t_pairGrad N (ss5t_d1 ε) z) z :=
    ss5t_hasGradientAt_pair N (ss5_phiTr ε) (ss5t_d1 ε) z (fun k l _ => ss5t_hasDerivAt_phi hε _)
  have h2 := ss5t_hasGradientAt_normsq z
  rw [hasGradientAt_iff_hasFDerivAt] at h1 h2 ⊢
  rw [map_add]
  exact h1.add h2

theorem ss5t_gradient_PhiTr {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Ch5 N) :
    gradient (ss5_PhiTr N ε) z = ss5t_pairGrad N (ss5t_d1 ε) z :=
  (ss5t_hasGradientAt_pair N (ss5_phiTr ε) (ss5t_d1 ε) z
    (fun k l _ => ss5t_hasDerivAt_phi hε _)).gradient

theorem ss5t_gradient_U {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Ch5 N) :
    gradient (ss5_U N ε) z = ss5t_pairGrad N (ss5t_d1 ε) z + (1 / 2 : ℝ) • z :=
  (ss5t_hasGradientAt_U hε z).gradient

/-- Gradient of the singular potential in the open chamber. -/
theorem ss5t_gradient_Phi {N : ℕ} {z : Ch5 N} (hz : z ∈ ss5_chamber N) :
    gradient (ss5_Phi N) z = ss5t_pairGrad N (fun g => -(g⁻¹)) z :=
  (ss5t_hasGradientAt_pair N (fun g => -Real.log g) (fun g => -(g⁻¹)) z
    (fun k l hkl => (Real.hasDerivAt_log (sub_pos.2 (hz k l hkl)).ne').neg)).gradient

theorem ss5t_contDiff_U {N : ℕ} {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (ss5_U N ε) := by
  have hterm : ∀ k l : Fin N, ContDiff ℝ 2 (fun w : Ch5 N => if k < l then ss5_phiTr ε (w l - w k) else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      have hL : ContDiff ℝ 2 (fun w : Ch5 N => w l - w k) := by
        have := (innerSL ℝ (ss5t_v k l)).contDiff (n := 2)
        convert this using 1
        funext w
        simp [ss5t_inner_v]
      exact (ss5t_contDiff_phi hε).comp hL
    · simp only [hkl, if_false]
      exact contDiff_const
  have h1 : ContDiff ℝ 2 (ss5_PhiTr N ε) :=
    contDiff_const.mul (ContDiff.sum fun k _ => ContDiff.sum fun l _ => hterm k l)
  exact h1.add (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem ss5t_pairGrad_dist {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z z' : Ch5 N) :
    ‖ss5t_pairGrad N (ss5t_d1 ε) z - ss5t_pairGrad N (ss5t_d1 ε) z'‖ ≤
      4 * (N : ℝ) * (ε ^ 2)⁻¹ * ‖z - z'‖ := by
  unfold ss5t_pairGrad
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ k l : Fin N, ‖(if k < l then ss5t_d1 ε (z l - z k) • ss5t_v k l else 0) -
      (if k < l then ss5t_d1 ε (z' l - z' k) • ss5t_v k l else 0)‖ ≤ 4 * (ε ^ 2)⁻¹ * ‖z - z'‖ := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have h1 := (ss5t_d1_lip hε).dist_le_mul (z l - z k) (z' l - z' k)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at h1
      have h2 : |(z l - z k) - (z' l - z' k)| ≤ 2 * ‖z - z'‖ := by
        have : (z l - z k) - (z' l - z' k) = inner ℝ (ss5t_v k l) (z - z') := by
          rw [ss5t_inner_v]; simp; ring
        rw [this]
        calc |inner ℝ (ss5t_v k l) (z - z')| ≤ ‖ss5t_v k l‖ * ‖z - z'‖ := abs_real_inner_le_norm _ _
          _ ≤ 2 * ‖z - z'‖ := by gcongr; exact ss5t_norm_v k l
      have h3 := ss5t_norm_v k l
      have hp : 0 ≤ (ε ^ 2)⁻¹ := by positivity
      calc |ss5t_d1 ε (z l - z k) - ss5t_d1 ε (z' l - z' k)| * ‖ss5t_v k l‖
          ≤ ((ε ^ 2)⁻¹ * (2 * ‖z - z'‖)) * 2 := by
            gcongr
            exact h1.trans (by gcongr)
        _ = 4 * (ε ^ 2)⁻¹ * ‖z - z'‖ := by ring
    · simp only [hkl, if_false, sub_zero, norm_zero]
      positivity
  have hsum : ‖∑ k : Fin N, ∑ l : Fin N, ((if k < l then ss5t_d1 ε (z l - z k) • ss5t_v k l else 0) -
      (if k < l then ss5t_d1 ε (z' l - z' k) • ss5t_v k l else 0))‖ ≤
      (N : ℝ) * ((N : ℝ) * (4 * (ε ^ 2)⁻¹ * ‖z - z'‖)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin N, ‖∑ l : Fin N, ((if k < l then ss5t_d1 ε (z l - z k) • ss5t_v k l else 0) -
          (if k < l then ss5t_d1 ε (z' l - z' k) • ss5t_v k l else 0))‖
        ≤ ∑ k : Fin N, ((N : ℝ) * (4 * (ε ^ 2)⁻¹ * ‖z - z'‖)) := by
          refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
          calc ∑ l : Fin N, ‖(if k < l then ss5t_d1 ε (z l - z k) • ss5t_v k l else 0) -
                (if k < l then ss5t_d1 ε (z' l - z' k) • ss5t_v k l else 0)‖
              ≤ ∑ l : Fin N, (4 * (ε ^ 2)⁻¹ * ‖z - z'‖) := Finset.sum_le_sum fun l _ => hterm k l
            _ = _ := by simp
      _ = _ := by simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc 1 / (N : ℝ) * ‖∑ k : Fin N, ∑ l : Fin N, ((if k < l then ss5t_d1 ε (z l - z k) • ss5t_v k l else 0) -
          (if k < l then ss5t_d1 ε (z' l - z' k) • ss5t_v k l else 0))‖
        ≤ 1 / (N : ℝ) * ((N : ℝ) * ((N : ℝ) * (4 * (ε ^ 2)⁻¹ * ‖z - z'‖))) := by gcongr
      _ = 4 * (N : ℝ) * (ε ^ 2)⁻¹ * ‖z - z'‖ := by field_simp

theorem ss5t_PhiTr_ge {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Ch5 N) :
    -(2 * (N : ℝ) * ‖z‖) ≤ ss5_PhiTr N ε z := by
  have hterm : ∀ k l : Fin N, -(2 * ‖z‖) ≤ (if k < l then ss5_phiTr ε (z l - z k) else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      refine le_trans ?_ (ss5t_phi_ge hε hε1 _)
      have : |z l - z k| ≤ 2 * ‖z‖ := by
        rw [← ss5t_inner_v k l z]
        calc |inner ℝ (ss5t_v k l) z| ≤ ‖ss5t_v k l‖ * ‖z‖ := abs_real_inner_le_norm _ _
          _ ≤ 2 * ‖z‖ := by gcongr; exact ss5t_norm_v k l
      linarith
    · simp only [hkl, if_false]
      linarith [norm_nonneg z]
  unfold ss5_PhiTr
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum : -((N : ℝ) * ((N : ℝ) * (2 * ‖z‖))) ≤
        ∑ k : Fin N, ∑ l : Fin N, (if k < l then ss5_phiTr ε (z l - z k) else 0) := by
      calc -((N : ℝ) * ((N : ℝ) * (2 * ‖z‖)))
          = ∑ k : Fin N, ∑ l : Fin N, (-(2 * ‖z‖)) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    calc -(2 * (N : ℝ) * ‖z‖) = 1 / (N : ℝ) * (-((N : ℝ) * ((N : ℝ) * (2 * ‖z‖)))) := by
          field_simp
      _ ≤ _ := by gcongr

theorem ss5t_U_ge {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Ch5 N) :
    (1 / 8 : ℝ) * ‖z‖ ^ 2 - 8 * (N : ℝ) ^ 2 ≤ ss5_U N ε z := by
  have := ss5t_PhiTr_ge hε hε1 z
  unfold ss5_U
  nlinarith [sq_nonneg (‖z‖ - 8 * N)]

theorem ss5t_monotone {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z z' : Ch5 N) :
    0 ≤ inner ℝ (gradient (ss5_PhiTr N ε) z - gradient (ss5_PhiTr N ε) z') (z - z') := by
  rw [ss5t_gradient_PhiTr hε, ss5t_gradient_PhiTr hε]
  unfold ss5t_pairGrad
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [inner_smul_left, sum_inner]
  refine mul_nonneg (by simp) (Finset.sum_nonneg fun k _ => ?_)
  rw [sum_inner]
  refine Finset.sum_nonneg fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    rw [← sub_smul, inner_smul_left, ss5t_inner_v]
    simp only [conj_trivial, PiLp.sub_apply]
    have e : z l - z' l - (z k - z' k) = (z l - z k) - (z' l - z' k) := by ring
    rw [e]
    rcases le_total (z l - z k) (z' l - z' k) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (ss5t_d1_mono hε h)) (sub_nonpos.2 h)
    · exact mul_nonneg (sub_nonneg.2 (ss5t_d1_mono hε h)) (sub_nonneg.2 h)
  · simp [hkl]

theorem ss5_trunc_props_proof (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ 2 (ss5_U N ε) ∧ (∃ K : ℝ≥0, LipschitzWith K (gradient (ss5_U N ε))) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ^ 2 - C ≤ ss5_U N ε z) ∧
      ∀ z z' : Ch5 N, 0 ≤ inner ℝ (gradient (ss5_PhiTr N ε) z - gradient (ss5_PhiTr N ε) z') (z - z') := by
  refine ⟨ss5t_contDiff_U hε, ⟨Real.toNNReal (4 * (N : ℝ) * (ε ^ 2)⁻¹ + 1 / 2), ?_⟩,
    ⟨1 / 8, 8 * (N : ℝ) ^ 2, by norm_num, fun z => ss5t_U_ge hε hε1 z⟩, fun z z' => ss5t_monotone hε z z'⟩
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), ss5t_gradient_U hε,
    ss5t_gradient_U hε]
  have h1 := ss5t_pairGrad_dist hε z z'
  calc ‖ss5t_pairGrad N (ss5t_d1 ε) z + (1 / 2 : ℝ) • z -
        (ss5t_pairGrad N (ss5t_d1 ε) z' + (1 / 2 : ℝ) • z')‖
      = ‖(ss5t_pairGrad N (ss5t_d1 ε) z - ss5t_pairGrad N (ss5t_d1 ε) z') + (1 / 2 : ℝ) • (z - z')‖ := by
        congr 1; rw [smul_sub]; abel
    _ ≤ ‖ss5t_pairGrad N (ss5t_d1 ε) z - ss5t_pairGrad N (ss5t_d1 ε) z'‖ + ‖(1 / 2 : ℝ) • (z - z')‖ :=
        norm_add_le _ _
    _ ≤ 4 * (N : ℝ) * (ε ^ 2)⁻¹ * ‖z - z'‖ + 1 / 2 * ‖z - z'‖ := by
        rw [norm_smul]; norm_num; exact h1
    _ = (4 * (N : ℝ) * (ε ^ 2)⁻¹ + 1 / 2) * ‖z - z'‖ := by ring

example := (@ss5_trunc_props_proof : type_of% @HRS.MP.SelfSimP5.ss5_trunc_props)

end HRS.MP.SelfSimP5Impl
