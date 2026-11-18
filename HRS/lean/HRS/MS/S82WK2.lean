import HRS.MS.S82UG8
import HRS.MS.S82WK1

/-!
# S8.2 A04 (S82W), part 3: the cut-off `Θ_m` of a configuration (far-field times pair cut-offs)
`Θ_m X = ∏_{(i,j)} φ_{ij}(X)`, `φ_{ii} = wc(‖x_i‖²/m²)`, `φ_{ij} = 1 - wc(m² ‖x_i - x_j‖²)` (`i ≠ j`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section factor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma wk_factor_jets {ch : ℝ → ℝ} {B : ℝ} (h : IsCut ch B) {u : E → ℝ} (hu : ContDiff ℝ 2 u) {x : E}
    {e1 e2 : ℝ} (h0 : u x ∈ Set.Icc (1 : ℝ) 2 → ‖fderiv ℝ u x‖ ≤ e1 ∧ ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ e2)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    ‖fderiv ℝ (fun y => ch (u y)) x‖ ≤ B * e1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ch (u y))) x‖ ≤ B * e1 ^ 2 + B * e2 := by
  obtain ⟨hch, hB, -, hz, hbd⟩ := h
  obtain ⟨j1, j2⟩ := w_comp_jets hch hu x
  by_cases hx : u x ∈ Set.Icc (1 : ℝ) 2
  · obtain ⟨a1, a2⟩ := h0 hx
    obtain ⟨b1, b2⟩ := hbd (u x)
    have n1 := norm_nonneg (fderiv ℝ u x)
    have n2 := norm_nonneg (fderiv ℝ (fderiv ℝ u) x)
    constructor
    · exact j1.trans ((mul_le_mul b1 a1 n1 hB))
    · refine j2.trans ?_
      have h1 : |deriv (deriv ch) (u x)| * ‖fderiv ℝ u x‖ ^ 2 ≤ B * e1 ^ 2 :=
        mul_le_mul b2 (pow_le_pow_left₀ n1 a1 2) (by positivity) hB
      have h2 : |deriv ch (u x)| * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B * e2 := mul_le_mul b1 a2 n2 hB
      linarith
  · obtain ⟨a, b⟩ := hz _ hx
    rw [a] at j1
    rw [a, b] at j2
    simp only [abs_zero, zero_mul, zero_add] at j1 j2
    constructor
    · exact j1.trans (by positivity)
    · exact j2.trans (by positivity)

lemma wk_mul_const_jets {g : E → ℝ} (hg : ContDiff ℝ 2 g) (k : ℝ) (x : E) :
    ‖fderiv ℝ (fun y => k * g y) x‖ = |k| * ‖fderiv ℝ g x‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => k * g y)) x‖ = |k| * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfd : fderiv ℝ (fun y => k * g y) = fun y => k • fderiv ℝ g y :=
    funext fun y => fderiv_const_mul (hd y) k
  have hu2 : Differentiable ℝ (fderiv ℝ g) := by
    have : ContDiff ℝ (1 + 1) g := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
    exact (contDiff_succ_iff_fderiv.1 this).2.2.differentiable one_ne_zero
  constructor
  · rw [hfd]
    have := norm_smul k (fderiv ℝ g x)
    simpa [Real.norm_eq_abs] using this
  · have e : fderiv ℝ (fun y => k • fderiv ℝ g y) x = k • fderiv ℝ (fderiv ℝ g) x :=
      fderiv_const_smul (hu2 x) k
    rw [hfd, e]
    have := ContinuousLinearMap.opNorm_smul_le k (fderiv ℝ (fderiv ℝ g) x)
    refine le_antisymm (by simpa [Real.norm_eq_abs] using this) ?_
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [abs_zero, zero_mul]; exact ContinuousLinearMap.opNorm_nonneg _
    · have h2 := ContinuousLinearMap.opNorm_smul_le k⁻¹ (k • fderiv ℝ (fderiv ℝ g) x)
      rw [← mul_smul, inv_mul_cancel₀ hk, one_smul] at h2
      rw [Real.norm_eq_abs, abs_inv] at h2
      have hk' : 0 < |k| := abs_pos.2 hk
      calc |k| * ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ |k| * (|k|⁻¹ * ‖k • fderiv ℝ (fderiv ℝ g) x‖) :=
            mul_le_mul_of_nonneg_left h2 hk'.le
        _ = ‖k • fderiv ℝ (fderiv ℝ g) x‖ := by field_simp

end factor

def wB : ℝ := Classical.choose exists_isCut

lemma wB_cut : IsCut wc wB ∧ IsCut (fun s => 1 - wc s) wB := Classical.choose_spec exists_isCut

lemma wB_nonneg : 0 ≤ wB := wB_cut.1.2.1

section theta
variable {d N : ℕ}

def wP (d N : ℕ) (i : Fin N) : EucConfig d N →L[ℝ] Euc d :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i

def wL (d N : ℕ) (i j : Fin N) : EucConfig d N →L[ℝ] Euc d :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j

lemma wP_apply (i : Fin N) (X : EucConfig d N) : wP d N i X = X i := rfl

lemma wL_apply (i j : Fin N) (X : EucConfig d N) : wL d N i j X = X i - X j := by simp [wL]

lemma wP_norm_le (i : Fin N) : ‖wP d N i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => ?_
  rw [wP_apply, one_mul]; exact norm_le_pi_norm X i

lemma wL_norm_le (i j : Fin N) : ‖wL d N i j‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun X => ?_
  rw [wL_apply]
  calc ‖X i - X j‖ ≤ ‖X i‖ + ‖X j‖ := norm_sub_le _ _
    _ ≤ ‖X‖ + ‖X‖ := add_le_add (norm_le_pi_norm X i) (norm_le_pi_norm X j)
    _ = 2 * ‖X‖ := by ring

/-- the factors of the cut-off -/
def wfac (m : ℝ) (p : Fin N × Fin N) (X : EucConfig d N) : ℝ :=
  if p.1 = p.2 then wc ((1 / m ^ 2) * ‖X p.1‖ ^ 2) else 1 - wc (m ^ 2 * ‖X p.1 - X p.2‖ ^ 2)

def wTheta (d N : ℕ) (m : ℝ) (X : EucConfig d N) : ℝ := ∏ p : Fin N × Fin N, wfac m p X

lemma wfac_diag (m : ℝ) (i : Fin N) :
    (wfac (d := d) m (i, i)) = fun y => wc ((1 / m ^ 2) * ‖wP d N i y‖ ^ 2) := by
  funext y; simp [wfac, wP_apply]

lemma wfac_pair (m : ℝ) {i j : Fin N} (h : i ≠ j) :
    (wfac (d := d) m (i, j)) = fun y => (fun s => 1 - wc s) (m ^ 2 * ‖wL d N i j y‖ ^ 2) := by
  funext y; simp [wfac, wL_apply, h]

lemma wfac_contDiff (m : ℝ) (p : Fin N × Fin N) : ContDiff ℝ 2 (wfac (d := d) m p) := by
  have hc : ContDiff ℝ 2 wc := wc_contDiff.of_le (by norm_num)
  obtain ⟨i, j⟩ := p
  by_cases h : i = j
  · subst h
    rw [wfac_diag]
    exact hc.comp (contDiff_const.mul (wk_sq_jets (wP d N i)).1)
  · rw [wfac_pair m h]
    exact (contDiff_const.sub hc).comp (contDiff_const.mul (wk_sq_jets (wL d N i j)).1)

lemma wfac_01 (m : ℝ) (p : Fin N × Fin N) (X : EucConfig d N) : 0 ≤ wfac m p X ∧ wfac m p X ≤ 1 := by
  unfold wfac
  split_ifs
  · exact ⟨wc_nonneg _, wc_le_one _⟩
  · exact ⟨by linarith [wc_le_one (m ^ 2 * ‖X p.1 - X p.2‖ ^ 2)], by linarith [wc_nonneg (m ^ 2 * ‖X p.1 - X p.2‖ ^ 2)]⟩

lemma wTheta_contDiff (m : ℝ) : ContDiff ℝ 2 (wTheta d N m) :=
  contDiff_prod (fun p _ => wfac_contDiff m p)

lemma wTheta_01 (m : ℝ) (X : EucConfig d N) : 0 ≤ wTheta d N m X ∧ wTheta d N m X ≤ 1 :=
  ⟨Finset.prod_nonneg fun p _ => (wfac_01 m p X).1,
    Finset.prod_le_one₀ (fun p _ => (wfac_01 m p X).1) fun p _ => (wfac_01 m p X).2⟩

def wb1 (p : Fin N × Fin N) (X : EucConfig d N) : ℝ :=
  if p.1 = p.2 then 4 * wB else 8 * wB * ‖X p.1 - X p.2‖ ^ (-(1 : ℝ))

def wb2 (p : Fin N × Fin N) (X : EucConfig d N) : ℝ :=
  if p.1 = p.2 then 18 * wB else 80 * wB * ‖X p.1 - X p.2‖ ^ (-(2 : ℝ))

set_option maxHeartbeats 1000000 in
lemma wfac_jets {m : ℝ} (hm : 1 ≤ m) (p : Fin N × Fin N) {X : EucConfig d N}
    (hX : p.1 ≠ p.2 → X p.1 ≠ X p.2) :
    ‖fderiv ℝ (wfac (d := d) m p) X‖ ≤ wb1 p X ∧ ‖fderiv ℝ (fderiv ℝ (wfac (d := d) m p)) X‖ ≤ wb2 p X := by
  have hB := wB_nonneg
  have hm0 : 0 < m := by linarith
  obtain ⟨i, j⟩ := p
  by_cases h : i = j
  · subst h
    simp only [wb1, wb2, if_true]
    rw [wfac_diag]
    obtain ⟨hsc, hsj⟩ := wk_sq_jets (wP d N i)
    obtain ⟨s1, s2⟩ := hsj X
    have hk : (0 : ℝ) ≤ 1 / m ^ 2 := by positivity
    obtain ⟨m1, m2⟩ := wk_mul_const_jets hsc (1 / m ^ 2) X
    rw [abs_of_nonneg hk] at m1 m2
    have := wk_factor_jets (ch := wc) (B := wB) wB_cut.1 (u := fun y => (1 / m ^ 2) * ‖wP d N i y‖ ^ 2)
      (contDiff_const.mul hsc) (x := X) (e1 := 4) (e2 := 2) ?_ (by norm_num) (by norm_num)
    · obtain ⟨a, b⟩ := this
      constructor
      · linarith
      · nlinarith
    · intro hx
      have h2 : (1 / m ^ 2) * ‖X i‖ ^ 2 ≤ 2 := hx.2
      have h3 : ‖X i‖ ≤ 2 * m := by
        have : ‖X i‖ ^ 2 ≤ (2 * m) ^ 2 := by
          have : ‖X i‖ ^ 2 ≤ 2 * m ^ 2 := by
            rw [one_div, inv_mul_le_iff₀ (by positivity)] at h2; linarith
          nlinarith
        exact le_of_sq_le_sq this (by positivity) |>.trans le_rfl
      have hP := wP_norm_le (d := d) i
      have hn1 : ‖wP d N i X‖ ≤ 2 * m := by rw [wP_apply]; exact h3
      have e1 : (1 / m ^ 2) * (2 * ‖wP d N i‖ * ‖wP d N i X‖) ≤ 4 := by
        have : (1 / m ^ 2) * (2 * ‖wP d N i‖ * ‖wP d N i X‖) ≤ (1 / m ^ 2) * (2 * 1 * (2 * m)) := by
          gcongr
        refine this.trans ?_
        have : (1 / m ^ 2) * (2 * 1 * (2 * m)) = 4 / m := by field_simp; ring
        rw [this, div_le_iff₀ hm0]; nlinarith
      have e2 : (1 / m ^ 2) * (2 * ‖wP d N i‖ ^ 2) ≤ 2 := by
        have : (1 / m ^ 2) * (2 * ‖wP d N i‖ ^ 2) ≤ (1 / m ^ 2) * (2 * 1 ^ 2) := by
          gcongr
        refine this.trans ?_
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
      exact ⟨by rw [m1]; exact (mul_le_mul_of_nonneg_left s1 hk).trans (by simpa [mul_assoc] using e1) |>.trans le_rfl,
        by rw [m2]; exact (mul_le_mul_of_nonneg_left s2 hk).trans (by simpa [mul_assoc] using e2)⟩
  · simp only [wb1, wb2, h, if_false]
    rw [wfac_pair m h]
    have hr : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 (hX h))
    obtain ⟨hsc, hsj⟩ := wk_sq_jets (wL d N i j)
    obtain ⟨s1, s2⟩ := hsj X
    have hk : (0 : ℝ) ≤ m ^ 2 := by positivity
    obtain ⟨m1, m2⟩ := wk_mul_const_jets hsc (m ^ 2) X
    rw [abs_of_nonneg hk] at m1 m2
    set r := ‖X i - X j‖ with hrdef
    have hrinv : r ^ (-(1 : ℝ)) = r⁻¹ := Real.rpow_neg_one r
    have hrinv2 : r ^ (-(2 : ℝ)) = (r ^ 2)⁻¹ := by
      rw [Real.rpow_neg hr.le]; norm_cast
    have hLn := wL_norm_le (d := d) i j
    have hLX : ‖wL d N i j X‖ = r := by rw [wL_apply]
    have key : (m ^ 2 * ‖wL d N i j X‖ ^ 2 ∈ Set.Icc (1 : ℝ) 2) →
        ‖fderiv ℝ (fun y => m ^ 2 * ‖wL d N i j y‖ ^ 2) X‖ ≤ 8 * r⁻¹ ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => m ^ 2 * ‖wL d N i j y‖ ^ 2)) X‖ ≤ 16 * (r ^ 2)⁻¹ := by
      intro hx
      have h2 : m ^ 2 * ‖wL d N i j X‖ ^ 2 ≤ 2 := hx.2
      rw [hLX] at h2
      have h3 : m ^ 2 * r ≤ 2 * r⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hr]; nlinarith
      have h4 : m ^ 2 ≤ 2 * (r ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      have n1 : ‖fderiv ℝ (fun y => ‖wL d N i j y‖ ^ 2) X‖ ≤ 4 * r := by
        rw [hLX] at s1
        nlinarith [norm_nonneg (fderiv ℝ (fun y => ‖wL d N i j y‖ ^ 2) X)]
      have n2 : ‖fderiv ℝ (fderiv ℝ (fun y => ‖wL d N i j y‖ ^ 2)) X‖ ≤ 8 := by
        have := mul_self_le_mul_self (norm_nonneg (wL d N i j)) hLn
        nlinarith
      constructor
      · rw [m1]
        calc m ^ 2 * ‖fderiv ℝ (fun y => ‖wL d N i j y‖ ^ 2) X‖ ≤ m ^ 2 * (4 * r) :=
              mul_le_mul_of_nonneg_left n1 hk
          _ ≤ 8 * r⁻¹ := by nlinarith
      · rw [m2]
        calc m ^ 2 * ‖fderiv ℝ (fderiv ℝ (fun y => ‖wL d N i j y‖ ^ 2)) X‖ ≤ m ^ 2 * 8 :=
              mul_le_mul_of_nonneg_left n2 hk
          _ ≤ 16 * (r ^ 2)⁻¹ := by nlinarith
    obtain ⟨a, b⟩ := wk_factor_jets (ch := fun s => 1 - wc s) (B := wB) wB_cut.2
      (u := fun y => m ^ 2 * ‖wL d N i j y‖ ^ 2) (contDiff_const.mul hsc) (x := X)
      (e1 := 8 * r⁻¹) (e2 := 16 * (r ^ 2)⁻¹) key (by positivity) (by positivity)
    have e : (8 * r⁻¹) ^ 2 = 64 * (r ^ 2)⁻¹ := by field_simp; norm_num
    constructor
    · rw [hrinv]; linarith
    · rw [hrinv2]; rw [e] at b; linarith

end theta

end HRS.MS.S82W
