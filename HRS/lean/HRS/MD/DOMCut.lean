/-
# HRS.MD.DOMCut — packet DOM-CUT (part 1): the pair cut-off profile

`sE y = ∑_k (1 - cos 2π y_k)` and its torus version `sT`; the profile `th` (smooth, `0` on `(-∞,1]`, `1` on
`[2,∞)`); the factor `Th ε v = th (sE v / ε)` with the gradient/Laplacian bounds
`|∇Th|² sE ≤ M₁`, `|ΔTh| sE ≤ M₂` on the shell `sE ≤ 2ε`, and `∇Th = 0 = ΔTh` when `sE > 2ε`.
-/
import HRS.MD.DOMCalc

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

variable {d : ℕ}

/-! ### The circle functions -/

def sT (u : Torus d) : ℝ := ∑ k, (1 - Real.cos (2 * Real.pi * ‖u k‖))

def sE (y : Euc d) : ℝ := ∑ k, (1 - Real.cos (2 * Real.pi * y k))

theorem domp_norm_coe_circle (r : ℝ) : ‖((r : ℝ) : UnitAddCircle)‖ = |r - round r| := by
  have := AddCircle.norm_eq (1 : ℝ) (x := r)
  simpa using this

theorem domp_cos_norm_coe (r : ℝ) :
    Real.cos (2 * Real.pi * ‖((r : ℝ) : UnitAddCircle)‖) = Real.cos (2 * Real.pi * r) := by
  rw [domp_norm_coe_circle]
  have h1 : 2 * Real.pi * |r - round r| = |2 * Real.pi * (r - round r)| := by
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
  rw [h1, Real.cos_abs]
  have := Real.cos_sub_int_mul_two_pi (2 * Real.pi * r) (round r)
  rw [← this]
  congr 1
  ring

theorem domp_sT_mk (y : Euc d) : sT (Torus.mk y) = sE y := by
  unfold sT sE
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Torus.mk y) k = ((y k : ℝ) : UnitAddCircle) from rfl, domp_cos_norm_coe]

theorem domp_sE_nonneg (y : Euc d) : 0 ≤ sE y :=
  Finset.sum_nonneg fun k _ => by linarith [Real.cos_le_one (2 * Real.pi * y k)]

theorem domp_sT_nonneg (u : Torus d) : 0 ≤ sT u :=
  Finset.sum_nonneg fun k _ => by linarith [Real.cos_le_one (2 * Real.pi * ‖u k‖)]

theorem domp_sT_zero : sT (0 : Torus d) = 0 := by
  unfold sT
  simp

theorem domp_sT_neg (u : Torus d) : sT (-u) = sT u := by
  unfold sT
  simp

theorem domp_sE_neg (y : Euc d) : sE (-y) = sE y := by
  unfold sE
  simp [mul_neg, Real.cos_neg]

theorem domp_continuous_sT : Continuous (sT : Torus d → ℝ) := by
  unfold sT
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul
    (continuous_norm.comp (continuous_apply k))))

theorem domp_sE_eq_zero_imp (y : Euc d) (h : sE y = 0) : Torus.mk y = 0 := by
  unfold sE at h
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
    linarith [Real.cos_le_one (2 * Real.pi * y k)])).1 h
  funext k
  have h1 := hk k (Finset.mem_univ k)
  have h2 : Real.cos (2 * Real.pi * y k) = 1 := by linarith
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 h2
  have h3 : y k = m := by
    have := Real.pi_pos
    nlinarith
  show ((y k : ℝ) : UnitAddCircle) = 0
  rw [h3, AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

theorem domp_sT_pos {u : Torus d} (hu : u ≠ 0) : 0 < sT u := by
  rcases (domp_sT_nonneg u).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hu
    have h1 : sT u = sE (Torus.rep u) := by
      rw [← domp_sT_mk, Torus.mk_rep]
    rw [← Torus.mk_rep u]
    exact domp_sE_eq_zero_imp _ (by rw [← h1]; exact h.symm)

theorem domp_contDiff_sE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sE : Euc d → ℝ) := by
  unfold sE
  refine ContDiff.sum fun k _ => ?_
  refine contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul ?_))
  exact (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff

theorem domp_hasFDerivAt_sE (y : Euc d) :
    HasFDerivAt (sE : Euc d → ℝ)
      (∑ k, (2 * Real.pi * Real.sin (2 * Real.pi * y k)) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y := by
  unfold sE
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have h1 : HasFDerivAt (fun u : Euc d => 2 * Real.pi * u k)
      ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y :=
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * Real.pi)
  have h2 := (Real.hasDerivAt_cos (2 * Real.pi * y k)).comp_hasFDerivAt y h1
  have h3 := (hasFDerivAt_const (1 : ℝ) y).sub h2
  convert h3 using 1
  · funext z; simp
  · rw [zero_sub, neg_smul, neg_neg, smul_smul]
    congr 1
    ring

theorem domp_dk_sE (k : Fin d) (y : Euc d) : dk sE k y = 2 * Real.pi * Real.sin (2 * Real.pi * y k) := by
  unfold dk
  rw [(domp_hasFDerivAt_sE y).fderiv]
  simp [PiLp.single_apply, Finset.sum_apply]

theorem domp_ddk_sE (k : Fin d) (y : Euc d) :
    ddk sE k y = 4 * Real.pi ^ 2 * Real.cos (2 * Real.pi * y k) := by
  unfold ddk
  have e : dk sE k = fun z : Euc d => 2 * Real.pi * Real.sin (2 * Real.pi * z k) :=
    funext fun z => domp_dk_sE k z
  rw [e]
  have h1 : HasFDerivAt (fun u : Euc d => 2 * Real.pi * u k)
      ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y :=
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * Real.pi)
  have h2 : HasFDerivAt (fun z : Euc d => 2 * Real.pi * Real.sin (2 * Real.pi * z k))
      ((2 * Real.pi) • (Real.cos (2 * Real.pi * y k) • ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)))) y :=
    ((Real.hasDerivAt_sin (2 * Real.pi * y k)).comp_hasFDerivAt y h1).const_mul (2 * Real.pi)
  rw [h2.fderiv]
  simp [PiLp.single_apply]
  ring

theorem domp_sin_sq_le (x : ℝ) : Real.sin x ^ 2 ≤ 2 * (1 - Real.cos x) := by
  have h := Real.sin_sq_add_cos_sq x
  have h1 := Real.cos_le_one x
  have h2 := Real.neg_one_le_cos x
  nlinarith

theorem domp_sum_sin_sq_le (y : Euc d) :
    ∑ k, (2 * Real.pi * Real.sin (2 * Real.pi * y k)) ^ 2 ≤ 8 * Real.pi ^ 2 * sE y := by
  unfold sE
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := domp_sin_sq_le (2 * Real.pi * y k)
  have h2 : (2 * Real.pi * Real.sin (2 * Real.pi * y k)) ^ 2 =
      4 * Real.pi ^ 2 * Real.sin (2 * Real.pi * y k) ^ 2 := by ring
  rw [h2]
  nlinarith [sq_nonneg Real.pi]

/-! ### The profile `th` -/

def th (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem domp_th_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) th :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem domp_th_zero {t : ℝ} (ht : t ≤ 1) : th t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem domp_th_one {t : ℝ} (ht : 2 ≤ t) : th t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem domp_th_nonneg (t : ℝ) : 0 ≤ th t := Real.smoothTransition.nonneg _

theorem domp_th_le_one (t : ℝ) : th t ≤ 1 := Real.smoothTransition.le_one _

theorem domp_deriv_th_zero {t : ℝ} (ht : 2 < t) : deriv th t = 0 := by
  have : th =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact domp_th_one hy.le
  rw [this.deriv_eq]; simp

theorem domp_deriv_th_zero' {t : ℝ} (ht : t < 1) : deriv th t = 0 := by
  have : th =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact domp_th_zero hy.le
  rw [this.deriv_eq]; simp

theorem domp_deriv2_th_zero {t : ℝ} (ht : 2 < t) : deriv (deriv th) t = 0 := by
  have : deriv th =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact domp_deriv_th_zero hy
  rw [this.deriv_eq]; simp

theorem domp_deriv2_th_zero' {t : ℝ} (ht : t < 1) : deriv (deriv th) t = 0 := by
  have : deriv th =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact domp_deriv_th_zero' hy
  rw [this.deriv_eq]; simp

theorem domp_bounded_of_support {φ : ℝ → ℝ} (hc : Continuous φ)
    (hs : ∀ t, t ∉ Set.Icc (1 : ℝ) 2 → φ t = 0) : ∃ A : ℝ, 0 ≤ A ∧ ∀ t, |φ t| ≤ A := by
  have hsupp : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => by
      by_contra h
      exact hx (hs x h))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hsupp
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

theorem domp_exists_th_bounds : ∃ A₁ A₂ : ℝ, 0 ≤ A₁ ∧ 0 ≤ A₂ ∧
    (∀ t, |deriv th t| ≤ A₁) ∧ (∀ t, |deriv (deriv th) t| ≤ A₂) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) th := domp_th_smooth
  have h1 : ContDiff ℝ 1 (deriv th) := by
    have := hs.iterate_deriv 1
    simp only [Function.iterate_one] at this
    exact this.of_le (by exact_mod_cast le_top)
  have h2 : ContDiff ℝ 1 (deriv (deriv th)) := by
    have := hs.iterate_deriv 2
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at this
    exact this.of_le (by exact_mod_cast le_top)
  obtain ⟨A₁, hA₁, hA₁'⟩ := domp_bounded_of_support h1.continuous (fun t ht => by
    rcases not_and_or.1 ht with h | h
    · exact domp_deriv_th_zero' (not_le.1 h)
    · exact domp_deriv_th_zero (not_le.1 h))
  obtain ⟨A₂, hA₂, hA₂'⟩ := domp_bounded_of_support h2.continuous (fun t ht => by
    rcases not_and_or.1 ht with h | h
    · exact domp_deriv2_th_zero' (not_le.1 h)
    · exact domp_deriv2_th_zero (not_le.1 h))
  exact ⟨A₁, A₂, hA₁, hA₂, hA₁', hA₂'⟩

/-! ### The factor `Th ε v = th (ε⁻¹ sE v)` -/

def Th (ε : ℝ) (v : Euc d) : ℝ := th (ε⁻¹ * sE v)

theorem domp_contDiff_T (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => ε⁻¹ * sE y) :=
  contDiff_const.mul domp_contDiff_sE

theorem domp_Th_smooth (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Th ε : Euc d → ℝ) :=
  domp_th_smooth.comp (domp_contDiff_T ε)

theorem domp_dk_T (ε : ℝ) (k : Fin d) (y : Euc d) :
    dk (fun z : Euc d => ε⁻¹ * sE z) k y = ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * y k)) := by
  have hd : DifferentiableAt ℝ (sE : Euc d → ℝ) y :=
    (domp_contDiff_sE.differentiable (by simp)) y
  unfold dk
  rw [fderiv_const_mul hd]
  have := domp_dk_sE k y
  unfold dk at this
  simp [this]

theorem domp_ddk_T (ε : ℝ) (k : Fin d) (y : Euc d) :
    ddk (fun z : Euc d => ε⁻¹ * sE z) k y = ε⁻¹ * (4 * Real.pi ^ 2 * Real.cos (2 * Real.pi * y k)) := by
  have e : dk (fun z : Euc d => ε⁻¹ * sE z) k =
      fun z => ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * z k)) := funext fun z => domp_dk_T ε k z
  unfold ddk
  rw [e]
  have h1 : HasFDerivAt (fun u : Euc d => 2 * Real.pi * u k)
      ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y :=
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * Real.pi)
  have h2 : HasFDerivAt (fun z : Euc d => ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * z k)))
      (ε⁻¹ • ((2 * Real.pi) • (Real.cos (2 * Real.pi * y k) • ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ))))) y :=
    (((Real.hasDerivAt_sin (2 * Real.pi * y k)).comp_hasFDerivAt y h1).const_mul (2 * Real.pi)).const_mul ε⁻¹
  rw [h2.fderiv]
  simp [PiLp.single_apply]
  all_goals first | (left; ring) | ring

theorem domp_dk_Th (ε : ℝ) (k : Fin d) (v : Euc d) :
    dk (Th ε) k v = deriv th (ε⁻¹ * sE v) * (ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * v k))) := by
  have hT := (domp_contDiff_T ε (d := d)).differentiable (by simp) v
  have hθ := (domp_th_smooth.differentiable (by simp)) (ε⁻¹ * sE v)
  have := domp_dk_comp' th hθ hT k
  rw [domp_dk_T] at this
  exact this

theorem domp_ddk_Th (ε : ℝ) (k : Fin d) (v : Euc d) :
    ddk (Th ε) k v = deriv (deriv th) (ε⁻¹ * sE v) *
        (ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * v k))) ^ 2 +
      deriv th (ε⁻¹ * sE v) * (ε⁻¹ * (4 * Real.pi ^ 2 * Real.cos (2 * Real.pi * v k))) := by
  have hT : ContDiffAt ℝ 2 (fun y : Euc d => ε⁻¹ * sE y) v :=
    ((domp_contDiff_T ε (d := d)).of_le (by norm_cast)).contDiffAt
  have hθ : ContDiff ℝ 2 th := domp_th_smooth.of_le (by norm_cast)
  have := domp_ddk_comp th hθ hT k
  rw [domp_dk_T, domp_ddk_T] at this
  exact this

theorem domp_Th_far {ε : ℝ} (hε : 0 < ε) {v : Euc d} (hv : 2 * ε < sE v) :
    gradient (Th ε) v = 0 ∧ Laplacian.laplacian (Th ε) v = 0 := by
  have hcont : Continuous (fun y : Euc d => ε⁻¹ * sE y) := (domp_contDiff_T ε).continuous
  have hev : Th ε =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
    have : ∀ᶠ y in 𝓝 v, 2 < ε⁻¹ * sE y := by
      refine hcont.continuousAt.eventually (lt_mem_nhds ?_)
      show 2 < ε⁻¹ * sE v
      rw [← div_eq_inv_mul, lt_div_iff₀ hε]; linarith
    filter_upwards [this] with y hy
    exact domp_th_one hy.le
  refine ⟨?_, ?_⟩
  · rw [hev.gradient_eq]; simp
  · rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    exact congrFun (InnerProductSpace.laplacian_const (E := Euc d) (c := (1 : ℝ))) v

theorem domp_Th_grad_sq {ε A₁ : ℝ} (hε : 0 < ε) (hA₁ : ∀ t, |deriv th t| ≤ A₁) (v : Euc d) :
    ‖gradient (Th ε) v‖ ^ 2 ≤ A₁ ^ 2 * (8 * Real.pi ^ 2 * sE v) * ε⁻¹ ^ 2 := by
  rw [domp_norm_gradient_sq]
  have hA : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ 0)
  calc ∑ k, dk (Th ε) k v ^ 2
      = ∑ k, deriv th (ε⁻¹ * sE v) ^ 2 * (ε⁻¹ ^ 2 * (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [domp_dk_Th]; ring
    _ ≤ ∑ k, A₁ ^ 2 * (ε⁻¹ ^ 2 * (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have := hA₁ (ε⁻¹ * sE v)
        calc deriv th (ε⁻¹ * sE v) ^ 2 = |deriv th (ε⁻¹ * sE v)| ^ 2 := (sq_abs _).symm
          _ ≤ A₁ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = A₁ ^ 2 * ε⁻¹ ^ 2 * ∑ k, (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ A₁ ^ 2 * ε⁻¹ ^ 2 * (8 * Real.pi ^ 2 * sE v) := by
        gcongr
        exact domp_sum_sin_sq_le v
    _ = _ := by ring

theorem domp_Th_lap_le {ε A₁ A₂ : ℝ} (hε : 0 < ε) (hA₁ : ∀ t, |deriv th t| ≤ A₁)
    (hA₂ : ∀ t, |deriv (deriv th) t| ≤ A₂) (v : Euc d) :
    |Laplacian.laplacian (Th ε) v| ≤
      A₂ * (8 * Real.pi ^ 2 * sE v) * ε⁻¹ ^ 2 + d * (A₁ * (4 * Real.pi ^ 2)) * ε⁻¹ := by
  have hcd : ContDiffAt ℝ 2 (Th ε : Euc d → ℝ) v :=
    ((domp_Th_smooth ε).of_le (by norm_cast)).contDiffAt
  rw [domp_lap_eq_sum_ddk hcd]
  have hA₁0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (abs_nonneg _).trans (hA₂ 0)
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  calc |∑ k, ddk (Th ε) k v| ≤ ∑ k, |ddk (Th ε) k v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (A₂ * ε⁻¹ ^ 2 * (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2 +
          A₁ * (4 * Real.pi ^ 2) * ε⁻¹) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [domp_ddk_Th]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          have h2 := hA₂ (ε⁻¹ * sE v)
          calc |deriv (deriv th) (ε⁻¹ * sE v)| * |(ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * v k))) ^ 2|
              ≤ A₂ * |(ε⁻¹ * (2 * Real.pi * Real.sin (2 * Real.pi * v k))) ^ 2| :=
                mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
            _ = A₂ * ε⁻¹ ^ 2 * (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2 := by
                rw [abs_of_nonneg (sq_nonneg _)]; ring
        · rw [abs_mul]
          have h1 := hA₁ (ε⁻¹ * sE v)
          have hcos : |ε⁻¹ * (4 * Real.pi ^ 2 * Real.cos (2 * Real.pi * v k))| ≤ ε⁻¹ * (4 * Real.pi ^ 2) := by
            rw [abs_mul, abs_of_nonneg hεi, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)]
            exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)) hεi
          calc |deriv th (ε⁻¹ * sE v)| * |ε⁻¹ * (4 * Real.pi ^ 2 * Real.cos (2 * Real.pi * v k))|
              ≤ A₁ * (ε⁻¹ * (4 * Real.pi ^ 2)) := mul_le_mul h1 hcos (abs_nonneg _) hA₁0
            _ = A₁ * (4 * Real.pi ^ 2) * ε⁻¹ := by ring
    _ = A₂ * ε⁻¹ ^ 2 * ∑ k, (2 * Real.pi * Real.sin (2 * Real.pi * v k)) ^ 2 +
          d * (A₁ * (4 * Real.pi ^ 2) * ε⁻¹) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    _ ≤ A₂ * ε⁻¹ ^ 2 * (8 * Real.pi ^ 2 * sE v) + d * (A₁ * (4 * Real.pi ^ 2) * ε⁻¹) := by
        gcongr
        exact domp_sum_sin_sq_le v
    _ = _ := by ring

/-- The shell estimates: `|∇Th|² sE ≤ M₁`, `|ΔTh| sE ≤ M₂` on `0 < sE ≤ 2ε`; `∇Th = ΔTh = 0` for `sE > 2ε`. -/
theorem domp_Th_bounds : ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ (ε : ℝ) (v : Euc d), 0 < ε →
    (2 * ε < sE v → gradient (Th ε) v = 0 ∧ Laplacian.laplacian (Th ε) v = 0) ∧
    (0 < sE v → sE v ≤ 2 * ε →
      ‖gradient (Th ε) v‖ ^ 2 * sE v ≤ M₁ ∧ |Laplacian.laplacian (Th ε) v| * sE v ≤ M₂) := by
  obtain ⟨A₁, A₂, hA₁0, hA₂0, hA₁, hA₂⟩ := domp_exists_th_bounds
  refine ⟨32 * Real.pi ^ 2 * A₁ ^ 2, 32 * Real.pi ^ 2 * A₂ + 8 * Real.pi ^ 2 * d * A₁,
    by positivity, by positivity, fun ε v hε => ⟨fun hv => domp_Th_far hε hv, fun hσ hsh => ?_⟩⟩
  set σ := sE v with hσdef
  have hεσ : σ / 2 ≤ ε := by linarith
  have hεi : ε⁻¹ ≤ 2 / σ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hε hσ]; linarith
  have hεi2 : ε⁻¹ ^ 2 ≤ 4 / σ ^ 2 := by
    calc ε⁻¹ ^ 2 ≤ (2 / σ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hε.le) hεi 2
      _ = 4 / σ ^ 2 := by rw [div_pow]; norm_num
  have hεi0 : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  constructor
  · have h := domp_Th_grad_sq hε hA₁ v
    calc ‖gradient (Th ε) v‖ ^ 2 * σ ≤ A₁ ^ 2 * (8 * Real.pi ^ 2 * σ) * ε⁻¹ ^ 2 * σ :=
          mul_le_mul_of_nonneg_right h hσ.le
      _ ≤ A₁ ^ 2 * (8 * Real.pi ^ 2 * σ) * (4 / σ ^ 2) * σ := by gcongr
      _ = 32 * Real.pi ^ 2 * A₁ ^ 2 := by field_simp; ring
  · have h := domp_Th_lap_le hε hA₁ hA₂ v
    calc |Laplacian.laplacian (Th ε) v| * σ
        ≤ (A₂ * (8 * Real.pi ^ 2 * σ) * ε⁻¹ ^ 2 + d * (A₁ * (4 * Real.pi ^ 2)) * ε⁻¹) * σ :=
          mul_le_mul_of_nonneg_right h hσ.le
      _ ≤ (A₂ * (8 * Real.pi ^ 2 * σ) * (4 / σ ^ 2) + d * (A₁ * (4 * Real.pi ^ 2)) * (2 / σ)) * σ := by
          gcongr
      _ = 32 * Real.pi ^ 2 * A₂ + 8 * Real.pi ^ 2 * d * A₁ := by field_simp; ring

end HRS.MD.DOMProof

end
