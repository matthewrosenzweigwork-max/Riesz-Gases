import HRS.MC.D1TAux1

/-!
# Packet D1T, auxiliary file 2: locality of the heat-damped series for small `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators FourierTransform

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

theorem d1t_mode_integral {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (k : Lattice d) (y0 : Euc d) :
    ∫ y : Euc d, ((fdlPhiScale ψ t y : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y)) =
      ((fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) * Torus.mode k (Torus.mk y0) := by
  have h := Per.per_fourier_scale hψ ht (Lattice.toEuc k)
  have key : ∀ y : Euc d, ((fdlPhiScale ψ t y : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y)) =
      Torus.mode k (Torus.mk y0) * (𝐞 (-inner ℝ y (Lattice.toEuc k)) • ((fdlPhiScale ψ t y : ℝ) : ℂ)) := by
    intro y
    simp only [Torus.mode_mk, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [Torus.dot_eq_inner, Torus.dot_eq_inner, inner_sub_right, real_inner_comm y]
    rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul, h, mul_comm]
  push_cast; rfl


theorem d1t_mk_eq (w : Euc d) :
    Torus.mk w = fun i => (((w i - round (w i) : ℝ)) : UnitAddCircle) := by
  funext i
  simp only [Torus.mk]
  rw [AddCircle.coe_sub]
  have : ((round (w i) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round (w i), by simp⟩
  rw [this, sub_zero]

theorem d1t_theta_euc (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ w : Euc d, (∃ i0, ∀ n : ℤ, δ ≤ |w i0 - n|) →
      ‖∑' k : Lattice d, ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) *
          Torus.mode k (Torus.mk w)‖ ≤ M := by
  obtain ⟨M, hM⟩ := d1t_theta_unif d hδ
  refine ⟨M, fun u hu hu1 w ⟨i0, hi0⟩ => ?_⟩
  rw [d1t_mk_eq w]
  exact hM u hu hu1 (fun i => w i - round (w i)) (fun i => abs_sub_round (w i))
    ⟨i0, hi0 (round (w i0))⟩


theorem d1t_phiScale_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    0 ≤ fdlPhiScale ψ t y := by
  unfold fdlPhiScale
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le d)) (D1E.d1e_phi_nonneg hψ _)

theorem d1t_phiScale_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    Integrable (fdlPhiScale ψ t) := by
  refine (Per.per_phiScale_contDiff hψ t).continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) t) fun y hy => ?_
  refine Per.per_phiScale_zero hψ ht ?_
  rw [mem_closedBall_zero_iff] at hy
  exact (not_le.mp hy).le

theorem d1t_phiScale_integral {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    ∫ y, fdlPhiScale ψ t y = fdlPsiHat ψ 0 ^ 2 := by
  have h := Per.per_fourier_scale hψ ht (0 : Euc d)
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul, smul_zero] at h
  have h2 : (((∫ y, fdlPhiScale ψ t y : ℝ)) : ℂ) = ((fdlPsiHat ψ 0 ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    exact integral_ofReal.symm
  exact_mod_cast h2


/-- Locality of the heat-damped Fourier series of `P φ_t` for small `t`. -/
theorem d1t_loc {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {η : ℝ} (hη : 0 < η) {y0 : Euc d} (i0 : Fin d)
    (hy0 : ∀ n : ℤ, η ≤ |y0 i0 - n|) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ η / 2 →
      |∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 *
          Torus.cosMode k (Torus.mk y0)| ≤ M := by
  obtain ⟨M1, hM1⟩ := d1t_theta_euc d (half_pos hη)
  refine ⟨M1 * fdlPsiHat ψ 0 ^ 2, fun ε hε hε1 t ht htη => ?_⟩
  set φt : Euc d → ℝ := fdlPhiScale ψ t with hφt
  have hnn : ∀ y, 0 ≤ φt y := d1t_phiScale_nonneg hψ ht
  have hint : Integrable φt := d1t_phiScale_int hψ ht
  have hZ : ∫ y, φt y = fdlPsiHat ψ 0 ^ 2 := d1t_phiScale_integral hψ ht
  have hcont : Continuous φt := (Per.per_phiScale_contDiff hψ t).continuous
  have hcs : HasCompactSupport φt := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) t) fun y hy => ?_
    refine Per.per_phiScale_zero hψ ht ?_
    rw [mem_closedBall_zero_iff] at hy
    exact (not_le.mp hy).le
  set e : Lattice d → ℝ := fun k => Real.exp (-ε * Lattice.enorm k ^ 2) with he
  let F : Lattice d → Euc d → ℂ := fun k y =>
    ((φt y : ℝ) : ℂ) * (((e k : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y)))
  have hFcont : ∀ k, Continuous (F k) := by
    intro k
    have h1 : Continuous fun y : Euc d => Torus.mode k (Torus.mk (y0 - y)) :=
      (Torus.continuous_mode k).comp (Torus.continuous_mk.comp (continuous_const.sub continuous_id))
    exact (Complex.continuous_ofReal.comp hcont).mul (continuous_const.mul h1)
  have hFint : ∀ k, Integrable (F k) := by
    intro k
    refine (hFcont k).integrable_of_hasCompactSupport ?_
    exact (hcs.comp_left Complex.ofReal_zero).mul_right
  have hFnorm : ∀ k y, ‖F k y‖ = e k * φt y := by
    intro k y
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mode,
      abs_of_nonneg (hnn y), mul_one]
    have : |e k| = e k := abs_of_pos (Real.exp_pos _)
    rw [this]
    ring
  have hFsum : Summable fun k => ∫ y, ‖F k y‖ := by
    simp_rw [hFnorm]
    simp_rw [integral_const_mul, hZ]
    exact (summable_gauss_lattice d ε hε).mul_right _
  have hHas := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hterm : ∀ k, ∫ y, F k y =
      ((e k * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) * Torus.mode k (Torus.mk y0) := by
    intro k
    have : ∀ y, F k y = ((e k : ℝ) : ℂ) * (((φt y : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y))) := by
      intro y; simp only [F]; ring
    simp_rw [this]
    rw [integral_const_mul, hφt, d1t_mode_integral hψ ht k y0]
    push_cast; ring
  have hre := Complex.reCLM.hasSum hHas
  have hre' : HasSum (fun k : Lattice d => e k * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 *
      Torus.cosMode k (Torus.mk y0)) (∫ y, ∑' k, F k y).re := by
    have h3 : (fun k : Lattice d => Complex.reCLM (∫ y, F k y)) = fun k : Lattice d =>
        e k * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 * Torus.cosMode k (Torus.mk y0) := by
      funext k
      rw [Complex.reCLM_apply, hterm k, Complex.re_ofReal_mul]
      rfl
    rw [h3] at hre
    simpa using hre
  show |∑' k : Lattice d, e k * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 *
      Torus.cosMode k (Torus.mk y0)| ≤ _
  rw [hre'.tsum_eq]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hsumF : ∀ y, ∑' k, F k y = ((φt y : ℝ) : ℂ) * ∑' k : Lattice d,
      ((e k : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y)) := fun y => tsum_mul_left
  simp_rw [hsumF]
  have hbd : ∀ y, ‖((φt y : ℝ) : ℂ) * ∑' k : Lattice d,
      ((e k : ℝ) : ℂ) * Torus.mode k (Torus.mk (y0 - y))‖ ≤ φt y * M1 := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn y)]
    rcases (hnn y).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hty : ‖y‖ < t := by
        by_contra hh
        have := Per.per_phiScale_zero hψ ht (not_lt.mp hh)
        rw [hφt] at hpos
        linarith
      refine mul_le_mul_of_nonneg_left (hM1 ε hε hε1 (y0 - y) ⟨i0, fun n => ?_⟩) hpos.le
      have h1 : |y i0| ≤ ‖y‖ := by
        have := PiLp.norm_apply_le y i0
        simpa using this
      have h2 : |y0 i0 - n| ≤ |y0 i0 - y i0 - n| + |y i0| := by
        calc |y0 i0 - n| = |(y0 i0 - y i0 - n) + y i0| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have h3 := hy0 n
      show η / 2 ≤ |y0 i0 - y i0 - n|
      linarith
  refine (norm_integral_le_of_norm_le (hint.mul_const M1) (ae_of_all _ hbd)).trans ?_
  rw [integral_mul_const, hZ]
  exact le_of_eq (mul_comm _ _)

end HRS.MC.D1T
