import HRS.Sections.ScrnAux15

/-!
# Packet SCRN, part 16: the covariance `Cov_Haar(f^0) + ∫ Σ̄` on the Fourier side

For transported tests `f_a^r` with `coeffOf (f_a^r) k = e^{-(t_a - r) λ_k} ψ̂_a(k)` (`0 ≤ r ≤ t_a`),
`Σ̄^{ac}_r = c ∫⟨∇f_a^r, ∇f_c^r⟩ 1_{r < t_a ∧ t_c}`, `c = 2β⁻¹`:

`Cov(f_a^0, f_c^0) + ∫_0^T Σ̄^{ac} = Re ∑_{k≠0} conj(ψ̂_a) ψ̂_c κ_k`, with
`κ_k = S_k e^{-|t_a-t_c| λ_k} + (1 - S_k) e^{-(t_a+t_c) λ_k}`, `S_k = β⁻¹(2π|k|)²/λ_k`
(`scrn_Q_formula`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE PDE.ClassicalAux

/-- The deterministic covariance density `Σ̄_r^{ab} = 1_{0 ≤ r < t_a ∧ t_b} c ∫ ⟨∇f_a^r, ∇f_b^r⟩`. -/
def scrnSigBar {p : ℕ} (ts : Fin p → ℝ) (f : Fin p → ℝ → Torus d → ℝ) (c : ℝ) (r : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => if 0 ≤ r ∧ r < min (ts a) (ts b) then
    c * ∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x) else 0

/-- The Fourier multiplier `κ_k` of the covariance. -/
def scrnKappa (invβ : ℝ) (lam : Lattice d → ℝ) (ta tc : ℝ) (k : Lattice d) : ℝ :=
  (invβ * (2 * Real.pi * Lattice.enorm k) ^ 2 / lam k) * Real.exp (-|ta - tc| * lam k) +
    (1 - invβ * (2 * Real.pi * Lattice.enorm k) ^ 2 / lam k) * Real.exp (-(ta + tc) * lam k)

lemma scrn_summable_cross {u v : Torus d → ℝ} (hu : Torus.IsCk 2 u) (hv : Torus.IsCk 2 v) :
    Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ 2 * (‖coeffOf u k‖ * ‖coeffOf v k‖) := by
  have h1 := (scrn_parseval_grad hu hu).summable
  have h2 := (scrn_parseval_grad hv hv).summable
  have e : ∀ (w : Torus d → ℝ) (k : Lattice d),
      (2 * Real.pi * Lattice.enorm k) ^ 2 * (conj (coeffOf w k) * coeffOf w k).re =
        (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖coeffOf w k‖ ^ 2 := by
    intro w k
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((h1.add h2).mul_left (1 / 2))
  have := e u k
  have := e v k
  nlinarith [sq_nonneg (‖coeffOf u k‖ - ‖coeffOf v k‖), sq_nonneg (2 * Real.pi * Lattice.enorm k)]

lemma scrn_re_scale {x y : ℝ} {A B C D : ℂ} (hA : A = (x : ℂ) * C) (hB : B = (y : ℂ) * D) :
    (conj A * B).re = x * y * (conj C * D).re := by
  rw [hA, hB]
  have : conj ((x : ℂ) * C) * ((y : ℂ) * D) = ((x * y : ℝ) : ℂ) * (conj C * D) := by
    simp only [map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.re_ofReal_mul]

lemma scrn_time_int {lam ta tc : ℝ} (hlam : 0 < lam) (hta : 0 ≤ ta) (htc : 0 ≤ tc) :
    ∫ r in (0 : ℝ)..min ta tc, Real.exp (-(ta - r) * lam) * Real.exp (-(tc - r) * lam) =
      (Real.exp (-|ta - tc| * lam) - Real.exp (-(ta + tc) * lam)) / (2 * lam) := by
  have hm : 0 ≤ min ta tc := le_min hta htc
  have e1 : ∀ r : ℝ, Real.exp (-(ta - r) * lam) * Real.exp (-(tc - r) * lam) =
      Real.exp (-(ta + tc) * lam) * (1 / (2 * lam)) * (2 * lam * Real.exp (2 * lam * r)) := by
    intro r
    rw [← Real.exp_add]
    field_simp
    rw [← Real.exp_add]
    congr 1; ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, scrn_int_exp lam _ hm]
  have e2 : Real.exp (-(ta + tc) * lam) * Real.exp (2 * lam * min ta tc) =
      Real.exp (-|ta - tc| * lam) := by
    rw [← Real.exp_add]; congr 1
    rcases le_total ta tc with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have : Real.exp (-(ta + tc) * lam) * (1 / (2 * lam)) * (Real.exp (2 * lam * min ta tc) - 1) =
      (Real.exp (-|ta - tc| * lam) - Real.exp (-(ta + tc) * lam)) / (2 * lam) := by
    rw [← e2]; ring
  exact this

lemma scrn_cont_of_ck2 {g : Torus d → ℝ} (hg : Torus.IsCk 2 g) : Continuous g :=
  KernelGrad.isCk_continuous (hg.of_le (by norm_num))

/-- The covariance of the transported tests plus the integrated covariance density, on the Fourier
side. -/
theorem scrn_Q_formula {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, 0 ≤ ts a) {T : ℝ}
    (hT : ∀ a, ts a ≤ T) (invβ : ℝ) (lam : Lattice d → ℝ) (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam : ∀ k, k ≠ 0 → 0 < lam k) (ψ : Fin p → Torus d → ℝ) (hψ : ∀ a, Torus.IsCk 2 (ψ a))
    (f : Fin p → ℝ → Torus d → ℝ) (hf2 : ∀ a, ∀ r ∈ Icc 0 (ts a), Torus.IsCk 2 (f a r))
    (hfc : ∀ a, ∀ r ∈ Icc 0 (ts a), ∀ k,
      coeffOf (f a r) k = ((Real.exp (-(ts a - r) * lam k) : ℝ) : ℂ) * coeffOf (ψ a) k)
    (a c : Fin p) :
    HasSum (fun k : Lattice d => if k = 0 then (0 : ℝ) else
        (conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re * scrnKappa invβ lam (ts a) (ts c) k)
      ((∫ x, (f a 0 x - ∫ y, f a 0 y) * (f c 0 x - ∫ y, f c 0 y)) +
        ∫ r in Icc 0 T, scrnSigBar ts f (2 * invβ) r a c) := by
  set ta := ts a with hta
  set tc := ts c with htc
  have hta0 : 0 ≤ ta := hts a
  have htc0 : 0 ≤ tc := hts c
  set m := min ta tc with hm
  have hm0 : 0 ≤ m := le_min hta0 htc0
  have hmT : m ≤ T := (min_le_left _ _).trans (hT a)
  have h0a : (0 : ℝ) ∈ Icc 0 ta := ⟨le_rfl, hta0⟩
  have h0c : (0 : ℝ) ∈ Icc 0 tc := ⟨le_rfl, htc0⟩
  -- the covariance part
  have hPar := scrn_parseval_re (scrn_cont_of_ck2 (hf2 a 0 h0a)) (scrn_cont_of_ck2 (hf2 c 0 h0c))
  have hmean : ∀ b, coeffOf (f b 0) 0 = (((∫ x, f b 0 x : ℝ)) : ℂ) := fun b =>
    MFApriori.coeffOf_zero_eq_integral' _
  have hcovEq : (∫ x, (f a 0 x - ∫ y, f a 0 y) * (f c 0 x - ∫ y, f c 0 y)) =
      (∫ x, f a 0 x * f c 0 x) - (∫ y, f a 0 y) * (∫ y, f c 0 y) := by
    have hia : Integrable (f a 0) := (scrn_cont_of_ck2 (hf2 a 0 h0a)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hic : Integrable (f c 0) := (scrn_cont_of_ck2 (hf2 c 0 h0c)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hiac : Integrable (fun x => f a 0 x * f c 0 x) :=
      ((scrn_cont_of_ck2 (hf2 a 0 h0a)).mul (scrn_cont_of_ck2 (hf2 c 0 h0c))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have e : ∀ x, (f a 0 x - ∫ y, f a 0 y) * (f c 0 x - ∫ y, f c 0 y) =
        f a 0 x * f c 0 x - (∫ y, f c 0 y) * f a 0 x - (∫ y, f a 0 y) * f c 0 x +
          (∫ y, f a 0 y) * (∫ y, f c 0 y) := fun x => by ring
    simp_rw [e]
    rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul]
    · simp; ring
    · exact hiac
    · exact hia.const_mul _
    · exact hiac.sub (hia.const_mul _)
    · exact hic.const_mul _
    · exact (hiac.sub (hia.const_mul _)).sub (hic.const_mul _)
    · exact integrable_const _
  have hcovHas : HasSum (fun k : Lattice d => if k = 0 then (0 : ℝ) else
      (conj (coeffOf (f a 0) k) * coeffOf (f c 0) k).re)
      ((∫ x, f a 0 x * f c 0 x) - (∫ y, f a 0 y) * (∫ y, f c 0 y)) := by
    have h1 := hasSum_ite_eq (0 : Lattice d) ((conj (coeffOf (f a 0) 0) * coeffOf (f c 0) 0).re)
    have h2 := hPar.sub h1
    have e0 : (conj (coeffOf (f a 0) 0) * coeffOf (f c 0) 0).re =
        (∫ y, f a 0 y) * (∫ y, f c 0 y) := by
      rw [hmean a, hmean c]
      simp [Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [e0] at h2
    convert h2 using 1
    funext k
    by_cases hk : k = 0
    · subst hk; simp [e0]
    · simp [hk]
  have hcov2 : HasSum (fun k : Lattice d => if k = 0 then (0 : ℝ) else
      (conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re * Real.exp (-(ta + tc) * lam k))
      ((∫ x, (f a 0 x - ∫ y, f a 0 y) * (f c 0 x - ∫ y, f c 0 y))) := by
    rw [hcovEq]
    convert hcovHas using 1
    funext k
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk, if_neg hk]
      rw [scrn_re_scale (hfc a 0 h0a k) (hfc c 0 h0c k)]
      simp only [sub_zero]
      have h3 : Real.exp (-ts a * lam k) * Real.exp (-ts c * lam k) =
          Real.exp (-(ta + tc) * lam k) := by
        rw [← Real.exp_add]; congr 1; simp only [hta, htc]; ring
      rw [← h3]; ring
  -- the integrated covariance density
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = 2 * invβ := ⟨_, rfl⟩
  rw [← hc0]
  set G : ℝ → ℝ := fun r => ∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f c r) x) with hG
  have hIntEq : ∫ r in Icc 0 T, scrnSigBar ts f c0 r a c = ∫ r in (0 : ℝ)..m, c0 * G r := by
    have e : ∀ r, scrnSigBar ts f c0 r a c = (Ico 0 m).indicator (fun r => c0 * G r) r := by
      intro r
      unfold scrnSigBar
      simp only [Matrix.of_apply]
      by_cases h : 0 ≤ r ∧ r < min (ts a) (ts c)
      · rw [if_pos h, Set.indicator_of_mem (show r ∈ Ico 0 m from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show r ∉ Ico 0 m from h)]
    simp_rw [e]
    rw [setIntegral_indicator measurableSet_Ico]
    have : Icc 0 T ∩ Ico 0 m = Ico 0 m := by
      ext r; simp only [mem_inter_iff, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, (h2.trans_le hmT).le⟩, h1, h2⟩
    rw [this, intervalIntegral.integral_of_le hm0, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo]
  have hsum := scrn_summable_cross (hψ a) (hψ c)
  set B : Lattice d → ℝ := fun k => |c0| * ((2 * Real.pi * Lattice.enorm k) ^ 2 *
    (‖coeffOf (ψ a) k‖ * ‖coeffOf (ψ c) k‖)) with hB
  have hBs : Summable B := hsum.mul_left _
  set F : Lattice d → ℝ → ℝ := fun k r => c0 * ((2 * Real.pi * Lattice.enorm k) ^ 2 *
    ((conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re *
      (Real.exp (-(ta - r) * lam k) * Real.exp (-(tc - r) * lam k)))) with hF
  have hTime : HasSum (fun k : Lattice d => ∫ r in (0 : ℝ)..m, F k r) (∫ r in (0 : ℝ)..m, c0 * G r) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => B k) ?_ ?_ ?_ ?_ ?_
    · intro k
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      fun_prop
    · intro k
      refine Filter.Eventually.of_forall fun r hr => ?_
      rw [uIoc_of_le hm0] at hr
      have hra : r ≤ ta := hr.2.trans (min_le_left _ _)
      have hrc : r ≤ tc := hr.2.trans (min_le_right _ _)
      have e1 : Real.exp (-(ta - r) * lam k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [hlam0 k])
      have e2 : Real.exp (-(tc - r) * lam k) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [hlam0 k])
      have e3 : Real.exp (-(ta - r) * lam k) * Real.exp (-(tc - r) * lam k) ≤ 1 := by
        have := Real.exp_pos (-(ta - r) * lam k)
        have := Real.exp_pos (-(tc - r) * lam k)
        nlinarith
      have e4 : 0 ≤ Real.exp (-(ta - r) * lam k) * Real.exp (-(tc - r) * lam k) := by positivity
      have e5 : |(conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re| ≤
          ‖coeffOf (ψ a) k‖ * ‖coeffOf (ψ c) k‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, RCLike.norm_conj]
      simp only [hF, hB, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi * Lattice.enorm k) ^ 2),
        abs_of_nonneg e4]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |(conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re| *
            (Real.exp (-(ta - r) * lam k) * Real.exp (-(tc - r) * lam k))
          ≤ |(conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re| * 1 :=
            mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact e5
    · exact Filter.Eventually.of_forall fun r _ => hBs
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun r hr => ?_
      rw [uIoc_of_le hm0] at hr
      have hra : r ∈ Icc 0 ta := ⟨hr.1.le, hr.2.trans (min_le_left _ _)⟩
      have hrc : r ∈ Icc 0 tc := ⟨hr.1.le, hr.2.trans (min_le_right _ _)⟩
      have hP := scrn_parseval_grad (hf2 a r hra) (hf2 c r hrc)
      have hP2 : HasSum (fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ 2 *
          ((conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re *
            (Real.exp (-(ta - r) * lam k) * Real.exp (-(tc - r) * lam k)))) (G r) := by
        convert hP using 1
        funext k
        rw [scrn_re_scale (hfc a r hra k) (hfc c r hrc k)]
        ring
      exact hP2.mul_left c0
  have hper : ∀ k : Lattice d, ∫ r in (0 : ℝ)..m, F k r =
      if k = 0 then 0 else c0 * ((2 * Real.pi * Lattice.enorm k) ^ 2 *
        ((conj (coeffOf (ψ a) k) * coeffOf (ψ c) k).re *
          ((Real.exp (-|ta - tc| * lam k) - Real.exp (-(ta + tc) * lam k)) / (2 * lam k)))) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h0 : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm Lattice.toEuc
        rw [show (WithLp.toLp 2 fun i => (((0 : Lattice d) i : ℤ) : ℝ)) = (0 : Euc d) from by
          ext i; simp]
        simp
      simp [hF, h0]
    · rw [if_neg hk]
      simp only [hF]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      rw [scrn_time_int (hlam k hk) hta0 htc0]
  have hTot := hcov2.add hTime
  rw [hIntEq]
  convert hTot using 1
  funext k
  rw [hper k]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, if_neg hk, if_neg hk]
    have hl := hlam k hk
    unfold scrnKappa
    rw [hc0]
    field_simp
    ring

end HRS
