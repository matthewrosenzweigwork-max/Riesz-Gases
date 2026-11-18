import HRS.Uniform.Q12P17

/-!
# Q12, Peyre part 18: the Poisson solution on the torus and its Dirichlet energy

For smooth probability densities `f, g` there is a smooth `u` with `Δu = g - f` and
`∫ u (f - g) = hmSum f g / (4π²)`.
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_isSmooth_toFun (c : PDE.Coeff d) (hreal : PDE.IsRealCoeff c)
    (hdec : ∀ N : ℕ, PDE.MemHs (N : ℝ) c) : Torus.IsSmooth (PDE.toFun c) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_infty]
  intro n
  have hm : (d : ℝ) / 2 + n < ((⌈(d : ℝ) / 2 + n⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil ((d : ℝ) / 2 + n)
    push_cast; linarith
  obtain ⟨C, hC⟩ := PDE.toFun_isCk_le (d := d) n ((⌈(d : ℝ) / 2 + n⌉₊ + 1 : ℕ) : ℝ) hm
  exact (hC c (hdec _) hreal).1

lemma q12_cont_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).continuous

/-- The Fourier multiplier `-(4π²|k|²)⁻¹` applied to the coefficients of `h`. -/
def poissonC (h : Torus d → ℝ) : PDE.Coeff d :=
  fun k => -(((4 * π ^ 2 * Lattice.enorm k ^ 2)⁻¹ : ℝ) : ℂ) * PDE.coeffOf h k

lemma q12_inv_le_one {k : Lattice d} (hk : k ≠ 0) : (4 * π ^ 2 * Lattice.enorm k ^ 2)⁻¹ ≤ 1 := by
  have h1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk
  have h2 : 1 ≤ π := by linarith [Real.pi_gt_three]
  have h4 : 1 ≤ π ^ 2 := by nlinarith
  have h5 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
  have h6 := mul_le_mul h4 h5 zero_le_one (by positivity : (0 : ℝ) ≤ π ^ 2)
  have h3 : 1 ≤ 4 * π ^ 2 * Lattice.enorm k ^ 2 := by nlinarith
  exact inv_le_one_of_one_le₀ h3

theorem q12_poisson {f g : Torus d → ℝ} (hf : IsProbDensity f) (hg : IsProbDensity g)
    (hfs : Torus.IsSmooth f) (hgs : Torus.IsSmooth g) :
    ∃ u : Torus d → ℝ, Torus.IsSmooth u ∧ (∀ x, Torus.laplacian u x = g x - f x) ∧
      ∫ x, u x * (f x - g x) = hmSum f g / (4 * π ^ 2) := by
  have hcf := q12_cont_of_smooth hfs
  have hcg := q12_cont_of_smooth hgs
  set h : Torus d → ℝ := fun x => g x - f x with hh
  have hhs : Torus.IsSmooth h := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => g (Torus.mk y) - f (Torus.mk y))
    exact (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) from hgs).sub
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hfs)
  have hch : Continuous h := hcg.sub hcf
  -- coefficients of `h`
  have hcoef : ∀ k, PDE.coeffOf h k = Torus.fcoef g k - Torus.fcoef f k := by
    intro k
    rw [PDE.coeffOf_eq_fcoef]
    unfold Torus.fcoef
    rw [← integral_sub]
    · congr 1; funext x; simp only [hh]; push_cast; ring
    · exact ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hcg)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hcf)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hc0 : PDE.coeffOf h 0 = 0 := by
    rw [hcoef, Torus.fcoef_zero, Torus.fcoef_zero]
    simp [Torus.mean, hf.integral_one, hg.integral_one]
  have hreal_h : PDE.IsRealCoeff (PDE.coeffOf h) :=
    PDE.isRealCoeff_coeffOf h (hch.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hmem_h : ∀ m : ℝ, PDE.MemHs m (PDE.coeffOf h) := fun m =>
    PDE.MFSemigroup.memHs_of_isSmooth hhs m
  set c : PDE.Coeff d := poissonC h with hc
  have hnorm_c : ∀ k, ‖c k‖ ≤ ‖PDE.coeffOf h k‖ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [hc, poissonC, hc0]
    · simp only [hc, poissonC, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ (4 * π ^ 2 * Lattice.enorm k ^ 2)⁻¹ := by positivity
      rw [abs_of_nonneg h0]
      calc _ ≤ 1 * ‖PDE.coeffOf h k‖ := mul_le_mul_of_nonneg_right (q12_inv_le_one hk) (norm_nonneg _)
        _ = _ := one_mul _
  have hreal_c : PDE.IsRealCoeff c := by
    intro k
    simp only [hc, poissonC]
    rw [hreal_h k, q12_enorm_neg, map_mul, map_neg, Complex.conj_ofReal]
  have hmem_c : ∀ m : ℝ, PDE.MemHs m c := by
    intro m
    refine Summable.of_nonneg_of_le (fun k => by unfold PDE.sobWeight; positivity) (fun k => ?_) (hmem_h m)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm_c k) 2)
      (by unfold PDE.sobWeight; positivity)
  have hsum_c : Summable fun k => ‖c k‖ :=
    PDE.summable_norm_of_memHs ((d : ℝ) / 2 + 1) (by linarith) c (hmem_c _)
  have hsum_h : Summable fun k => ‖PDE.coeffOf h k‖ :=
    PDE.summable_norm_of_memHs ((d : ℝ) / 2 + 1) (by linarith) _ (hmem_h _)
  set u : Torus d → ℝ := PDE.toFun c with hu
  have hus : Torus.IsSmooth u := q12_isSmooth_toFun c hreal_c fun N => hmem_c _
  have hcu : PDE.coeffOf u = c := PDE.coeffOf_toFun c hreal_c hsum_c
  have hu2 : Torus.IsCk 2 u := by
    have := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift u) from hus).of_le q12_two_le_top
    exact this
  have hcu1 : Torus.IsCk 1 u := hu2.of_le (by norm_num)
  -- Δu = h
  have hlapc : Continuous (Torus.laplacian u) := by
    have : Torus.laplacian u = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j u) x :=
      funext (PDE.laplacian_eq_sum u hu2)
    rw [this]
    exact continuous_finset_sum _ fun j _ =>
      PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j u hu2)
  have hcoef_lap : PDE.coeffOf (Torus.laplacian u) = PDE.coeffOf h := by
    rw [PDE.coeffOf_laplacian u hu2, hcu]
    funext k
    simp only [PDE.laplaceCoeff, hc, poissonC]
    by_cases hk : k = 0
    · subst hk; simp [hc0]
    · have hne : (4 * π ^ 2 * Lattice.enorm k ^ 2 : ℝ) ≠ 0 := by
        have h1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk
        have h2 : (0 : ℝ) < π := Real.pi_pos
        positivity
      have : ((4 * π ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
      have hen : (Lattice.enorm k : ℂ) ≠ 0 := by
        have h1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk
        exact_mod_cast (by linarith : Lattice.enorm k ≠ 0)
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast at this ⊢
      field_simp
  have hlap : ∀ x, Torus.laplacian u x = g x - f x := by
    intro x
    have h1 := PDE.toFun_coeffOf (Torus.laplacian u) hlapc (by simpa [hcoef_lap] using hsum_h)
    have h2 := PDE.toFun_coeffOf h hch hsum_h
    have := h1.symm.trans ((congrArg PDE.toFun hcoef_lap).trans h2)
    exact congrFun this x
  refine ⟨u, hus, hlap, ?_⟩
  -- energy via Parseval
  have hcu_cont : Continuous u := q12_cont_of_smooth hus
  have hmu : MemLp (fun x => (u x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hcu_cont).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmh : MemLp (fun x => (h x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hch).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := PDE.hasSum_parseval (fun x => (u x : ℂ)) (fun x => (h x : ℂ)) hmu hmh
  have hterm : ∀ n : Lattice d,
      conj (Torus.funFourierCoeff (fun x => (u x : ℂ)) n) * Torus.funFourierCoeff (fun x => (h x : ℂ)) n =
        ((-((4 * π ^ 2 * Lattice.enorm n ^ 2)⁻¹ * ‖PDE.coeffOf h n‖ ^ 2) : ℝ) : ℂ) := by
    intro n
    have e1 : Torus.funFourierCoeff (fun x => (u x : ℂ)) n = c n := by
      rw [← hcu]; rfl
    have e2 : Torus.funFourierCoeff (fun x => (h x : ℂ)) n = PDE.coeffOf h n := rfl
    rw [e1, e2]
    simp only [hc, poissonC, map_mul, map_neg, Complex.conj_ofReal]
    have : conj (PDE.coeffOf h n) * PDE.coeffOf h n = ((‖PDE.coeffOf h n‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      push_cast; rfl
    push_cast
    rw [show -(((4 * π ^ 2 * Lattice.enorm n ^ 2 : ℂ))⁻¹) * conj (PDE.coeffOf h n) * PDE.coeffOf h n =
      -((4 * π ^ 2 * Lattice.enorm n ^ 2 : ℂ))⁻¹ * (conj (PDE.coeffOf h n) * PDE.coeffOf h n) by ring]
    push_cast at this
    rw [this]; ring
  have hint : ∫ t, conj ((fun x => (u x : ℂ)) t) * (fun x => (h x : ℂ)) t = ((∫ x, u x * h x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal (μ := volume) (f := fun x => u x * h x)]
    congr 1; funext t
    simp [Complex.conj_ofReal]
  simp_rw [hterm, hint] at hP
  have hP' : HasSum (fun n : Lattice d => -((4 * π ^ 2 * Lattice.enorm n ^ 2)⁻¹ * ‖PDE.coeffOf h n‖ ^ 2))
      (∫ x, u x * h x) := Complex.hasSum_ofReal.mp hP
  have hP2 := hP'.neg
  simp only [neg_neg] at hP2
  have hE : ∫ x, u x * (f x - g x) = -∫ x, u x * h x := by
    rw [← integral_neg]; congr 1; funext x; simp only [hh]; ring
  rw [hE, ← hP2.tsum_eq]
  unfold hmSum
  rw [div_eq_inv_mul, ← tsum_mul_left]
  congr 1; funext k
  by_cases hk : k = 0
  · subst hk; simp [hc0]
  · rw [if_neg hk, hcoef, norm_sub_rev]
    have : (4 * π ^ 2 * Lattice.enorm k ^ 2)⁻¹ = (4 * π ^ 2)⁻¹ * (Lattice.enorm k ^ 2)⁻¹ := by
      rw [mul_inv]
    rw [this]; ring

end HRS.Uniform.Q12
