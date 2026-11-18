import HRS.Main.HeadlineEdgeworth

/-!
# Packet CC1: proof of `ccd_smooth_density_of_bound` (Fourier reconstruction)

Statement copied verbatim from `HRS/MC/CrossCovSpec.lean`.  Route: `c_k = L (realMode k)`, `|c_k| ≤ C_N jp(k)^{-N}`,
`χ = ∑ c_k realMode k` smooth by the decay, `∫ ψ χ = ∑ ψ̂_k c_k` by termwise integration, and
`L ψ = ∑ ψ̂_k c_k` because the partial sums `mean ψ + ∑_{k ∈ F} ψ̂_k e_k` converge to `ψ` in `L²` (`N = 0`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

/-! ### CCD1: Fourier reconstruction -/

theorem p_cc1_smooth_const (c : ℝ) : Torus.IsSmooth (fun _ : Torus d => c) := by
  unfold Torus.IsSmooth Torus.IsCk
  exact contDiff_const

theorem p_cc1_smooth_add {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (f + g) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.add hg

theorem p_cc1_smooth_sub {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x - g x) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.sub hg

theorem p_cc1_smooth_smul (a : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Torus.IsSmooth (a • f) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.const_smul a

theorem p_cc1_smooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) :=
  StaticLimitAux.isSmooth_realMode' k

theorem p_cc1_cd_realMode (k : NonzeroLattice d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode k)) :=
  StaticLimitAux.isSmooth_realMode' k

theorem p_cc1_cd_of_smooth {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) := hψ

/-- The partial sum `m + ∑_{k ∈ F} a_k e_k`. -/
def p_cc1_trig (m : ℝ) (a : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) : Torus d → ℝ :=
  fun x => m + ∑ k ∈ F, a k * Torus.realMode k x

theorem p_cc1_smooth_trig (m : ℝ) (a : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) :
    Torus.IsSmooth (p_cc1_trig m a F) := by
  unfold p_cc1_trig Torus.IsSmooth Torus.IsCk
  have : Torus.lift (fun x => m + ∑ k ∈ F, a k * Torus.realMode k x) =
      fun y => m + ∑ k ∈ F, a k * Torus.lift (Torus.realMode k) y := rfl
  rw [this]
  refine contDiff_const.add (ContDiff.sum fun k _ => ?_)
  exact (p_cc1_cd_realMode k).const_smul (a k)

theorem p_cc1_coeff_realMode (k j : NonzeroLattice d) :
    Torus.funRealCoeff (Torus.realMode k : Torus d → ℝ) j = if j = k then 1 else 0 := by
  unfold Torus.funRealCoeff
  rw [Torus.realMode_orthonormal j k]

theorem p_cc1_snorm_realMode (N : ℕ) (k : NonzeroLattice d) :
    HRS.sobolevNorm (-(N : ℝ)) (Torus.realMode k) = Lattice.jp k.1 ^ (-(N : ℝ)) := by
  unfold HRS.sobolevNorm
  have hm : Torus.mean (Torus.realMode k : Torus d → ℝ) = 0 := Torus.integral_realMode k
  rw [hm]
  simp_rw [p_cc1_coeff_realMode k]
  rw [tsum_eq_single k]
  · rw [← Torus.jp_rpow_sq]
    simp only [↓reduceIte]
    simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [zero_add, Real.sqrt_sq (Real.rpow_nonneg (Torus.jp_pos _).le _)]
  · intro j hj
    simp [hj]

theorem p_cc1_snorm_zero (φ : Torus d → ℝ) :
    HRS.sobolevNorm (-((0 : ℕ) : ℝ)) φ =
      Real.sqrt ((Torus.mean φ) ^ 2 + ∑' k : NonzeroLattice d, Torus.funRealCoeff φ k ^ 2) := by
  unfold HRS.sobolevNorm
  simp

theorem p_cc1_tail (w : NonzeroLattice d → ℝ) (hw : Summable w) :
    Tendsto (fun F : Finset (NonzeroLattice d) => ∑' k, (if k ∈ F then 0 else w k)) atTop (𝓝 0) := by
  classical
  have e : ∀ F : Finset (NonzeroLattice d),
      ∑' k, (if k ∈ F then 0 else w k) = (∑' k, w k) - ∑ k ∈ F, w k := by
    intro F
    have hF : Summable (fun k => if k ∈ F then w k else 0) :=
      summable_of_ne_finset_zero (s := F) fun k hk => by simp [hk]
    have h1 : (fun k => if k ∈ F then (0 : ℝ) else w k) = fun k => w k - (if k ∈ F then w k else 0) := by
      funext k; by_cases hk : k ∈ F <;> simp [hk]
    rw [h1, hw.tsum_sub hF]
    congr 1
    rw [tsum_eq_sum (s := F) (fun k hk => by simp [hk])]
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  simp_rw [e]
  have := (tendsto_const_nhds (x := ∑' k, w k)).sub hw.hasSum
  simpa using this

/-- Coefficients of `ψ - (mean ψ + S_F ψ)`. -/
theorem p_cc1_coeff_remainder {ψ : Torus d → ℝ} (hψ : Continuous ψ) (F : Finset (NonzeroLattice d))
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => ψ x - p_cc1_trig (Torus.mean ψ) (fun j => Torus.funRealCoeff ψ j) F x) k =
      Torus.funRealCoeff ψ k - (if k ∈ F then Torus.funRealCoeff ψ k else 0) := by
  classical
  set c : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff ψ j with hc
  unfold Torus.funRealCoeff
  have hint : ∀ {φ : Torus d → ℝ}, Continuous φ → Integrable φ := fun hφ =>
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hik : ∀ {φ : Torus d → ℝ}, Continuous φ → Integrable (fun x => Torus.realMode k x * φ x) :=
    fun hφ => hint ((Torus.continuous_realMode k).mul hφ)
  have h1 : ∀ x, Torus.realMode k x * (ψ x - p_cc1_trig (Torus.mean ψ) c F x) =
      Torus.realMode k x * ψ x - Torus.mean ψ * Torus.realMode k x -
        ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x) := by
    intro x
    unfold p_cc1_trig
    rw [mul_sub, mul_add, Finset.mul_sum]
    have : ∑ j ∈ F, Torus.realMode k x * (c j * Torus.realMode j x) =
        ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  simp_rw [h1]
  have i1 : Integrable (fun x => Torus.realMode k x * ψ x) := hik hψ
  have i2 : Integrable (fun x => Torus.mean ψ * Torus.realMode k x) :=
    (hint (Torus.continuous_realMode k)).const_mul _
  have i3 : Integrable (fun x => ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x)) :=
    integrable_finsetSum _ fun j _ => (hik (Torus.continuous_realMode j)).const_mul _
  have e1 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.realMode k x * ψ x - Torus.mean ψ * Torus.realMode k x)
    (g := fun x => ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x)) (i1.sub i2) i3
  have e2 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.realMode k x * ψ x) (g := fun x => Torus.mean ψ * Torus.realMode k x) i1 i2
  rw [e1, e2, integral_const_mul, Torus.integral_realMode,
    integral_finsetSum _ fun j _ => (hik (Torus.continuous_realMode j)).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal k]
  simp [Finset.sum_ite_eq]
  rfl

theorem p_cc1_mean_remainder {ψ : Torus d → ℝ} (hψ : Continuous ψ) (F : Finset (NonzeroLattice d))
    (a : NonzeroLattice d → ℝ) :
    Torus.mean (fun x => ψ x - p_cc1_trig (Torus.mean ψ) a F x) = 0 := by
  have hint : ∀ {φ : Torus d → ℝ}, Continuous φ → Integrable φ := fun hφ =>
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable ψ := hint hψ
  have i3 : Integrable (fun x => ∑ k ∈ F, a k * Torus.realMode k x) :=
    integrable_finsetSum _ fun j _ => (hint (Torus.continuous_realMode j)).const_mul _
  have h2 : ∫ x : Torus d, ∑ k ∈ F, a k * Torus.realMode k x = 0 := by
    rw [integral_finsetSum _ fun j _ => (hint (Torus.continuous_realMode j)).const_mul _]
    simp [integral_const_mul, Torus.integral_realMode]
  have e0 : ∀ x, ψ x - p_cc1_trig (Torus.mean ψ) a F x =
      (ψ x - Torus.mean ψ) - ∑ k ∈ F, a k * Torus.realMode k x := by
    intro x; unfold p_cc1_trig; ring
  have hmm : Torus.mean (fun x => ψ x - p_cc1_trig (Torus.mean ψ) a F x) =
      ∫ x : Torus d, (ψ x - p_cc1_trig (Torus.mean ψ) a F x) := rfl
  rw [hmm]
  simp_rw [e0]
  have hi : Integrable (fun x => ψ x - Torus.mean ψ) := i1.sub (integrable_const _)
  rw [integral_sub hi i3, integral_sub i1 (integrable_const _), h2]
  simp [Torus.mean]

/-- `L` on the partial sums. -/
theorem p_cc1_L_trig (L : (Torus d → ℝ) → ℝ)
    (hadd : ∀ ψ ψ' : Torus d → ℝ, Torus.IsSmooth ψ → Torus.IsSmooth ψ' → L (ψ + ψ') = L ψ + L ψ')
    (hsmul : ∀ (c : ℝ) (ψ : Torus d → ℝ), Torus.IsSmooth ψ → L (c • ψ) = c * L ψ)
    (hconst : ∀ c : ℝ, L (fun _ => c) = 0) (m : ℝ) (a : NonzeroLattice d → ℝ)
    (F : Finset (NonzeroLattice d)) :
    L (p_cc1_trig m a F) = ∑ k ∈ F, a k * L (Torus.realMode k) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have : p_cc1_trig m a ∅ = fun _ => m := by
      funext x; simp [p_cc1_trig]
    rw [this, hconst]; simp
  | insert j F hj ih =>
    have : p_cc1_trig m a (insert j F) = p_cc1_trig m a F + a j • Torus.realMode j := by
      funext x
      simp only [p_cc1_trig, Finset.sum_insert hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, hadd _ _ (p_cc1_smooth_trig m a F) (p_cc1_smooth_smul _ (p_cc1_smooth_realMode j)),
      hsmul _ _ (p_cc1_smooth_realMode j), ih, Finset.sum_insert hj]
    ring

theorem p_cc1_summable_sq {ψ : Torus d → ℝ} (hψ : Continuous ψ)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖) :
    Summable fun k : NonzeroLattice d => Torus.funRealCoeff ψ k ^ 2 := by
  have hint : Integrable ψ := hψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := Torus.summable_norm_funRealCoeff hint hs
  have h2 : Tendsto (fun k : NonzeroLattice d => |Torus.funRealCoeff ψ k|) cofinite (𝓝 0) :=
    h1.tendsto_cofinite_zero
  have h3 : ∀ᶠ k : NonzeroLattice d in cofinite, |Torus.funRealCoeff ψ k| ≤ 1 :=
    h2.eventually (ge_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually h1 ?_
  filter_upwards [h3] with k hk
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg (Torus.funRealCoeff ψ k)]

/-- `L ψ = ∑ ψ̂_k L(e_k)` for smooth `ψ`, using only the `N = 0` bound. -/
theorem p_cc1_hasSum (L : (Torus d → ℝ) → ℝ)
    (hadd : ∀ ψ ψ' : Torus d → ℝ, Torus.IsSmooth ψ → Torus.IsSmooth ψ' → L (ψ + ψ') = L ψ + L ψ')
    (hsmul : ∀ (c : ℝ) (ψ : Torus d → ℝ), Torus.IsSmooth ψ → L (c • ψ) = c * L ψ)
    (hconst : ∀ c : ℝ, L (fun _ => c) = 0) (C : ℝ)
    (hC : ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ → |L ψ| ≤ C * HRS.sobolevNorm (-((0 : ℕ) : ℝ)) ψ)
    {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff ψ k * L (Torus.realMode k)) (L ψ) := by
  classical
  have hψc : Continuous ψ := Torus.continuous_of_continuous_lift (p_cc1_cd_of_smooth hψ).continuous
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift ψ) := contDiff_infty.mp (p_cc1_cd_of_smooth hψ)
  have hs : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := Torus.summable_fcoef_of_contDiff hd
  have hsq := p_cc1_summable_sq hψc hs
  set a : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff ψ j with ha
  set φ : Finset (NonzeroLattice d) → Torus d → ℝ :=
    fun F x => ψ x - p_cc1_trig (Torus.mean ψ) a F x with hφ
  have hφs : ∀ F, Torus.IsSmooth (φ F) := fun F => p_cc1_smooth_sub hψ (p_cc1_smooth_trig _ a F)
  have hsplit : ∀ F, L ψ = L (p_cc1_trig (Torus.mean ψ) a F) + L (φ F) := by
    intro F
    rw [← hadd _ _ (p_cc1_smooth_trig _ a F) (hφs F)]
    congr 1
    funext x; simp [hφ]
  have hpart : ∀ F : Finset (NonzeroLattice d),
      ∑ k ∈ F, Torus.funRealCoeff ψ k * L (Torus.realMode k) = L (p_cc1_trig (Torus.mean ψ) a F) := by
    intro F
    rw [p_cc1_L_trig L hadd hsmul hconst]
  have hnorm : ∀ F, HRS.sobolevNorm (-((0 : ℕ) : ℝ)) (φ F) =
      Real.sqrt (∑' k, (if k ∈ F then 0 else a k ^ 2)) := by
    intro F
    rw [p_cc1_snorm_zero, show Torus.mean (φ F) = 0 from p_cc1_mean_remainder hψc F a]
    congr 1
    rw [zero_pow two_ne_zero, zero_add]
    refine tsum_congr fun k => ?_
    have := p_cc1_coeff_remainder hψc F k
    simp only [hφ] at this ⊢
    rw [this]
    by_cases hk : k ∈ F <;> simp [hk, ha]
  have htail := p_cc1_tail (fun k => a k ^ 2) hsq
  have hsqrt : Tendsto (fun F : Finset (NonzeroLattice d) =>
      Real.sqrt (∑' k, (if k ∈ F then 0 else a k ^ 2))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp htail
    rw [Real.sqrt_zero] at h
    exact h
  have hbound : Tendsto (fun F : Finset (NonzeroLattice d) =>
      |C| * Real.sqrt (∑' k, (if k ∈ F then 0 else a k ^ 2))) atTop (𝓝 0) := by
    simpa using hsqrt.const_mul |C|
  unfold HasSum
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun F => dist_nonneg) (fun F => ?_) hbound
  rw [hpart F, Real.dist_eq]
  have h1 := hC _ (hφs F)
  rw [hnorm F] at h1
  have h2 : L (p_cc1_trig (Torus.mean ψ) a F) - L ψ = - L (φ F) := by
    linarith [hsplit F]
  rw [h2, abs_neg]
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)

/-- Bound on the iterated derivatives of the lifted real modes. -/
theorem p_cc1_norm_iteratedFDeriv_realMode (k : NonzeroLattice d) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) x‖ ≤
      ((i : ℝ) + 1) * Real.sqrt 2 * Lattice.jp k.1 ^ i := by
  have hs : ContDiff ℝ i (Torus.lift (Torus.realMode k)) :=
    (p_cc1_cd_realMode k).of_le (by exact_mod_cast le_top)
  have hb := Torus.bddAbove_norm_iteratedFDeriv_lift i (Torus.realMode k) hs
  have h1 : ‖iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) x‖ ≤
      ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) y‖ := le_ciSup hb x
  have h2 : (⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) y‖) ≤
      Torus.cbNorm i (Torus.realMode k) := by
    unfold Torus.cbNorm
    refine Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (Torus.realMode k)) y‖)
      (fun j _ => Real.iSup_nonneg fun y => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))
  exact h1.trans (h2.trans (Torus.cbNorm_realMode_le_aux i k))

theorem p_cc1_summable_jp (n : ℕ) :
    Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (n + d + 1))⁻¹ * Lattice.jp k.1 ^ n := by
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine hs.congr fun k => ?_
  have hj := Torus.jp_pos k.1
  rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
    Real.rpow_natCast]
  have hn : Lattice.jp k.1 ^ (n + d + 1) = Lattice.jp k.1 ^ n * Lattice.jp k.1 ^ (d + 1) := by ring
  rw [hn]
  field_simp

/-- Smoothness of `∑ c_k e_k` for rapidly decaying `c`. -/
theorem p_cc1_isSmooth_tsum (c : NonzeroLattice d → ℝ)
    (hc : ∀ N : ℕ, ∃ C : ℝ, ∀ k : NonzeroLattice d, |c k| ≤ C * Lattice.jp k.1 ^ (-(N : ℝ))) :
    Torus.IsSmooth (fun x => ∑' k, c k * Torus.realMode k x) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_infty]
  intro n
  obtain ⟨C, hC⟩ := hc (n + d + 1)
  have hlift : Torus.lift (fun x => ∑' k, c k * Torus.realMode k x) =
      fun y => ∑' k, c k * Torus.lift (Torus.realMode k) y := rfl
  rw [hlift]
  refine contDiff_tsum (𝕜 := ℝ) (N := (n : ℕ∞))
    (v := fun _ k => |C| * (((n : ℝ) + 1) * Real.sqrt 2) *
      ((Lattice.jp k.1 ^ (n + d + 1))⁻¹ * Lattice.jp k.1 ^ n)) ?_ ?_ ?_
  · intro k
    have hs : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode k)) :=
      (p_cc1_cd_realMode k).of_le (by exact_mod_cast le_top)
    exact hs.const_smul (c k)
  · intro i _
    exact (p_cc1_summable_jp (d := d) n).mul_left _
  · intro i k x hi
    have hi' : i ≤ n := by exact_mod_cast hi
    have hs : ContDiff ℝ i (Torus.lift (Torus.realMode k)) :=
      (p_cc1_cd_realMode k).of_le (by exact_mod_cast le_top)
    have e : iteratedFDeriv ℝ i (fun y => c k * Torus.lift (Torus.realMode k) y) x =
        c k • iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) x :=
      iteratedFDeriv_const_smul_apply (a := c k) (f := Torus.lift (Torus.realMode k)) hs.contDiffAt
    rw [e, norm_smul, Real.norm_eq_abs]
    have hj := Torus.jp_pos k.1
    have hj1 := Torus.jp_ge_one k.1
    have h1 := p_cc1_norm_iteratedFDeriv_realMode k i x
    have h2 : Lattice.jp k.1 ^ i ≤ Lattice.jp k.1 ^ n := pow_le_pow_right₀ hj1 hi'
    have h3 : ((i : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hi'
    have hCk : |c k| ≤ |C| * (Lattice.jp k.1 ^ (n + d + 1))⁻¹ := by
      refine (hC k).trans ?_
      have : Lattice.jp k.1 ^ (-((n + d + 1 : ℕ) : ℝ)) = (Lattice.jp k.1 ^ (n + d + 1))⁻¹ := by
        rw [Real.rpow_neg hj.le, Real.rpow_natCast]
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (pow_nonneg hj.le _))
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc |c k| * ‖iteratedFDeriv ℝ i (Torus.lift (Torus.realMode k)) x‖
        ≤ (|C| * (Lattice.jp k.1 ^ (n + d + 1))⁻¹) * (((n : ℝ) + 1) * Real.sqrt 2 * Lattice.jp k.1 ^ n) := by
          refine mul_le_mul hCk (h1.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = _ := by ring

theorem p_cc1_integral (c : NonzeroLattice d → ℝ) (hsum : Summable fun k => |c k|)
    {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ∫ x, ψ x * (∑' k, c k * Torus.realMode k x) = ∑' k, Torus.funRealCoeff ψ k * c k := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (f := ψ) hψ.continuousOn
  set F : NonzeroLattice d → Torus d → ℝ := fun k x => ψ x * (c k * Torus.realMode k x) with hF
  have hFi : ∀ k, Integrable (F k) := fun k =>
    ((hψ.mul (continuous_const.mul (Torus.continuous_realMode k)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k, ∫ x, ‖F k x‖ ≤ B * Real.sqrt 2 * |c k| := by
    intro k
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun x => ‖F k x‖) (C := B * Real.sqrt 2 * |c k|) (Filter.Eventually.of_forall fun x => by
        rw [norm_norm, hF]
        simp only [Real.norm_eq_abs, abs_mul]
        have h1 := hB x (Set.mem_univ x)
        rw [Real.norm_eq_abs] at h1
        have h2 := Torus.abs_realMode_le k x
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x (Set.mem_univ x))
        calc |ψ x| * (|c k| * |Torus.realMode k x|) ≤ B * (|c k| * Real.sqrt 2) := by
              gcongr
          _ = _ := by ring)
    simp only [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans (by simpa using h)
  have hsm : Summable fun k => ∫ x, ‖F k x‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hbd
      (hsum.mul_left _)
  have h := hasSum_integral_of_summable_integral_norm hFi hsm
  have e1 : ∀ x, ∑' k, F k x = ψ x * ∑' k, c k * Torus.realMode k x := fun x => by
    simp only [hF]; rw [tsum_mul_left]
  have e3 : ∀ k, ∫ x, F k x = Torus.funRealCoeff ψ k * c k := by
    intro k
    simp only [hF, Torus.funRealCoeff]
    have : ∀ x, ψ x * (c k * Torus.realMode k x) = c k * (Torus.realMode k x * ψ x) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul]; ring
  simp_rw [e1, e3] at h
  exact h.tsum_eq.symm

theorem ccd_smooth_density_of_bound (L : (Torus d → ℝ) → ℝ)
    (hadd : ∀ ψ ψ' : Torus d → ℝ, Torus.IsSmooth ψ → Torus.IsSmooth ψ' → L (ψ + ψ') = L ψ + L ψ')
    (hsmul : ∀ (c : ℝ) (ψ : Torus d → ℝ), Torus.IsSmooth ψ → L (c • ψ) = c * L ψ)
    (hconst : ∀ c : ℝ, L (fun _ => c) = 0)
    (hbound : ∀ N : ℕ, ∃ C : ℝ, ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      |L ψ| ≤ C * HRS.sobolevNorm (-(N : ℝ)) ψ) :
    ∃ χ : Torus d → ℝ, Torus.IsSmooth χ ∧ ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∫ x, ψ x * χ x = L ψ := by
  set c : NonzeroLattice d → ℝ := fun k => L (Torus.realMode k) with hcdef
  have hc : ∀ N : ℕ, ∃ C : ℝ, ∀ k : NonzeroLattice d, |c k| ≤ C * Lattice.jp k.1 ^ (-(N : ℝ)) := by
    intro N
    obtain ⟨C, hC⟩ := hbound N
    refine ⟨C, fun k => ?_⟩
    have := hC _ (p_cc1_smooth_realMode k)
    rwa [p_cc1_snorm_realMode] at this
  have hsum : Summable fun k => |c k| := by
    obtain ⟨C, hC⟩ := hc (d + 1)
    have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
      (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (hs.mul_left C)
    refine (hC k).trans (le_of_eq ?_)
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring]
  refine ⟨fun x => ∑' k, c k * Torus.realMode k x, p_cc1_isSmooth_tsum c hc, ?_⟩
  intro ψ hψ
  have hψc : Continuous ψ := Torus.continuous_of_continuous_lift (p_cc1_cd_of_smooth hψ).continuous
  obtain ⟨C, hC⟩ := hbound 0
  have hH := p_cc1_hasSum L hadd hsmul hconst C hC hψ
  rw [p_cc1_integral c hsum hψc]
  exact hH.tsum_eq

end HRS.MC.CrossCov
