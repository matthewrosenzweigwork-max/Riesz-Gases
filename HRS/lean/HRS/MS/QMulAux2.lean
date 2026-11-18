import HRS.MS.QMulAux1

/-!
# MS-QMUL, part 2: `H^m` norm versus coordinate derivatives

For `g` in the class `QOk m` (`C^m`, all derivatives of order `≤ m` in `L¹ ∩ L²`):
* `qm_lower`: `∫⁻ ⟨ξ⟩^m |ĝ|² ≤ 2^m ∑_{n ≤ m} ∑_i ∫⁻ |∂^i g|²`;
* `qm_upper`: `∑_{n ≤ m} ∑_i ∫⁻ |∂^i g|² ≤ (m+1) ∫⁻ ⟨ξ⟩^m |ĝ|²`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_sum_sq (n : ℕ) (ξ : Euc d) :
    ∑ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 =
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n := by
  have h1 : ∀ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 =
      (4 * Real.pi ^ 2) ^ n * ∏ t, (ξ (i t)) ^ 2 := by
    intro i
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, ← Finset.prod_pow]
    simp only [sq_abs]
    congr 1; ring
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have h2 : ∑ i : Fin n → Fin d, ∏ t, (ξ (i t)) ^ 2 = (∑ j : Fin d, (ξ j) ^ 2) ^ n := by
    have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin d)))
      (fun _ j => (ξ j) ^ 2)
    rw [Fintype.piFinset_univ] at this
    rw [← this]; simp
  rw [h2, ← mul_pow]
  congr 2
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem qm_wt_pow_le (m : ℕ) (ξ : Euc d) :
    wt ξ ^ m ≤ 2 ^ m * ∑ n ∈ Finset.range (m + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n := by
  have hx : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have : wt ξ = (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) + 1 := by unfold wt; ring
  rw [this, add_pow, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [one_pow, mul_one]
  have h2 : (m.choose k : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m k
  calc _ ≤ (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k * 2 ^ m := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_comm _ _

theorem qm_pow_le_wt {n m : ℕ} (hn : n ≤ m) (ξ : Euc d) :
    (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n ≤ wt ξ ^ m :=
  (pow_le_pow_left₀ (by positivity) (by unfold wt; linarith) n).trans
    (pow_le_pow_right₀ (one_le_wt ξ) hn)

/-- the regularity class: `C^m`, all derivatives of order `≤ m` in `L¹ ∩ L²` -/
def QOk (m : ℕ) (f : Euc d → ℂ) : Prop :=
  ContDiff ℝ m f ∧ ∀ k : ℕ, k ≤ m →
    Integrable (iteratedFDeriv ℝ k f) volume ∧ MemLp (iteratedFDeriv ℝ k f) 2 volume

theorem qm_norm_pd_le {n : ℕ} (i : Fin n → Fin d) (f : Euc d → ℂ) (x : Euc d) :
    ‖qm_pd i f x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  unfold qm_pd
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ t, ‖(EuclideanSpace.single (i t) (1:ℝ) : Euc d)‖ = 1 := by simp
  rw [this, mul_one]

theorem qm_continuous_pd {m n : ℕ} (hn : n ≤ m) {f : Euc d → ℂ} (hf : ContDiff ℝ m f)
    (i : Fin n → Fin d) : Continuous (qm_pd i f) :=
  (continuous_eval_const (fun t : Fin n => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))).comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hn))

theorem qm_pd_L1L2 {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) {n : ℕ} (hn : n ≤ m)
    (i : Fin n → Fin d) : Integrable (qm_pd i f) volume ∧ MemLp (qm_pd i f) 2 volume :=
  ⟨((hf.2 n hn).1.norm).mono' (qm_continuous_pd hn hf.1 i).aestronglyMeasurable
      (Filter.Eventually.of_forall (qm_norm_pd_le i f)),
    (hf.2 n hn).2.mono (qm_continuous_pd hn hf.1 i).aestronglyMeasurable
      (Filter.Eventually.of_forall (qm_norm_pd_le i f))⟩

theorem qm_enorm_sq_fourier_pd {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) {n : ℕ} (hn : n ≤ m)
    (i : Fin n → Fin d) (ξ : Euc d) :
    ‖𝓕 (qm_pd i f) ξ‖ₑ ^ 2 =
      ENNReal.ofReal (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖𝓕 f ξ‖ ^ 2) := by
  rw [← ofReal_norm, qm_fourier_pd_norm hf.1 (fun k hk => (hf.2 k hk).1) hn i ξ,
    ← ENNReal.ofReal_pow (by positivity)]
  congr 1; ring

theorem qm_sum_enorm_sq {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) {n : ℕ} (hn : n ≤ m) (ξ : Euc d) :
    ∑ i : Fin n → Fin d, ‖𝓕 (qm_pd i f) ξ‖ₑ ^ 2 =
      ENNReal.ofReal ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n * ‖𝓕 f ξ‖ ^ 2) := by
  rw [Finset.sum_congr rfl (fun i _ => qm_enorm_sq_fourier_pd hf hn i ξ),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ← Finset.sum_mul, qm_sum_sq]

theorem qm_sum_sum_enorm_sq {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) (ξ : Euc d) :
    ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ‖𝓕 (qm_pd i f) ξ‖ₑ ^ 2 =
      ENNReal.ofReal ((∑ n ∈ Finset.range (m + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n) *
        ‖𝓕 f ξ‖ ^ 2) := by
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact qm_sum_enorm_sq hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) ξ

theorem qm_aemeasurable_enorm_sq {h : Euc d → ℂ} (h1 : Integrable h volume) :
    AEMeasurable (fun ξ => ‖𝓕 h ξ‖ₑ ^ 2) volume := by
  have hc : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  exact (hc.measurable.enorm.pow_const 2).aemeasurable

theorem qm_swap {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) :
    ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ∫⁻ x, ‖qm_pd i f x‖ₑ ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal ((∑ n ∈ Finset.range (m + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n) *
        ‖𝓕 f ξ‖ ^ 2) := by
  simp_rw [← qm_sum_sum_enorm_sq hf]
  rw [lintegral_finsetSum']
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [lintegral_finsetSum']
    · refine Finset.sum_congr rfl fun i _ => ?_
      have := qm_pd_L1L2 hf hn' i
      exact (qm_plancherel this.1 this.2).symm
    · exact fun i _ => qm_aemeasurable_enorm_sq (qm_pd_L1L2 hf hn' i).1
  · intro n hn
    have hn' : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    exact Finset.aemeasurable_fun_sum _ fun i _ => qm_aemeasurable_enorm_sq (qm_pd_L1L2 hf hn' i).1

theorem qm_lower {m : ℕ} {g : Euc d → ℂ} (hg : QOk m g) :
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 g ξ‖ ^ 2) ≤
      2 ^ m * ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ∫⁻ x, ‖qm_pd i g x‖ₑ ^ 2 := by
  rw [qm_swap hg, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
  refine lintegral_mono fun ξ => ?_
  have h2 : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal (2 ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc wt ξ ^ m * ‖𝓕 g ξ‖ ^ 2
      ≤ (2 ^ m * ∑ n ∈ Finset.range (m + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n) * ‖𝓕 g ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (qm_wt_pow_le m ξ) (sq_nonneg _)
    _ = _ := by ring

theorem qm_upper {m : ℕ} {f : Euc d → ℂ} (hf : QOk m f) :
    ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ∫⁻ x, ‖qm_pd i f x‖ₑ ^ 2 ≤
      (m + 1) * ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 f ξ‖ ^ 2) := by
  rw [qm_swap hf, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun ξ => ?_
  have h2 : ((m : ℝ≥0∞) + 1) = ENNReal.ofReal ((m : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : ∑ n ∈ Finset.range (m + 1), (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n ≤ ((m : ℝ) + 1) * wt ξ ^ m := by
    calc _ ≤ ∑ n ∈ Finset.range (m + 1), wt ξ ^ m :=
          Finset.sum_le_sum fun n hn => qm_pow_le_wt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) ξ
      _ = _ := by simp
  calc _ ≤ (((m : ℝ) + 1) * wt ξ ^ m) * ‖𝓕 f ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ = _ := by ring

end HRS.MS.QMul
