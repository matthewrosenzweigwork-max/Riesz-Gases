import HRS.MS.SA12Z3NearN7G

/-!
# S.A.12 N7 (SA12Z3), part H: the energy bound for one index tuple
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_idx_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (m : ℕ)
    (hm : 1 ≤ m) (MB Ka R : ℝ) (hR : 1 ≤ R) :
    ∃ A1 : ℝ, 0 ≤ A1 ∧ ∀ (c : Euc d) (om a W F : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
      (∀ i j, |M i j| ≤ MB) → Continuous om → HasCompactSupport om →
      Function.support om ⊆ closedBall c R → (∀ x, |om x| ≤ 1) →
      Continuous W → HasCompactSupport W → (∀ x, om x ^ 2 ≤ W x) →
      ContDiff ℝ (m + 1) a → HasCompactSupport a → Function.support a ⊆ closedBall c R →
      (∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) → (∀ x ∈ tsupport a, 1 ≤ W x) →
      ContDiff ℝ ∞ F → ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d),
      |∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x)| ≤
        A1 * ∫ x, W x * sa12z3_Y m F x := by
  have hsd : s < d := by linarith
  have hs1 : s ≤ (d : ℝ) - 1 := by linarith
  obtain ⟨CH, CH0, hCH, hCH0, hH⟩ := sa12z3_hess_real hd hs0 hs2
  obtain ⟨CF, CF0, hCF, hF1⟩ := sa12z3_first_real hd hs0 hsd hs1
  have hR0 : 0 < R := by linarith
  have hKH : 0 ≤ CH * R ^ CH0 := mul_nonneg hCH (Real.rpow_nonneg hR0.le _)
  have hKF : 0 ≤ CF * R ^ CF0 := mul_nonneg hCF (Real.rpow_nonneg hR0.le _)
  have hcT := sa12z3_cT_nonneg d m
  refine ⟨(d : ℝ) ^ 2 * |MB| * (CH * R ^ CH0 * Real.sqrt (Ka ^ 2) + CF * R ^ CF0 * Real.sqrt (Ka ^ 2) +
    CF * R ^ CF0 * Real.sqrt ((Ka * 2 ^ m) ^ 2 * sa12z3_cT d m)), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) (add_nonneg (add_nonneg
      (mul_nonneg hKH (Real.sqrt_nonneg _)) (mul_nonneg hKF (Real.sqrt_nonneg _)))
      (mul_nonneg hKF (Real.sqrt_nonneg _)))
  intro c om a W F M hM hom homc homs hom1 hW hWcs hWom ha hac has hKa hWa hF n hn idx
  set u : Euc d → ℝ := partialDeriv idx F with hu
  have hu_inf : ContDiff ℝ ∞ u := sa12z3_pd_contDiff_inf hF idx
  have huc : Continuous u := hu_inf.continuous
  have hW0 : ∀ x, 0 ≤ W x := fun x => (sq_nonneg _).trans (hWom x)
  set Y : Euc d → ℝ := sa12z3_Y m F with hY
  have hYc : Continuous Y := by
    rw [hY]
    unfold sa12z3_Y
    refine continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ => ?_
    exact ((sa12z3_pd_contDiff_inf hF γ).continuous).pow 2
  have hWYi : Integrable (fun x => W x * Y x) volume :=
    (hW.mul hYc).integrable_of_hasCompactSupport hWcs.mul_right
  set e : ℝ := ∫ x, W x * Y x with he
  have he0 : 0 ≤ e := integral_nonneg fun x => mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _)
  have hWui : Integrable (fun x => W x * u x ^ 2) volume :=
    (hW.mul (huc.pow 2)).integrable_of_hasCompactSupport hWcs.mul_right
  have hue : ∫ x, W x * u x ^ 2 ≤ e :=
    integral_mono hWui hWYi fun x => mul_le_mul_of_nonneg_left (sa12z3_pd_sq_le_Y hn F x idx) (hW0 x)
  -- regularity
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa 0 (Nat.zero_le _) 0)
  have hsa : tsupport a ⊆ closedBall c R := closure_minimal has isClosed_closedBall
  have hu2 : ContDiff ℝ 2 u := sa12z3_cd_of_inf hu_inf 2
  -- the three inputs
  have hv1 : ContDiff ℝ 2 (fun y => a y * u y) := ha2.mul hu2
  have hv1c : HasCompactSupport (fun y => a y * u y) := hac.mul_right
  have hv1s : Function.support (fun y => a y * u y) ⊆ closedBall c R := fun y hy =>
    has (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hDja : ∀ j, ContDiff ℝ 1 (D1 j a) := fun j =>
    (ha2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hv2 : ∀ j, ContDiff ℝ 1 (fun y => D1 j a y * u y) := fun j =>
    (hDja j).mul (sa12z3_cd_of_inf hu_inf 1)
  have hv2c : ∀ j, HasCompactSupport (fun y => D1 j a y * u y) := fun j => (D1_supp hac j).mul_right
  have hD1a_supp : ∀ j y, D1 j a y ≠ 0 → y ∈ tsupport a := by
    intro j y hy
    have : fderiv ℝ a y ≠ 0 := fun h0 => hy (by simp [D1, h0])
    exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this)
  have hv2s : ∀ j, Function.support (fun y => D1 j a y * u y) ⊆ closedBall c R := fun j y hy =>
    hsa (hD1a_supp j y (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hDju : ∀ j, ContDiff ℝ 1 (D1 j u) := fun j =>
    (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDF : ∀ j, ContDiff ℝ (m + 1) (D1 j F) := fun j =>
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := (m + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
  have hP : ∀ j, ContDiff ℝ (m + 1) (fun y => a y * D1 j F y) := fun j => ha.mul (hDF j)
  have hPc : ∀ j, HasCompactSupport (fun y => a y * D1 j F y) := fun j => hac.mul_right
  have hΦ1 : ∀ j, ContDiff ℝ 1 (partialDeriv idx (fun y => a y * D1 j F y)) := fun j => by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hP j) (by omega) idx
    exact this.of_le (by norm_cast; omega)
  have hv3 : ∀ j, ContDiff ℝ 1 (sa12z3_Rj a F idx j) := fun j => (hΦ1 j).sub (ha1.mul (hDju j))
  have hv3c : ∀ j, HasCompactSupport (sa12z3_Rj a F idx j) := fun j =>
    (sa12z3_pd_compact (hPc j) idx).sub hac.mul_right
  have hv3s : ∀ j y, sa12z3_Rj a F idx j y ≠ 0 → y ∈ tsupport a := by
    intro j y hy
    by_contra hny
    apply hy
    have h1 : a y = 0 := by
      by_contra h
      exact hny (subset_tsupport _ h)
    have h2 : partialDeriv idx (fun y => a y * D1 j F y) y = 0 := by
      by_contra h
      have := sa12z3_pd_support idx (Function.mem_support.2 h)
      exact hny (tsupport_mul_subset_left this)
    unfold sa12z3_Rj
    rw [h1, h2]; ring
  have hv3s' : ∀ j, Function.support (sa12z3_Rj a F idx j) ⊆ closedBall c R := fun j y hy =>
    hsa (hv3s j y hy)
  -- pointwise square bounds
  have hKaabs : ∀ y, |a y| ≤ Ka := fun y => by
    have := hKa 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hKaD : ∀ j y, |D1 j a y| ≤ Ka := fun j y => by
    have h1 := hKa 1 (by omega) y
    rw [norm_iteratedFDeriv_one] at h1
    have h2 := (fderiv ℝ a y).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at h2
    exact (by simpa [D1, Real.norm_eq_abs] using h2 : |D1 j a y| ≤ ‖fderiv ℝ a y‖).trans h1
  have hsq1 : ∀ y, (a y * u y) ^ 2 ≤ Ka ^ 2 * (W y * u y ^ 2) := by
    intro y
    by_cases hy : a y = 0
    · rw [hy, zero_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hW0 y) (sq_nonneg _))
    · have hW1 := hWa y (subset_tsupport _ hy)
      have h1 : a y ^ 2 ≤ Ka ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKaabs y) 2
      calc (a y * u y) ^ 2 = a y ^ 2 * u y ^ 2 := by ring
        _ ≤ Ka ^ 2 * (1 * u y ^ 2) := by rw [one_mul]; gcongr
        _ ≤ Ka ^ 2 * (W y * u y ^ 2) := by gcongr
  have hsq2 : ∀ j y, (D1 j a y * u y) ^ 2 ≤ Ka ^ 2 * (W y * u y ^ 2) := by
    intro j y
    by_cases hy : D1 j a y = 0
    · rw [hy, zero_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hW0 y) (sq_nonneg _))
    · have hW1 := hWa y (hD1a_supp j y hy)
      have h1 : D1 j a y ^ 2 ≤ Ka ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKaD j y) 2
      calc (D1 j a y * u y) ^ 2 = D1 j a y ^ 2 * u y ^ 2 := by ring
        _ ≤ Ka ^ 2 * (1 * u y ^ 2) := by rw [one_mul]; gcongr
        _ ≤ Ka ^ 2 * (W y * u y ^ 2) := by gcongr
  have hsq3 : ∀ j y, sa12z3_Rj a F idx j y ^ 2 ≤ (Ka * 2 ^ m) ^ 2 * sa12z3_cT d m * (W y * Y y) := by
    intro j y
    by_cases hy : sa12z3_Rj a F idx j y = 0
    · rw [hy]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hcT) (mul_nonneg (hW0 y) (sa12z3_Y_nonneg _ _ _))
    · have hW1 := hWa y (hv3s j y hy)
      have h1 := sa12z3_Rj_pt hn ha hF hKa idx j y
      have h2 : sa12z3_Rj a F idx j y ^ 2 ≤ (Ka * 2 ^ m * sa12z3_T m F y) ^ 2 := by
        rw [← sq_abs (sa12z3_Rj a F idx j y)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 := sa12z3_T_sq m F y
      calc sa12z3_Rj a F idx j y ^ 2 ≤ (Ka * 2 ^ m * sa12z3_T m F y) ^ 2 := h2
        _ = (Ka * 2 ^ m) ^ 2 * sa12z3_T m F y ^ 2 := by ring
        _ ≤ (Ka * 2 ^ m) ^ 2 * (sa12z3_cT d m * Y y) := by gcongr
        _ = (Ka * 2 ^ m) ^ 2 * sa12z3_cT d m * (1 * Y y) := by ring
        _ ≤ (Ka * 2 ^ m) ^ 2 * sa12z3_cT d m * (W y * Y y) := by
          have := sa12z3_Y_nonneg m F y
          gcongr
  -- integral bounds of the inputs
  have hint2 : ∀ {v : Euc d → ℝ}, Continuous v → HasCompactSupport v → Integrable (fun x => v x ^ 2) volume :=
    fun {v} hv hvc => Continuous.integrable_of_hasCompactSupport (f := fun x => v x ^ 2) (hv.pow 2)
      (hvc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hI1 : ∫ x, (a x * u x) ^ 2 ≤ Ka ^ 2 * e := by
    calc ∫ x, (a x * u x) ^ 2 ≤ ∫ x, Ka ^ 2 * (W x * u x ^ 2) :=
          integral_mono (hint2 (ha1.continuous.mul huc) hv1c) (hWui.const_mul _) hsq1
      _ = Ka ^ 2 * ∫ x, W x * u x ^ 2 := integral_const_mul _ _
      _ ≤ Ka ^ 2 * e := by gcongr
  have hI2 : ∀ j, ∫ x, (D1 j a x * u x) ^ 2 ≤ Ka ^ 2 * e := fun j => by
    calc ∫ x, (D1 j a x * u x) ^ 2 ≤ ∫ x, Ka ^ 2 * (W x * u x ^ 2) :=
          integral_mono (hint2 ((hv2 j).continuous) (hv2c j)) (hWui.const_mul _) (hsq2 j)
      _ = Ka ^ 2 * ∫ x, W x * u x ^ 2 := integral_const_mul _ _
      _ ≤ Ka ^ 2 * e := by gcongr
  have hI3 : ∀ j, ∫ x, sa12z3_Rj a F idx j x ^ 2 ≤ (Ka * 2 ^ m) ^ 2 * sa12z3_cT d m * e := fun j => by
    calc ∫ x, sa12z3_Rj a F idx j x ^ 2 ≤ ∫ x, (Ka * 2 ^ m) ^ 2 * sa12z3_cT d m * (W x * Y x) :=
          integral_mono (hint2 ((hv3 j).continuous) (hv3c j)) (hWYi.const_mul _) (hsq3 j)
      _ = _ := integral_const_mul _ _
  -- the decomposition and the sum
  have hdec := fun (x : Euc d) => sa12z3_pd_G_decomp hs0 hsd M hm ha hac hF hn idx x
  have hmain : ∀ i j : Fin d, |∫ x, om x ^ 2 * (u x * hessRiesz d s i j (fun y => a y * u y) x)| ≤
      CH * R ^ CH0 * Real.sqrt (Ka ^ 2) * e := fun i j =>
    sa12z3_term hom homc homs hom1 hW hWcs hWom huc (sa12z3_hess_cont hs0 hsd i j hv1 hv1c)
      hKH (sq_nonneg _) he0 hue
      (hH i j R hR c _ (sa12z3_memCb_of_cc hv1 hv1c) hv1s) hI1
  have hmain2 : ∀ i j : Fin d, |∫ x, om x ^ 2 * (u x * firstRiesz d s i (fun y => D1 j a y * u y) x)| ≤
      CF * R ^ CF0 * Real.sqrt (Ka ^ 2) * e := fun i j =>
    sa12z3_term hom homc homs hom1 hW hWcs hWom huc (sa12z3_firstRiesz_cont hs0 hsd i (hv2 j) (hv2c j))
      hKF (sq_nonneg _) he0 hue (hF1 i R hR c _ (hv2 j) (hv2c j) (hv2s j)) (hI2 j)
  have hmain3 : ∀ i j : Fin d, |∫ x, om x ^ 2 * (u x * firstRiesz d s i (sa12z3_Rj a F idx j) x)| ≤
      CF * R ^ CF0 * Real.sqrt ((Ka * 2 ^ m) ^ 2 * sa12z3_cT d m) * e := fun i j =>
    sa12z3_term hom homc homs hom1 hW hWcs hWom huc (sa12z3_firstRiesz_cont hs0 hsd i (hv3 j) (hv3c j))
      hKF (mul_nonneg (sq_nonneg _) hcT) he0 hue (hF1 i R hR c _ (hv3 j) (hv3c j) (hv3s' j)) (hI3 j)
  have hom2c : HasCompactSupport (fun x => om x ^ 2) :=
    homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hint : ∀ {X : Euc d → ℝ}, Continuous X → Integrable (fun x => om x ^ 2 * (u x * X x)) volume :=
    fun {X} hX => Continuous.integrable_of_hasCompactSupport (f := fun x => om x ^ 2 * (u x * X x))
      ((hom.pow 2).mul (huc.mul hX)) (hom2c.mul_right)
  have hcH := fun i j : Fin d => sa12z3_hess_cont hs0 hsd i j hv1 hv1c
  have hcT2 := fun i j : Fin d => sa12z3_firstRiesz_cont hs0 hsd i (hv2 j) (hv2c j)
  have hcT3 := fun i j : Fin d => sa12z3_firstRiesz_cont hs0 hsd i (hv3 j) (hv3c j)
  set HH : Fin d → Fin d → Euc d → ℝ := fun i j => hessRiesz d s i j (fun y => a y * u y) with hHH
  set T2 : Fin d → Fin d → Euc d → ℝ := fun i j => firstRiesz d s i (fun y => D1 j a y * u y) with hT2
  set T3 : Fin d → Fin d → Euc d → ℝ := fun i j => firstRiesz d s i (sa12z3_Rj a F idx j) with hT3
  have hIij : ∀ i j : Fin d, Integrable (fun x => M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x))) volume := fun i j =>
    (((hint (hcH i j)).sub (hint (hcT2 i j))).add (hint (hcT3 i j))).const_mul _
  have e1 : ∀ x, om x ^ 2 * (u x * partialDeriv idx (eucNonlocal s M a F) x) = ∑ i, ∑ j, M j i *
      (om x ^ 2 * (u x * HH i j x) - om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x)) := by
    intro x
    rw [hdec x, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [hHH, hT2, hT3]; ring
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hIij i j)]
  have hterm : ∀ i j : Fin d, |∫ x, M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x))| ≤
      |MB| * ((CH * R ^ CH0 * Real.sqrt (Ka ^ 2) + CF * R ^ CF0 * Real.sqrt (Ka ^ 2) +
        CF * R ^ CF0 * Real.sqrt ((Ka * 2 ^ m) ^ 2 * sa12z3_cT d m)) * e) := by
    intro i j
    rw [integral_const_mul, abs_mul]
    have hsplit : ∫ x, (om x ^ 2 * (u x * HH i j x) - om x ^ 2 * (u x * T2 i j x) +
        om x ^ 2 * (u x * T3 i j x)) = (∫ x, om x ^ 2 * (u x * HH i j x)) -
        (∫ x, om x ^ 2 * (u x * T2 i j x)) + ∫ x, om x ^ 2 * (u x * T3 i j x) := by
      have hI12 : Integrable (fun x => om x ^ 2 * (u x * HH i j x) - om x ^ 2 * (u x * T2 i j x)) volume :=
        (hint (hcH i j)).sub (hint (hcT2 i j))
      rw [integral_add hI12 (hint (hcT3 i j)), integral_sub (hint (hcH i j)) (hint (hcT2 i j))]
    rw [hsplit]
    have hMji : |M j i| ≤ |MB| := (hM j i).trans (le_abs_self MB)
    have b1 := hmain i j
    have b2 := hmain2 i j
    have b3 := hmain3 i j
    have hb : |(∫ x, om x ^ 2 * (u x * HH i j x)) - (∫ x, om x ^ 2 * (u x * T2 i j x)) +
        ∫ x, om x ^ 2 * (u x * T3 i j x)| ≤ (CH * R ^ CH0 * Real.sqrt (Ka ^ 2) +
          CF * R ^ CF0 * Real.sqrt (Ka ^ 2) + CF * R ^ CF0 * Real.sqrt ((Ka * 2 ^ m) ^ 2 * sa12z3_cT d m)) * e := by
      refine (abs_add_le _ _).trans ?_
      have := abs_sub (∫ x, om x ^ 2 * (u x * HH i j x)) (∫ x, om x ^ 2 * (u x * T2 i j x))
      nlinarith [abs_nonneg ((∫ x, om x ^ 2 * (u x * HH i j x)) - (∫ x, om x ^ 2 * (u x * T2 i j x)))]
    exact mul_le_mul hMji hb (abs_nonneg _) (abs_nonneg _)
  have hrow : ∀ i : Fin d, |∫ x, ∑ j, M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x))| ≤
      (d : ℝ) * (|MB| * ((CH * R ^ CH0 * Real.sqrt (Ka ^ 2) + CF * R ^ CF0 * Real.sqrt (Ka ^ 2) +
        CF * R ^ CF0 * Real.sqrt ((Ka * 2 ^ m) ^ 2 * sa12z3_cT d m)) * e)) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hIij i j)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hterm i j).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_refl _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hrow i).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
