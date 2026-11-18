import HRS.Commutator.Whole.ExternalAuxHLS1

/-!
# X-LI (Li's fractional Leibniz rule), part 1: maximal function toolkit

* `Mx_strong`: the strong `(p,p)` maximal inequality for `ℝ≥0∞`-valued measurable functions;
* `lintegral_ball_le`, `lintegral_Phi_le`: a convolution with the dyadic majorant kernel
  `Phi j y = 2^{jd} (1 + 2^j |y|)^{-(d+1)}` is dominated by the maximal function.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The Hardy–Littlewood maximal theorem for `ℝ≥0∞`-valued functions (finite constant). -/
lemma Mx_strong (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ f : 𝔼 → ℝ≥0∞, Measurable f →
      ∫⁻ x, cmxHLS_Md f x ^ p ≤ C * ∫⁻ x, f x ^ p := by
  obtain ⟨C, hC, h⟩ := cmxHLS_strong hd hp
  refine ⟨C.toNNReal, fun f hf => ?_⟩
  -- truncations
  set fn : ℕ → 𝔼 → ℝ≥0 := fun n y => if ‖y‖ < n then (min (f y) n).toNNReal else 0 with hfn
  have hfn_meas : ∀ n, Measurable (fn n) := fun n => by
    refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
    exact (hf.min measurable_const).ennreal_toNNReal
  have hfn_le : ∀ n y, ((fn n y : ℝ≥0) : ℝ≥0∞) ≤ f y := fun n y => by
    simp only [hfn]
    split_ifs
    · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))]
      exact min_le_left _ _
    · simp
  have hfn_mono : Monotone (fun n y => ((fn n y : ℝ≥0) : ℝ≥0∞)) := by
    intro m n hmn y
    simp only [hfn]
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    by_cases hm : ‖y‖ < m
    · have hn : ‖y‖ < n := lt_of_lt_of_le hm hmn'
      rw [if_pos hm, if_pos hn]
      refine ENNReal.coe_le_coe.2 ?_
      refine ENNReal.toNNReal_mono (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)) ?_
      exact min_le_min le_rfl (by exact_mod_cast hmn)
    · rw [if_neg hm]; simp
  have hfn_sup : ∀ y, ⨆ n, ((fn n y : ℝ≥0) : ℝ≥0∞) = f y := by
    intro y
    refine le_antisymm (iSup_le fun n => hfn_le n y) ?_
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    obtain ⟨m, hm⟩ := exists_nat_gt ‖y‖
    refine lt_iSup_iff.2 ⟨max n m, ?_⟩
    simp only [hfn]
    have hmm : ‖y‖ < ((max n m : ℕ) : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast le_max_right n m)
    rw [if_pos hmm, ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (min_le_right _ _))]
    refine lt_min hc (lt_of_lt_of_le hn ?_)
    exact_mod_cast le_max_left n m
  -- monotone convergence
  have hMd_mono : ∀ x, Monotone (fun n => cmxHLS_Md (fun y => ((fn n y : ℝ≥0) : ℝ≥0∞)) x) := by
    intro x m n hmn
    unfold cmxHLS_Md
    refine iSup_mono fun j => ?_
    exact mul_le_mul_right (lintegral_mono fun y => hfn_mono hmn y) _
  have hMd_sup : ∀ x, ⨆ n, cmxHLS_Md (fun y => ((fn n y : ℝ≥0) : ℝ≥0∞)) x = cmxHLS_Md f x := by
    intro x
    unfold cmxHLS_Md
    rw [iSup_comm]
    refine iSup_congr fun j => ?_
    rw [← ENNReal.mul_iSup, ← lintegral_iSup (fun n => (hfn_meas n).coe_nnreal_ennreal) hfn_mono]
    congr 1
    refine lintegral_congr fun y => hfn_sup y
  have hlim : ∫⁻ x, cmxHLS_Md f x ^ p = ⨆ n, ∫⁻ x, cmxHLS_Md (fun y => ((fn n y : ℝ≥0) : ℝ≥0∞)) x ^ p := by
    rw [← lintegral_iSup]
    · congr 1; ext x
      rw [← hMd_sup x]
      exact (Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
        (ENNReal.monotone_rpow_of_nonneg (by linarith)) (ENNReal.zero_rpow_of_pos (by linarith)))
    · intro n; exact (cmxHLS_Md_measurable (hfn_meas n).coe_nnreal_ennreal).pow_const _
    · intro m n hmn x
      exact ENNReal.rpow_le_rpow (hMd_mono x hmn) (by linarith)
  rw [hlim]
  refine iSup_le fun n => ?_
  have := h (fn n) (hfn_meas n)
  refine this.trans ?_
  refine mul_le_mul' le_rfl ?_
  exact lintegral_mono fun y => ENNReal.rpow_le_rpow (hfn_le n y) (by linarith)

lemma lintegral_ball_le (f : 𝔼 → ℝ≥0∞) (x : 𝔼) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in closedBall x R, f y ≤
      ENNReal.ofReal ((2 * R) ^ d) * volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md f x := by
  obtain ⟨n, hn1, hn2⟩ := _root_.exists_mem_Ioc_zpow hR (one_lt_two : (1:ℝ) < 2)
  have hsub : closedBall x R ⊆ closedBall x ((2:ℝ) ^ (n+1)) := closedBall_subset_closedBall hn2
  have h2 : ((2:ℝ) ^ (n+1)) ≤ 2 * R := by
    rw [zpow_add₀ (by norm_num), zpow_one]; linarith
  calc ∫⁻ y in closedBall x R, f y ≤ ∫⁻ y in closedBall x ((2:ℝ) ^ (n+1)), f y :=
        lintegral_mono_set hsub
    _ ≤ volume (closedBall x ((2:ℝ) ^ (n+1))) * cmxHLS_Md f x := cmxHLS_lintegral_le f x (n+1)
    _ = ENNReal.ofReal (((2:ℝ) ^ (n+1)) ^ d) * volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md f x := by
        rw [cmxHLS_vol_closedBall x (zpow_pos (by norm_num) _).le]
    _ ≤ _ := by
        gcongr

/-- The dyadic majorant kernel `2^{jd} (1 + 2^j |y|)^{-(d+1)}`. -/
def Phi (j : ℤ) (y : 𝔼) : ℝ≥0∞ :=
  ENNReal.ofReal (((2:ℝ) ^ j) ^ d * ((1 + (2:ℝ) ^ j * ‖y‖) ^ (d + 1))⁻¹)

/-- The constant of the maximal-function domination of `Phi`. -/
def KP (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 ^ (d + 1)) * volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)

lemma KP_ne_top : KP d ≠ ⊤ := by
  unfold KP
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne

lemma Phi_measurable (j : ℤ) : Measurable (Phi j : 𝔼 → ℝ≥0∞) := by
  unfold Phi
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

lemma Phi_neg (j : ℤ) (y : 𝔼) : Phi j (-y) = Phi j y := by
  simp [Phi]

/-- step-function majorant of `Phi` -/
lemma Phi_le_tsum (j : ℤ) (y : 𝔼) :
    Phi j y ≤ ∑' k : ℕ, (ball (0 : 𝔼) ((2:ℝ) ^ k / (2:ℝ) ^ j)).indicator
      (fun _ => ENNReal.ofReal (((2:ℝ) ^ j) ^ d * 2 ^ (d + 1) / ((2:ℝ) ^ k) ^ (d + 1))) y := by
  set s : ℝ := (2:ℝ) ^ j with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) j
  have hex : ∃ k : ℕ, s * ‖y‖ < (2:ℝ) ^ k := pow_unbounded_of_one_lt _ (by norm_num)
  classical
  obtain ⟨k0, hk0spec, hk0min⟩ : ∃ k0 : ℕ, s * ‖y‖ < (2:ℝ) ^ k0 ∧
      ∀ m < k0, ¬ (s * ‖y‖ < (2:ℝ) ^ m) := ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hmem : y ∈ ball (0 : 𝔼) ((2:ℝ) ^ k0 / s) := by
    rw [mem_ball_zero_iff, lt_div_iff₀ hs0]; linarith
  refine le_trans ?_ (ENNReal.le_tsum k0)
  rw [Set.indicator_of_mem hmem]
  unfold Phi
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < (1 + s * ‖y‖) := by positivity
  rcases Nat.eq_zero_or_pos k0 with h0 | hk
  · rw [h0]
    have : ((1 + s * ‖y‖) ^ (d + 1))⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact one_le_pow₀ (by nlinarith [norm_nonneg y])
    calc s ^ d * ((1 + s * ‖y‖) ^ (d + 1))⁻¹ ≤ s ^ d * 1 := by gcongr
      _ ≤ s ^ d * 2 ^ (d + 1) / ((2:ℝ) ^ 0) ^ (d + 1) := by
        simp only [pow_zero, one_pow, div_one, mul_one]
        have : (1:ℝ) ≤ 2 ^ (d + 1) := one_le_pow₀ (by norm_num)
        nlinarith [pow_pos hs0 d]
  · obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
    have hnot : ¬ (s * ‖y‖ < (2:ℝ) ^ k) := hk0min k (by omega)
    have h1 : (2:ℝ) ^ k ≤ 1 + s * ‖y‖ := by linarith [not_lt.1 hnot]
    have h2 : ((2:ℝ) ^ k) ^ (d + 1) ≤ (1 + s * ‖y‖) ^ (d + 1) := pow_le_pow_left₀ (by positivity) h1 _
    calc s ^ d * ((1 + s * ‖y‖) ^ (d + 1))⁻¹ ≤ s ^ d * (((2:ℝ) ^ k) ^ (d + 1))⁻¹ := by
          gcongr
      _ = s ^ d * 2 ^ (d + 1) / ((2:ℝ) ^ (k + 1)) ^ (d + 1) := by
          rw [pow_succ 2 k, mul_pow]; field_simp

lemma lintegral_ball_shift (a : ℝ≥0∞) {G : 𝔼 → ℝ≥0∞} (hG : Measurable G) (x : 𝔼) (ρ : ℝ) :
    ∫⁻ y, (ball (0 : 𝔼) ρ).indicator (fun y => a * G (x - y)) y = a * ∫⁻ z in ball x ρ, G z := by
  have h : (fun y : 𝔼 => (ball (0 : 𝔼) ρ).indicator (fun y => a * G (x - y)) y) =
      fun y => (ball x ρ).indicator (fun z => a * G z) (x - y) := by
    ext y
    have : (y ∈ ball (0 : 𝔼) ρ) ↔ (x - y ∈ ball x ρ) := by
      rw [mem_ball_zero_iff, mem_ball, dist_eq_norm]
      simp
    by_cases hy : y ∈ ball (0 : 𝔼) ρ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (this.1 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h' => hy (this.2 h'))]
  rw [h, lintegral_sub_left_eq_self (fun z => (ball x ρ).indicator (fun z => a * G z) z) x,
    lintegral_indicator measurableSet_ball, lintegral_const_mul _ hG]

/-- convolution with the dyadic majorant kernel is dominated by the maximal function -/
lemma lintegral_Phi_le (j : ℤ) {G : 𝔼 → ℝ≥0∞} (hG : Measurable G) (x : 𝔼) :
    ∫⁻ y, Phi j y * G (x - y) ≤ KP d * cmxHLS_Md G x := by
  set s : ℝ := (2:ℝ) ^ j with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) j
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (s ^ d * 2 ^ (d + 1) / ((2:ℝ) ^ k) ^ (d + 1)) with hc
  set ρ : ℕ → ℝ := fun k => (2:ℝ) ^ k / s with hρ
  have hρ0 : ∀ k, 0 < ρ k := fun k => by positivity
  calc ∫⁻ y, Phi j y * G (x - y)
      ≤ ∫⁻ y, ∑' k : ℕ, (ball (0 : 𝔼) (ρ k)).indicator (fun y => c k * G (x - y)) y := by
        refine lintegral_mono fun y => ?_
        calc Phi j y * G (x - y)
            ≤ (∑' k : ℕ, (ball (0 : 𝔼) (ρ k)).indicator (fun _ => c k) y) * G (x - y) :=
              mul_le_mul_left (Phi_le_tsum j y) _
          _ = ∑' k : ℕ, (ball (0 : 𝔼) (ρ k)).indicator (fun y => c k * G (x - y)) y := by
              rw [← ENNReal.tsum_mul_right]
              congr 1; ext k
              by_cases h : y ∈ ball (0 : 𝔼) (ρ k) <;> simp [Set.indicator, h]
    _ = ∑' k : ℕ, ∫⁻ y, (ball (0 : 𝔼) (ρ k)).indicator (fun y => c k * G (x - y)) y := by
        rw [lintegral_tsum]
        intro k
        exact ((measurable_const.mul (hG.comp (measurable_const.sub measurable_id))).indicator
          measurableSet_ball).aemeasurable
    _ ≤ ∑' k : ℕ, c k * (ENNReal.ofReal ((2 * ρ k) ^ d) * volume (closedBall (0 : 𝔼) 1) *
          cmxHLS_Md G x) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [lintegral_ball_shift (c k) hG x (ρ k)]
        refine mul_le_mul_right ?_ _
        exact (lintegral_mono_set ball_subset_closedBall).trans (lintegral_ball_le G x (hρ0 k))
    _ = KP d * cmxHLS_Md G x := by
        have h1 : ∀ k : ℕ, c k * (ENNReal.ofReal ((2 * ρ k) ^ d) * volume (closedBall (0 : 𝔼) 1) *
            cmxHLS_Md G x) =
            ENNReal.ofReal (2 ^ (2 * d + 1) * (1 / 2) ^ k) * (volume (closedBall (0 : 𝔼) 1) *
            cmxHLS_Md G x) := by
          intro k
          have h2 : c k * ENNReal.ofReal ((2 * ρ k) ^ d) =
              ENNReal.ofReal (2 ^ (2 * d + 1) * (1 / 2) ^ k) := by
            rw [hc]
            simp only
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            simp only [hρ]
            have hk : (2:ℝ) ^ k ≠ 0 := by positivity
            have hs' : s ≠ 0 := hs0.ne'
            have hsd : s ^ d ≠ 0 := pow_ne_zero _ hs'
            rw [← mul_div_assoc, div_pow, one_div_pow]
            field_simp
            ring
          rw [← mul_assoc, ← mul_assoc, h2, mul_assoc]
        simp_rw [h1]
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
        · rw [tsum_mul_left, tsum_geometric_two]
          unfold KP
          rw [mul_assoc]
          congr 2
          rw [show (4:ℝ) ^ (d + 1) = 2 ^ (2 * d + 1) * 2 by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring]
        · exact (summable_geometric_two.mul_left _)

/-- convolution of `H` with the majorant kernel `Phi j` -/
def CvP (j : ℤ) (H : 𝔼 → ℝ≥0∞) (x : 𝔼) : ℝ≥0∞ := ∫⁻ y, Phi j y * H (x - y)

lemma CvP_measurable (j : ℤ) {H : 𝔼 → ℝ≥0∞} (hH : Measurable H) : Measurable (CvP j H) := by
  unfold CvP
  exact Measurable.lintegral_prod_right'
    (f := fun p : 𝔼 × 𝔼 => Phi j p.2 * H (p.1 - p.2))
    (((Phi_measurable j).comp measurable_snd).mul (hH.comp (measurable_fst.sub measurable_snd)))

lemma CvP_le (j : ℤ) {H : 𝔼 → ℝ≥0∞} (hH : Measurable H) (x : 𝔼) :
    CvP j H x ≤ KP d * cmxHLS_Md H x := lintegral_Phi_le j hH x

/-- duality: `∫ (Phi_j * H) w = ∫ H (Phi_j * w)` -/
lemma lintegral_CvP_mul (j : ℤ) {H w : 𝔼 → ℝ≥0∞} (hH : Measurable H) (hw : Measurable w) :
    ∫⁻ x, CvP j H x * w x = ∫⁻ z, H z * CvP j w z := by
  unfold CvP
  have m1 : Measurable (fun p : 𝔼 × 𝔼 => Phi j p.2 * H (p.1 - p.2) * w p.1) :=
    (((Phi_measurable j).comp measurable_snd).mul
      (hH.comp (measurable_fst.sub measurable_snd))).mul (hw.comp measurable_fst)
  have m2 : Measurable (fun p : 𝔼 × 𝔼 => Phi j p.2 * (H p.1 * w (p.1 - p.2))) :=
    ((Phi_measurable j).comp measurable_snd).mul
      ((hH.comp measurable_fst).mul (hw.comp (measurable_fst.sub measurable_snd)))
  calc ∫⁻ x, (∫⁻ y, Phi j y * H (x - y)) * w x
      = ∫⁻ x, ∫⁻ y, Phi j y * H (x - y) * w x := by
        refine lintegral_congr fun x => ?_
        have hm : Measurable (fun y : 𝔼 => Phi j y * H (x - y)) :=
          (Phi_measurable j).mul (hH.comp (measurable_const.sub measurable_id))
        rw [← lintegral_mul_const _ hm]
    _ = ∫⁻ y, ∫⁻ x, Phi j y * H (x - y) * w x := by
        exact lintegral_lintegral_swap m1.aemeasurable
    _ = ∫⁻ y, ∫⁻ z, Phi j y * (H z * w (z + y)) := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_add_right_eq_self (fun x => Phi j y * H (x - y) * w x) y]
        refine lintegral_congr fun z => ?_
        simp [mul_assoc]
    _ = ∫⁻ z, ∫⁻ y, Phi j y * (H z * w (z + y)) := by
        refine lintegral_lintegral_swap ?_
        exact (((Phi_measurable j).comp measurable_fst).mul
          ((hH.comp measurable_snd).mul (hw.comp (measurable_snd.add measurable_fst)))).aemeasurable
    _ = ∫⁻ z, H z * ∫⁻ y, Phi j y * w (z - y) := by
        refine lintegral_congr fun z => ?_
        have h1 : ∫⁻ y, Phi j y * (H z * w (z + y)) = H z * ∫⁻ y, Phi j y * w (z + y) := by
          have hm : Measurable (fun y : 𝔼 => Phi j y * w (z + y)) :=
            (Phi_measurable j).mul (hw.comp (measurable_const.add measurable_id))
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun y => ?_
          ring
        rw [h1]
        congr 1
        rw [← lintegral_neg_eq_self (fun y => Phi j y * w (z + y))]
        refine lintegral_congr fun y => ?_
        simp [Phi_neg, sub_eq_add_neg]

/-- The basic duality step: if `∫ T w ≤ A ∫ Hs · M w` for all measurable `w` and `∫ T^s < ∞`,
then `‖T‖_s ≲ A ‖Hs‖_s`. -/
lemma dual_Lp_bound (hd : 1 ≤ d) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ≥0, ∀ (T Hs : 𝔼 → ℝ≥0∞) (A : ℝ≥0∞), Measurable T → Measurable Hs →
      ∫⁻ x, T x ^ s ≠ ⊤ →
      (∀ w : 𝔼 → ℝ≥0∞, Measurable w → ∫⁻ x, T x * w x ≤ A * ∫⁻ x, Hs x * cmxHLS_Md w x) →
      ∫⁻ x, T x ^ s ≤ ((C : ℝ≥0∞) * A) ^ s * ∫⁻ x, Hs x ^ s := by
  set t : ℝ := s.conjExponent with ht
  have hconj : s.HolderConjugate t := Real.HolderConjugate.conjExponent hs
  have ht1 : 1 < t := (Real.holderConjugate_iff.1 hconj.symm).1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hst : 1 / s + 1 / t = 1 := by
    have := hconj.inv_add_inv_eq_one
    simpa [one_div] using this
  have hst2 : (s - 1) * t = s := by
    have h1 : 1 / t = 1 - 1 / s := by linarith
    have h2 : t = 1 / (1 - 1 / s) := by rw [← h1]; field_simp
    rw [h2]
    have : s - 1 ≠ 0 := by linarith
    field_simp
  obtain ⟨CM, hCM⟩ := Mx_strong hd ht1
  refine ⟨CM ^ (1 / t), fun T Hs A hT hHs hfin hdual => ?_⟩
  rw [ENNReal.coe_rpow_of_nonneg CM (one_div_nonneg.2 ht0.le)]
  set X : ℝ≥0∞ := ∫⁻ x, T x ^ s with hX
  set I : ℝ≥0∞ := ∫⁻ x, Hs x ^ s with hI
  set w : 𝔼 → ℝ≥0∞ := fun x => T x ^ (s - 1) with hw
  have hwm : Measurable w := hT.pow_const _
  have hTw : ∀ x, T x * w x = T x ^ s := by
    intro x
    simp only [hw]
    calc T x * T x ^ (s - 1) = T x ^ (1:ℝ) * T x ^ (s - 1) := by rw [ENNReal.rpow_one]
      _ = T x ^ ((1:ℝ) + (s - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (s - 1) (by norm_num) (by linarith)).symm
      _ = T x ^ s := by congr 1; ring
  have hwt : ∀ x, w x ^ t = T x ^ s := by
    intro x
    simp only [hw]
    rw [← ENNReal.rpow_mul, hst2]
  have h1 : X ≤ A * ∫⁻ x, Hs x * cmxHLS_Md w x := by
    have := hdual w hwm
    simpa only [hTw] using this
  have h2 : ∫⁻ x, Hs x * cmxHLS_Md w x ≤ I ^ (1 / s) * (CM * X) ^ (1 / t) := by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj (f := Hs) (g := cmxHLS_Md w)
      hHs.aemeasurable (cmxHLS_Md_measurable hwm).aemeasurable
    refine hH.trans ?_
    gcongr
    refine (hCM w hwm).trans ?_
    gcongr
    exact (lintegral_congr fun x => hwt x).le
  have h3 : X ≤ A * (I ^ (1 / s) * (CM ^ (1 / t) * X ^ (1 / t))) := by
    refine h1.trans ?_
    refine mul_le_mul_right ?_ _
    refine h2.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  by_cases hX0 : X = 0
  · rw [hX0]; simp
  have hXtop : X ≠ ⊤ := hfin
  have hsplit : X = X ^ (1 / s) * X ^ (1 / t) := by
    rw [← ENNReal.rpow_add _ _ hX0 hXtop, hst, ENNReal.rpow_one]
  have hpos : X ^ (1 / t) ≠ 0 := by
    intro h; rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with h | h
    · exact hX0 h.1
    · linarith [h.2, one_div_pos.2 ht0]
  have hfin2 : X ^ (1 / t) ≠ ⊤ := by
    intro h; rw [ENNReal.rpow_eq_top_iff] at h
    rcases h with h | h
    · linarith [h.2, one_div_pos.2 ht0]
    · exact hXtop h.1
  have h4 : X ^ (1 / s) ≤ (CM ^ (1 / t) * A) * I ^ (1 / s) := by
    have : X ^ (1 / s) * X ^ (1 / t) ≤ ((CM ^ (1 / t) * A) * I ^ (1 / s)) * X ^ (1 / t) := by
      calc X ^ (1 / s) * X ^ (1 / t) = X := hsplit.symm
        _ ≤ _ := h3
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left hpos hfin2).mp this
  calc X = (X ^ (1 / s)) ^ s := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
    _ ≤ ((CM ^ (1 / t) * A) * I ^ (1 / s)) ^ s := ENNReal.rpow_le_rpow h4 hs0.le
    _ = (CM ^ (1 / t) * A) ^ s * I := by
        have hI' : (I ^ (1 / s)) ^ s = I := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, hI']

/-! ### Sums over `ℤ` as increasing limits of finite sums -/

/-- the exhausting finsets of `ℤ` -/
def Fn (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

lemma Fn_mono : Monotone Fn := by
  intro m n hmn z hz
  simp only [Fn, Finset.mem_Icc] at hz ⊢
  have : (m : ℤ) ≤ n := by exact_mod_cast hmn
  constructor <;> linarith [hz.1, hz.2]

lemma tsum_eq_iSup_Fn (f : ℤ → ℝ≥0∞) : ∑' j, f j = ⨆ n : ℕ, ∑ j ∈ Fn n, f j := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine le_antisymm (iSup_le fun F => ?_) (iSup_le fun n => ?_)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, F ⊆ Fn n := by
      by_cases hF : F.Nonempty
      · refine ⟨(F.sup' hF Int.natAbs), fun z hz => ?_⟩
        simp only [Fn, Finset.mem_Icc]
        have : z.natAbs ≤ F.sup' hF Int.natAbs := Finset.le_sup' Int.natAbs hz
        omega
      · refine ⟨0, ?_⟩
        rw [Finset.not_nonempty_iff_eq_empty.1 hF]; exact Finset.empty_subset _
    exact le_iSup_of_le n (Finset.sum_le_sum_of_subset hn)
  · exact le_iSup_of_le (Fn n) le_rfl

lemma lintegral_rpow_iSup {g : ℕ → 𝔼 → ℝ≥0∞} (hg : ∀ n, Measurable (g n)) (hmono : Monotone g)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, (⨆ n, g n x) ^ p = ⨆ n, ∫⁻ x, g n x ^ p := by
  rw [← lintegral_iSup]
  · congr 1; ext x
    exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
        (ENNReal.monotone_rpow_of_nonneg hp.le) (ENNReal.zero_rpow_of_pos hp)
  · intro n; exact (hg n).pow_const _
  · intro m n hmn x
    exact ENNReal.rpow_le_rpow (hmono hmn x) hp.le

/-- a finite sum of `L^s` functions is `L^s` -/
lemma lintegral_finsum_rpow_ne_top {s : ℝ} (hs : 1 ≤ s) (F : Finset ℤ) {a : ℤ → 𝔼 → ℝ≥0∞}
    (ha : ∀ j, Measurable (a j)) (hfin : ∀ j ∈ F, ∫⁻ x, a j x ^ s ≠ ⊤) :
    ∫⁻ x, (∑ j ∈ F, a j x) ^ s ≠ ⊤ := by
  have hs0 : 0 < s := by linarith
  have hpt : ∀ x, (∑ j ∈ F, a j x) ^ s ≤ ((F.card : ℝ≥0∞)) ^ s * ∑ j ∈ F, a j x ^ s := by
    intro x
    have hB : ∀ j ∈ F, a j x ≤ (∑ k ∈ F, a k x ^ s) ^ (1 / s) := by
      intro j hj
      calc a j x = (a j x ^ s) ^ (1 / s) := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one]
        _ ≤ _ := ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun k => a k x ^ s)
              (fun _ _ => bot_le) hj) (by positivity)
    have h1 : ∑ j ∈ F, a j x ≤ (F.card : ℝ≥0∞) * (∑ k ∈ F, a k x ^ s) ^ (1 / s) := by
      calc ∑ j ∈ F, a j x ≤ ∑ j ∈ F, (∑ k ∈ F, a k x ^ s) ^ (1 / s) := Finset.sum_le_sum hB
        _ = _ := by simp
    calc (∑ j ∈ F, a j x) ^ s ≤ ((F.card : ℝ≥0∞) * (∑ k ∈ F, a k x ^ s) ^ (1 / s)) ^ s :=
          ENNReal.rpow_le_rpow h1 hs0.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ← ENNReal.rpow_mul, one_div,
            inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  have hc : ((F.card : ℝ≥0∞)) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs0.le (ENNReal.natCast_ne_top _)
  rw [lintegral_const_mul' _ _ hc, lintegral_finsetSum _ (fun j _ => (ha j).pow_const _)]
  refine ENNReal.mul_ne_top hc ?_
  exact (ENNReal.sum_lt_top.2 fun j hj => lt_top_iff_ne_top.2 (hfin j hj)).ne

/-- Positive-kernel vector-valued Fefferman–Stein inequality (`s > 1`):
`‖∑_j Φ_j * H_j‖_s ≲ ‖∑_j H_j‖_s`. -/
lemma conv_pos_strong (hd : 1 ≤ d) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ≥0, ∀ H : ℤ → 𝔼 → ℝ≥0∞, (∀ j, Measurable (H j)) →
      ∫⁻ x, (∑' j, CvP j (H j) x) ^ s ≤ C * ∫⁻ x, (∑' j, H j x) ^ s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C0, hC0⟩ := dual_Lp_bound hd hs
  obtain ⟨CMs, hCMs⟩ := Mx_strong hd hs
  set B : ℝ≥0∞ := ((C0 : ℝ≥0∞) * KP d) ^ s with hB
  have hKPs : KP d ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs0.le KP_ne_top
  have hBtop : B ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hs0.le (ENNReal.mul_ne_top ENNReal.coe_ne_top KP_ne_top)
  refine ⟨max 1 B.toNNReal, fun H hH => ?_⟩
  have hmax : B ≤ ((max 1 B.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    calc B = (B.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hBtop).symm
      _ ≤ _ := by exact_mod_cast le_max_right _ _
  have hC1 : ((max 1 B.toNNReal : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < max 1 B.toNNReal := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact_mod_cast this.ne'
  set Hs : 𝔼 → ℝ≥0∞ := fun x => ∑' j, H j x with hHs
  have hHsm : Measurable Hs := Measurable.ennreal_tsum hH
  by_cases hI : ∫⁻ x, Hs x ^ s = ⊤
  · show _ ≤ _ * ∫⁻ x, Hs x ^ s
    rw [hI, ENNReal.mul_top hC1]; exact le_top
  set T : ℕ → 𝔼 → ℝ≥0∞ := fun n x => ∑ j ∈ Fn n, CvP j (H j) x with hT
  have hTm : ∀ n, Measurable (T n) := fun n =>
    Finset.measurable_sum _ (fun j _ => CvP_measurable j (hH j))
  have hTmono : Monotone T := fun m n hmn x => Finset.sum_le_sum_of_subset (Fn_mono hmn)
  have hsup : ∀ x, ∑' j, CvP j (H j) x = ⨆ n, T n x := fun x => tsum_eq_iSup_Fn _
  have hH_le : ∀ j x, H j x ≤ Hs x := fun j x => ENNReal.le_tsum (f := fun j => H j x) j
  have key : ∀ n, ∫⁻ x, T n x ^ s ≤ B * ∫⁻ x, Hs x ^ s := by
    intro n
    have hfinj : ∀ j, ∫⁻ x, CvP j (H j) x ^ s ≠ ⊤ := by
      intro j
      refine ne_top_of_le_ne_top (b := KP d ^ s * (CMs * ∫⁻ x, Hs x ^ s))
        (ENNReal.mul_ne_top hKPs (ENNReal.mul_ne_top ENNReal.coe_ne_top hI)) ?_
      calc ∫⁻ x, CvP j (H j) x ^ s ≤ ∫⁻ x, (KP d * cmxHLS_Md (H j) x) ^ s :=
            lintegral_mono fun x => ENNReal.rpow_le_rpow (CvP_le j (hH j) x) hs0.le
        _ = KP d ^ s * ∫⁻ x, cmxHLS_Md (H j) x ^ s := by
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le]
            rw [lintegral_const_mul' _ _ hKPs]
        _ ≤ KP d ^ s * (CMs * ∫⁻ x, (H j x) ^ s) := by
            gcongr; exact hCMs _ (hH j)
        _ ≤ _ := by
            refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
            exact lintegral_mono fun x => ENNReal.rpow_le_rpow (hH_le j x) hs0.le
    have hTfin : ∫⁻ x, T n x ^ s ≠ ⊤ :=
      lintegral_finsum_rpow_ne_top hs.le (Fn n) (fun j => CvP_measurable j (hH j))
        (fun j _ => hfinj j)
    have hdual : ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
        ∫⁻ x, T n x * w x ≤ KP d * ∫⁻ x, Hs x * cmxHLS_Md w x := by
      intro w hw
      calc ∫⁻ x, T n x * w x = ∑ j ∈ Fn n, ∫⁻ x, CvP j (H j) x * w x := by
              simp_rw [hT, Finset.sum_mul]
              rw [lintegral_finsetSum]
              intro j _
              exact (CvP_measurable j (hH j)).mul hw
        _ = ∑ j ∈ Fn n, ∫⁻ z, H j z * CvP j w z :=
              Finset.sum_congr rfl fun j _ => lintegral_CvP_mul j (hH j) hw
        _ ≤ ∑ j ∈ Fn n, ∫⁻ z, H j z * (KP d * cmxHLS_Md w z) :=
              Finset.sum_le_sum fun j _ =>
                lintegral_mono fun z => mul_le_mul_right (CvP_le j hw z) _
        _ = KP d * ∫⁻ z, (∑ j ∈ Fn n, H j z) * cmxHLS_Md w z := by
              rw [← lintegral_const_mul' _ _ KP_ne_top]
              rw [← lintegral_finsetSum]
              · refine lintegral_congr fun z => ?_
                rw [Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by ring
              · intro j _
                exact (hH j).mul ((cmxHLS_Md_measurable hw).const_mul _)
        _ ≤ KP d * ∫⁻ z, Hs z * cmxHLS_Md w z := by
              gcongr with z
              exact ENNReal.sum_le_tsum _
    exact hC0 (T n) Hs (KP d) (hTm n) hHsm hTfin hdual
  calc ∫⁻ x, (∑' j, CvP j (H j) x) ^ s = ⨆ n, ∫⁻ x, T n x ^ s := by
        simp_rw [hsup]
        exact lintegral_rpow_iSup hTm hTmono hs0
    _ ≤ B * ∫⁻ x, Hs x ^ s := iSup_le key
    _ ≤ _ := by gcongr

end HRS.Commutator.Whole.XLI
