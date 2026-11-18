import HRS.MS.WhoAux3
import HRS.MS.UlTailAux2

/-!
# S54 part 4: decay classes, Leibniz in the weighted norm, derivatives of the cancellation convolution
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- a function with bounded derivatives (up to order `n`) -/
def CbCls (n : ℕ) (φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ n φ ∧ ∃ B : ℝ, ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B

theorem who_u2dec_mul {n : ℕ} {L A : ℝ} {ψ : Euc d → ℝ} (hψ : U2Dec n L A ψ) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ n φ) {B : ℝ} (hB : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) :
    U2Dec n L (A * B * 2 ^ n) (fun y => ψ y * φ y) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  refine ⟨hψ.1.mul hφ, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hψ.1 hφ y (by exact_mod_cast hm)).trans ?_
  have hw := u2Wt_pos (d := d) L y
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hψ.2 0 (Nat.zero_le _) y)
    exact (mul_nonneg_iff_of_pos_right hw).1 this
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
        ‖iteratedFDeriv ℝ (m - i) φ y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * u2Wt L y) * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hψ.2 i hi' y) (by positivity))
          (hB (m - i) (by omega) y) (norm_nonneg _) (by positivity)
    _ = (A * u2Wt L y * B) * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ = (A * u2Wt L y * B) * 2 ^ m := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; rfl
    _ ≤ A * B * 2 ^ n * u2Wt L y := by
        have : (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hm
        calc (A * u2Wt L y * B) * 2 ^ m ≤ (A * u2Wt L y * B) * 2 ^ n :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring

/-- the directional derivative of a function with decay has decay -/
theorem who_u2dec_dir {n : ℕ} {L A : ℝ} {ψ : Euc d → ℝ} (hψ : U2Dec (n + 1) L A ψ) (v : Euc d) :
    U2Dec n L (A * ‖v‖) (fun y => fderiv ℝ ψ y v) := by
  have hd1 : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ ψ) :=
    hψ.1.fderiv_right (by exact_mod_cast le_refl (n + 1))
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := (n : WithTop ℕ∞)) (c := v) (n := m)
    hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have := hψ.2 (m + 1) (by omega) y
  calc ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) ψ y‖ ≤ ‖v‖ * (A * u2Wt L y) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

theorem who_schwartz_u2dec (ψ : SchwartzMap (Euc d) ℝ) (n : ℕ) (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ U2Dec n L A (⇑ψ) :=
  ult_rapid_U2Dec (ult_schwartz_rapid ψ) n L


theorem who_Nsq_mono {r r' : ℕ} (h : r ≤ r') (P : ℝ) (φ : Euc d → ℝ) : Nsq r P φ ≤ Nsq r' P φ := by
  unfold Nsq
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

theorem who_wSq_le_Nsq {r i : ℕ} (hi : i ≤ r) (P : ℝ) (φ : Euc d → ℝ) :
    wSq P (fun x => ‖iteratedFDeriv ℝ i φ x‖) ≤ Nsq r P φ := by
  unfold Nsq
  exact Finset.single_le_sum (f := fun j => wSq P (fun x => ‖iteratedFDeriv ℝ j φ x‖))
    (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))

/-- Leibniz in the weighted norm -/
theorem who_wSq_leibniz {n r : ℕ} {i : ℕ} (hi : i ≤ r) (hrn : r ≤ n) {P : ℝ} {f φ : Euc d → ℝ}
    (hf : ContDiff ℝ n f) (hφ : ContDiff ℝ n φ) {Af : ℝ} (hAf : ∀ l ≤ n, ∀ y, ‖iteratedFDeriv ℝ l f y‖ ≤ Af) :
    wSq P (fun y => ‖iteratedFDeriv ℝ i (fun y => f y * φ y) y‖) ≤
      ENNReal.ofReal ((r + 1) ^ 2 * (2 ^ r * Af) ^ 2) * Nsq r P φ := by
  have hAf0 : 0 ≤ Af := (norm_nonneg _).trans (hAf 0 (Nat.zero_le _) 0)
  set t : ℕ → Euc d → ℝ := fun l y => ((i.choose l : ℝ) * Af) * ‖iteratedFDeriv ℝ (i - l) φ y‖ with ht
  have hpt : ∀ y, ‖iteratedFDeriv ℝ i (fun y => f y * φ y) y‖ ≤ ∑ l ∈ Finset.range (i + 1), t l y := by
    intro y
    refine (norm_iteratedFDeriv_mul_le hf hφ y (by exact_mod_cast hi.trans hrn)).trans ?_
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ n := by have := Finset.mem_range.1 hl; omega
    simp only [ht]
    calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l f y‖ * ‖iteratedFDeriv ℝ (i - l) φ y‖
        ≤ (i.choose l : ℝ) * Af * ‖iteratedFDeriv ℝ (i - l) φ y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hAf l hl' y) (by positivity)) (norm_nonneg _)
      _ = _ := by ring
  have htm : ∀ l, Measurable (t l) := fun l =>
    measurable_const.mul (hφ.continuous_iteratedFDeriv (m := i - l) (by exact_mod_cast (by omega : i - l ≤ n))).norm.measurable
  calc wSq P (fun y => ‖iteratedFDeriv ℝ i (fun y => f y * φ y) y‖)
      ≤ wSq P (fun y => ∑ l ∈ Finset.range (i + 1), t l y) := who_wSq_mono fun y => by
        have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun y => f y * φ y) y)
        exact pow_le_pow_left₀ h0 (hpt y) 2
    _ ≤ ((Finset.range (i + 1)).card : ℝ≥0∞) * ∑ l ∈ Finset.range (i + 1), wSq P (t l) :=
        who_wSq_sum_le _ htm
    _ ≤ ENNReal.ofReal ((r + 1) ^ 2 * (2 ^ r * Af) ^ 2) * Nsq r P φ := by
        have hterm : ∀ l ∈ Finset.range (i + 1), wSq P (t l) ≤
            ENNReal.ofReal ((2 ^ r * Af) ^ 2) * Nsq r P φ := by
          intro l hl
          have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
          have : wSq P (t l) = ENNReal.ofReal (((i.choose l : ℝ) * Af) ^ 2) *
              wSq P (fun y => ‖iteratedFDeriv ℝ (i - l) φ y‖) := who_wSq_smul P _ _
          rw [this]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (who_wSq_le_Nsq (by omega) P φ)
          have hch : (i.choose l : ℝ) ≤ 2 ^ r := by
            have : i.choose l ≤ 2 ^ i := by
              calc i.choose l ≤ ∑ j ∈ Finset.range (i + 1), i.choose j :=
                    Finset.single_le_sum (f := fun j => i.choose j) (fun _ _ => bot_le)
                      (Finset.mem_range.2 (by omega))
                _ = 2 ^ i := Nat.sum_range_choose i
            calc (i.choose l : ℝ) ≤ 2 ^ i := by exact_mod_cast this
              _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hi
          have := mul_le_mul_of_nonneg_right hch hAf0
          exact pow_le_pow_left₀ (by positivity) this 2
        calc ((Finset.range (i + 1)).card : ℝ≥0∞) * ∑ l ∈ Finset.range (i + 1), wSq P (t l)
            ≤ ((i + 1 : ℕ) : ℝ≥0∞) * ∑ l ∈ Finset.range (i + 1),
                ENNReal.ofReal ((2 ^ r * Af) ^ 2) * Nsq r P φ := by
              rw [Finset.card_range]
              exact mul_le_mul' le_rfl (Finset.sum_le_sum hterm)
          _ = ((i + 1 : ℕ) : ℝ≥0∞) * (((i + 1 : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal ((2 ^ r * Af) ^ 2) * Nsq r P φ)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal ((r + 1) ^ 2 * (2 ^ r * Af) ^ 2) * Nsq r P φ := by
              have h1 : ((i + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((r : ℝ) + 1) := by
                rw [← ENNReal.ofReal_natCast]
                exact ENNReal.ofReal_le_ofReal (by exact_mod_cast Nat.succ_le_succ hi)
              have e : ENNReal.ofReal (((r : ℝ) + 1) ^ 2 * (2 ^ r * Af) ^ 2) =
                  ENNReal.ofReal ((r : ℝ) + 1) * (ENNReal.ofReal ((r : ℝ) + 1) *
                    ENNReal.ofReal ((2 ^ r * Af) ^ 2)) := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1; ring
              rw [e]
              calc ((i + 1 : ℕ) : ℝ≥0∞) * (((i + 1 : ℕ) : ℝ≥0∞) *
                    (ENNReal.ofReal ((2 ^ r * Af) ^ 2) * Nsq r P φ))
                  ≤ ENNReal.ofReal ((r : ℝ) + 1) * (ENNReal.ofReal ((r : ℝ) + 1) *
                    (ENNReal.ofReal ((2 ^ r * Af) ^ 2) * Nsq r P φ)) := by gcongr
                _ = _ := by ring


/-- weighted bound for the derivatives of the cancellation convolution -/
theorem who_K_deriv_wSq (hd : 1 ≤ d) {P : ℝ} (hP : 0 ≤ P) (hPd : (d : ℝ) / 2 < P) {κ : Euc d → ℝ} {s : ℝ}
    (hK : UlKer κ s) (hs1 : s + 1 < d) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L A : ℝ} (hL : (d : ℝ) < L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ},
      U2Dec (k + 1) L A h → i ≤ k →
      wSq P (fun x => ‖iteratedFDeriv ℝ i (ultK κ h) x‖) ≤ ENNReal.ofReal C *
        (wSq P (fun x => ‖iteratedFDeriv ℝ i h x‖) +
          (∫⁻ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i h y‖) ^ 2 * wtMass (d := d) P) := by
  obtain ⟨C, hC0, hC⟩ := who_ultK_wSq (F := ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ)
    hd hP hPd hK hs1
  refine ⟨C, hC0, fun {L A} hL hA {k h} hdec hi => ?_⟩
  have hit := (ult_K_iter hd hK hL hA hdec).1 i hi
  have hc : Continuous (iteratedFDeriv ℝ i h) :=
    hdec.1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ k + 1))
  have := hC hc
  simp only [← hit] at this
  exact this


/-- `∫ (1+|y|)^{-2L} ⟨y⟩^{2P}` is finite when `2(L-P) > d` -/
theorem who_rhoMass_lt_top {P L : ℝ} (hP : 0 ≤ P) (hL : (d : ℝ) / 2 < L - P) :
    ∫⁻ y : Euc d, ENNReal.ofReal (u2Wt L y ^ 2 * jbracket y ^ (2 * P)) < ⊤ := by
  have hint : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-(2 * (L - P)))) volume := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]; linarith
  have hle : ∀ y : Euc d, u2Wt L y ^ 2 * jbracket y ^ (2 * P) ≤ (1 + ‖y‖) ^ (-(2 * (L - P))) := by
    intro y
    have hy : 0 < 1 + ‖y‖ := by positivity
    have hjb : jbracket y ≤ 1 + ‖y‖ := by
      unfold jbracket
      rw [Real.sqrt_le_left hy.le]
      nlinarith [norm_nonneg y]
    have h1 : jbracket y ^ (2 * P) ≤ (1 + ‖y‖) ^ (2 * P) :=
      Real.rpow_le_rpow (who_jb_pos y).le hjb (by linarith)
    have h2 : u2Wt L y ^ 2 = (1 + ‖y‖) ^ (-(2 * L)) := by
      unfold u2Wt
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; congr 1; push_cast; ring
    rw [h2]
    calc (1 + ‖y‖) ^ (-(2 * L)) * jbracket y ^ (2 * P)
        ≤ (1 + ‖y‖) ^ (-(2 * L)) * (1 + ‖y‖) ^ (2 * P) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hy.le _)
      _ = (1 + ‖y‖) ^ (-(2 * (L - P))) := by
          rw [← Real.rpow_add hy]; congr 1; ring
  refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hle y)) ?_
  exact hint.lintegral_lt_top

theorem who_sum_sq_le {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ S, f i) ^ 2 ≤ 2 ^ S.card * ∑ i ∈ S, f i ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have h2 : (2 : ℝ≥0∞) ^ (S.card + 1) = 2 ^ S.card * 2 := pow_succ _ _
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, h2]
    calc (f a + ∑ i ∈ S, f i) ^ 2 ≤ 2 * (f a ^ 2 + (∑ i ∈ S, f i) ^ 2) := who_sq_add_le _ _
      _ ≤ 2 * (f a ^ 2 + 2 ^ S.card * ∑ i ∈ S, f i ^ 2) := by gcongr
      _ ≤ 2 ^ S.card * 2 * (f a ^ 2 + ∑ i ∈ S, f i ^ 2) := by
          have h1 : (1 : ℝ≥0∞) ≤ 2 ^ S.card := one_le_pow₀ (by norm_num)
          calc 2 * (f a ^ 2 + 2 ^ S.card * ∑ i ∈ S, f i ^ 2)
              = 2 * f a ^ 2 + 2 ^ S.card * 2 * ∑ i ∈ S, f i ^ 2 := by ring
            _ ≤ 2 ^ S.card * 2 * f a ^ 2 + 2 ^ S.card * 2 * ∑ i ∈ S, f i ^ 2 := by
                gcongr
                calc (2 : ℝ≥0∞) = 1 * 2 := by ring
                  _ ≤ 2 ^ S.card * 2 := by gcongr
            _ = _ := by ring

/-- the `L¹` norm of the derivatives of a product with a decaying factor -/
theorem who_L1_leibniz {n : ℕ} {P L A : ℝ} (hP : 0 ≤ P) (hL : (d : ℝ) / 2 < L - P)
    {ψ φ : Euc d → ℝ} (hψ : U2Dec n L A ψ) (hφ : ContDiff ℝ n φ) {i : ℕ} (hi : i ≤ n) :
    (∫⁻ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => ψ y * φ y) y‖) ^ 2 ≤
      ENNReal.ofReal ((i + 1) * 2 ^ (i + 1) * (2 ^ i * A) ^ 2) *
        (∫⁻ y : Euc d, ENNReal.ofReal (u2Wt L y ^ 2 * jbracket y ^ (2 * P))) * Nsq i P φ := by
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hψ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  set Mρ : ℝ≥0∞ := ∫⁻ y : Euc d, ENNReal.ofReal (u2Wt L y ^ 2 * jbracket y ^ (2 * P)) with hMρ
  set b : ℕ → Euc d → ℝ := fun l y => ‖iteratedFDeriv ℝ (i - l) φ y‖ with hb
  have hbm : ∀ l, Measurable (b l) := fun l =>
    (hφ.continuous_iteratedFDeriv (m := i - l) (by exact_mod_cast (by omega : i - l ≤ n))).norm.measurable
  have hwm : Measurable (u2Wt (d := d) L) := (u2Wt_continuous L).measurable
  -- pointwise bound
  have hreal : ∀ y, ‖iteratedFDeriv ℝ i (fun y => ψ y * φ y) y‖ ≤
      ∑ l ∈ Finset.range (i + 1), ((i.choose l : ℝ) * A) * (u2Wt L y * b l y) := by
    intro y
    refine (norm_iteratedFDeriv_mul_le hψ.1 hφ y (by exact_mod_cast hi)).trans ?_
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ n := by have := Finset.mem_range.1 hl; omega
    calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l ψ y‖ * ‖iteratedFDeriv ℝ (i - l) φ y‖
        ≤ (i.choose l : ℝ) * (A * u2Wt L y) * ‖iteratedFDeriv ℝ (i - l) φ y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hψ.2 l hl' y) (by positivity))
            (norm_nonneg _)
      _ = _ := by simp only [hb]; ring
  have hpt : ∀ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => ψ y * φ y) y‖ ≤
      ∑ l ∈ Finset.range (i + 1), ENNReal.ofReal ((i.choose l : ℝ) * A) *
        (ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y)) := by
    intro y
    refine (ENNReal.ofReal_le_ofReal (hreal y)).trans (le_of_eq ?_)
    have hnn : ∀ l ∈ Finset.range (i + 1), 0 ≤ ((i.choose l : ℝ) * A) * (u2Wt L y * b l y) := fun l _ => by
      have := u2Wt_pos (d := d) L y
      have : 0 ≤ b l y := norm_nonneg _
      positivity
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (u2Wt_pos (d := d) L y).le]
  have hfm : ∀ l, Measurable fun y : Euc d => ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y) := fun l =>
    (ENNReal.measurable_ofReal.comp hwm).mul (ENNReal.measurable_ofReal.comp (hbm l))
  -- integrate
  have hI : ∀ l ∈ Finset.range (i + 1), (∫⁻ y, ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y)) ^ 2 ≤
      Mρ * Nsq i P φ := by
    intro l hl
    have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hcs := who_cs_lintegral (μ := volume)
      (f := fun y => ENNReal.ofReal (u2Wt L y * jbracket y ^ P))
      (g := fun y => ENNReal.ofReal (jbracket y ^ (-P) * b l y))
      (((u2Wt_continuous L).mul (by unfold jbracket; fun_prop : Continuous fun y : Euc d =>
        jbracket y ^ P) |>.measurable |> ENNReal.measurable_ofReal.comp).aemeasurable)
      (ENNReal.measurable_ofReal.comp (((who_jb_cont.measurable.pow_const (-P))).mul (hbm l))).aemeasurable
    have e1 : ∀ y : Euc d, ENNReal.ofReal (u2Wt L y * jbracket y ^ P) * ENNReal.ofReal (jbracket y ^ (-P) * b l y) =
        ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y) := fun y => by
      have hjp : jbracket y ^ P * jbracket y ^ (-P) = 1 := by
        rw [← Real.rpow_add (who_jb_pos y)]; simp
      have hw := u2Wt_pos (d := d) L y
      have hbn : 0 ≤ b l y := norm_nonneg _
      rw [← ENNReal.ofReal_mul (mul_nonneg hw.le (Real.rpow_nonneg (who_jb_pos y).le _)), ← ENNReal.ofReal_mul hw.le]
      congr 1
      calc u2Wt L y * jbracket y ^ P * (jbracket y ^ (-P) * b l y) =
          u2Wt L y * (jbracket y ^ P * jbracket y ^ (-P)) * b l y := by ring
        _ = _ := by rw [hjp]; ring
    have e2 : ∀ y : Euc d, ENNReal.ofReal (u2Wt L y * jbracket y ^ P) ^ 2 =
        ENNReal.ofReal (u2Wt L y ^ 2 * jbracket y ^ (2 * P)) := fun y => by
      have hw := u2Wt_pos (d := d) L y
      rw [← ENNReal.ofReal_pow (mul_nonneg hw.le (Real.rpow_nonneg (who_jb_pos y).le _)), mul_pow]
      congr 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul (who_jb_pos y).le]; congr 1; push_cast; ring
    have e3 : ∀ y : Euc d, ENNReal.ofReal (jbracket y ^ (-P) * b l y) ^ 2 =
        ENNReal.ofReal (wt P y * b l y ^ 2) := fun y => by
      rw [← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg (who_jb_pos y).le _) (norm_nonneg _)), mul_pow]
      congr 2
      unfold wt
      rw [← Real.rpow_natCast, ← Real.rpow_mul (who_jb_pos y).le]; congr 1; push_cast; ring
    simp only [e1, e2, e3] at hcs
    refine hcs.trans (mul_le_mul' le_rfl ?_)
    exact who_wSq_le_Nsq (by omega) P φ
  -- sum up
  have hfin : ∀ l, Measurable fun y : Euc d => ENNReal.ofReal ((i.choose l : ℝ) * A) *
      (ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y)) := fun l => measurable_const.mul (hfm l)
  calc (∫⁻ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => ψ y * φ y) y‖) ^ 2
      ≤ (∑ l ∈ Finset.range (i + 1), ENNReal.ofReal ((i.choose l : ℝ) * A) *
          ∫⁻ y, ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y)) ^ 2 := by
        gcongr
        refine (lintegral_mono hpt).trans (le_of_eq ?_)
        rw [lintegral_finsetSum _ (fun l _ => hfin l)]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 2 ^ (i + 1) * ∑ l ∈ Finset.range (i + 1), (ENNReal.ofReal ((i.choose l : ℝ) * A) *
          ∫⁻ y, ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y)) ^ 2 := by
        simpa using who_sum_sq_le (Finset.range (i + 1)) (fun l => ENNReal.ofReal ((i.choose l : ℝ) * A) *
          ∫⁻ y, ENNReal.ofReal (u2Wt L y) * ENNReal.ofReal (b l y))
    _ ≤ 2 ^ (i + 1) * ∑ l ∈ Finset.range (i + 1), ENNReal.ofReal ((2 ^ i * A) ^ 2) * (Mρ * Nsq i P φ) := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun l hl => ?_)
        rw [mul_pow, ← ENNReal.ofReal_pow (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (hI l hl)
        have hch : (i.choose l : ℝ) ≤ 2 ^ i := by
          have : i.choose l ≤ 2 ^ i := by
            calc i.choose l ≤ ∑ j ∈ Finset.range (i + 1), i.choose j :=
                  Finset.single_le_sum (f := fun j => i.choose j) (fun _ _ => bot_le)
                    (Finset.mem_range.2 (by have := Finset.mem_range.1 hl; omega))
              _ = 2 ^ i := Nat.sum_range_choose i
          exact_mod_cast this
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hch hA0) 2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ENNReal.ofReal (((i : ℝ) + 1) * 2 ^ (i + 1) * (2 ^ i * A) ^ 2) =
            ((i + 1 : ℕ) : ℝ≥0∞) * 2 ^ (i + 1) * ENNReal.ofReal ((2 ^ i * A) ^ 2) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          congr 2
          · rw [← ENNReal.ofReal_natCast]; push_cast; rfl
          · rw [show (2 : ℝ) ^ (i + 1) = ((2 ^ (i + 1) : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast]
            push_cast; rfl
        rw [this]
        ring

end HRS.MS.Who
