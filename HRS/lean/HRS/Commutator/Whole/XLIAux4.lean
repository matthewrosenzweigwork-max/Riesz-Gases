import HRS.Commutator.Whole.XLIAux3

/-!
# X-LI part 4: layer cake, tail estimates for dominated kernels
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma volume_layer (g : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < g} = g := by
  by_cases hg : g = ⊤
  · subst hg
    have : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ⊤} = Set.Ioi 0 := by
      ext t; simp [ENNReal.ofReal_lt_top]
    rw [this, Real.volume_Ioi]
  · have : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < g} = Set.Ioo 0 g.toReal := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      refine and_congr_right fun ht => ?_
      rw [ENNReal.ofReal_lt_iff_lt_toReal ht.le hg]
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hg]

/-- layer-cake representation of a weighted integral -/
lemma lintegral_mul_layer {f G : 𝔼 → ℝ≥0∞} (hf : Measurable f) (hG : Measurable G) :
    ∫⁻ x, f x * G x = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in {x | ENNReal.ofReal t < G x}, f x := by
  have h1 : ∀ x, f x * G x = ∫⁻ t in Set.Ioi (0 : ℝ),
      {x | ENNReal.ofReal t < G x}.indicator f x := by
    intro x
    have : ∫⁻ t in Set.Ioi (0 : ℝ), {x | ENNReal.ofReal t < G x}.indicator f x
        = ∫⁻ t, {t : ℝ | 0 < t ∧ ENNReal.ofReal t < G x}.indicator (fun _ => f x) t := by
      rw [← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun t => ?_
      by_cases h0 : 0 < t <;> by_cases h1 : ENNReal.ofReal t < G x <;>
        simp [Set.indicator, h0, h1]
    have hmeas : MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < G x} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    rw [this, lintegral_indicator_const hmeas, volume_layer, mul_comm]
  have hmeas2 : Measurable (fun p : 𝔼 × ℝ =>
      {x | ENNReal.ofReal p.2 < G x}.indicator f p.1) := by
    have hs : MeasurableSet {p : 𝔼 × ℝ | ENNReal.ofReal p.2 < G p.1} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hG.comp measurable_fst)
    have : (fun p : 𝔼 × ℝ => {x | ENNReal.ofReal p.2 < G x}.indicator f p.1) =
        {p : 𝔼 × ℝ | ENNReal.ofReal p.2 < G p.1}.indicator (fun p => f p.1) := by
      ext p; simp [Set.indicator]
    rw [this]
    exact (hf.comp measurable_fst).indicator hs
  calc ∫⁻ x, f x * G x = ∫⁻ x, ∫⁻ t in Set.Ioi (0 : ℝ),
        {x | ENNReal.ofReal t < G x}.indicator f x := lintegral_congr h1
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x, {x | ENNReal.ofReal t < G x}.indicator f x :=
        lintegral_lintegral_swap (hmeas2.aemeasurable)
    _ = _ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_indicator (measurableSet_lt measurable_const hG)]

/-- step-function majorant of the tail of `Phi` -/
lemma Phi_tail_le_tsum (j : ℤ) {r : ℝ} (hr : 0 < r) (y : 𝔼) :
    (if r ≤ ‖y‖ then Phi j y else 0) ≤ ∑' k : ℕ, (ball (0 : 𝔼) ((2 : ℝ) ^ (k + 1) * r)).indicator
      (fun _ => ENNReal.ofReal (((2:ℝ) ^ j) ^ d * (((2:ℝ) ^ j * (2 : ℝ) ^ k * r) ^ (d + 1))⁻¹)) y := by
  split_ifs with hy
  swap
  · exact zero_le
  set s : ℝ := (2:ℝ) ^ j with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) j
  have hex : ∃ k : ℕ, ‖y‖ < (2 : ℝ) ^ (k + 1) * r := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖y‖ / r) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hr] at hk
    calc ‖y‖ < (2 : ℝ) ^ k * r := hk
      _ ≤ (2 : ℝ) ^ (k + 1) * r := by gcongr; norm_num; omega
  classical
  obtain ⟨k0, hk0spec, hk0min⟩ : ∃ k0 : ℕ, ‖y‖ < (2 : ℝ) ^ (k0 + 1) * r ∧
      ∀ m < k0, ¬ (‖y‖ < (2 : ℝ) ^ (m + 1) * r) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hlow : (2 : ℝ) ^ k0 * r ≤ ‖y‖ := by
    rcases Nat.eq_zero_or_pos k0 with h0 | hk
    · rw [h0]; simpa using hy
    · have := hk0min (k0 - 1) (by omega)
      have e : k0 - 1 + 1 = k0 := by omega
      rw [e] at this
      exact not_lt.1 this
  have hmem : y ∈ ball (0 : 𝔼) ((2 : ℝ) ^ (k0 + 1) * r) := by
    rw [mem_ball_zero_iff]; exact hk0spec
  refine le_trans ?_ (ENNReal.le_tsum k0)
  rw [Set.indicator_of_mem hmem]
  unfold Phi
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < s * (2 : ℝ) ^ k0 * r := by positivity
  have h1 : s * (2 : ℝ) ^ k0 * r ≤ 1 + s * ‖y‖ := by
    have : s * (2 : ℝ) ^ k0 * r ≤ s * ‖y‖ := by
      calc s * (2 : ℝ) ^ k0 * r = s * ((2 : ℝ) ^ k0 * r) := by ring
        _ ≤ s * ‖y‖ := by gcongr
    linarith
  have h2 : (s * (2 : ℝ) ^ k0 * r) ^ (d + 1) ≤ (1 + s * ‖y‖) ^ (d + 1) :=
    pow_le_pow_left₀ hpos.le h1 _
  gcongr

/-- constant of the tail estimate -/
def KT (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * 4 ^ d) * volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)

lemma KT_ne_top : KT d ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne

lemma lintegral_Phi_tail_le (j : ℤ) {G : 𝔼 → ℝ≥0∞} (hG : Measurable G) (x : 𝔼) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ y, (if r ≤ ‖y‖ then Phi j y else 0) * G (x - y) ≤
      KT d * ENNReal.ofReal (((2 : ℝ) ^ j * r)⁻¹) * cmxHLS_Md G x := by
  set s : ℝ := (2:ℝ) ^ j with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) j
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (s ^ d * ((s * (2 : ℝ) ^ k * r) ^ (d + 1))⁻¹) with hc
  set ρ : ℕ → ℝ := fun k => (2 : ℝ) ^ (k + 1) * r with hρ
  have hρ0 : ∀ k, 0 < ρ k := fun k => by positivity
  calc ∫⁻ y, (if r ≤ ‖y‖ then Phi j y else 0) * G (x - y)
      ≤ ∫⁻ y, ∑' k : ℕ, (ball (0 : 𝔼) (ρ k)).indicator (fun y => c k * G (x - y)) y := by
        refine lintegral_mono fun y => ?_
        calc (if r ≤ ‖y‖ then Phi j y else 0) * G (x - y)
            ≤ (∑' k : ℕ, (ball (0 : 𝔼) (ρ k)).indicator (fun _ => c k) y) * G (x - y) :=
              mul_le_mul_left (Phi_tail_le_tsum j hr y) _
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
    _ = KT d * ENNReal.ofReal ((s * r)⁻¹) * cmxHLS_Md G x := by
        have h1 : ∀ k : ℕ, c k * (ENNReal.ofReal ((2 * ρ k) ^ d) * volume (closedBall (0 : 𝔼) 1) *
            cmxHLS_Md G x) =
            ENNReal.ofReal (2 ^ (2 * d) * (s * r)⁻¹ * (1 / 2) ^ k) * (volume (closedBall (0 : 𝔼) 1) *
            cmxHLS_Md G x) := by
          intro k
          have h2 : c k * ENNReal.ofReal ((2 * ρ k) ^ d) =
              ENNReal.ofReal (2 ^ (2 * d) * (s * r)⁻¹ * (1 / 2) ^ k) := by
            rw [hc]
            simp only
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            simp only [hρ]
            have hk : (2:ℝ) ^ k ≠ 0 := by positivity
            have hs' : s ≠ 0 := hs0.ne'
            have hr' : r ≠ 0 := hr.ne'
            rw [one_div_pow, mul_pow, mul_pow, mul_pow, mul_pow]
            field_simp
            ring
          rw [← mul_assoc, ← mul_assoc, h2, mul_assoc]
        simp_rw [h1]
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
        · rw [tsum_mul_left, tsum_geometric_two]
          unfold KT
          have : ENNReal.ofReal (2 ^ (2 * d) * (s * r)⁻¹ * 2) =
              ENNReal.ofReal (2 * 4 ^ d) * ENNReal.ofReal ((s * r)⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (4 : ℝ) ^ d = 2 ^ (2 * d) by
              rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
            ring
          rw [this]
          ring
        · exact (summable_geometric_two.mul_left _)

/-- `ENNReal` form of the average of `‖F‖` over a ball -/
lemma ofReal_setAverage_norm {F : 𝔼 → ℂ} (hF : LocallyIntegrable F volume) (x : 𝔼) {r : ℝ}
    (hr : 0 < r) :
    ENNReal.ofReal (⨍ y in closedBall x r, ‖F y‖) =
      (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖F y‖ₑ := by
  have hint : IntegrableOn F (closedBall x r) := hF.integrableOn_isCompact (isCompact_closedBall x r)
  have h0 := cmxHLS_vol_closedBall_ne_zero x hr
  have h1 := cmxHLS_vol_closedBall_ne_top x r
  rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (by positivity), 
    ENNReal.ofReal_inv_of_pos (by exact ENNReal.toReal_pos h0 h1), ofReal_integral_norm_eq_lintegral_enorm hint]
  simp [Measure.real, ENNReal.ofReal_toReal h1]

/-- Lebesgue differentiation: `|F| ≤ M|F|` almost everywhere -/
lemma enorm_le_Md_ae {F : 𝔼 → ℂ} (hF : LocallyIntegrable F volume) :
    ∀ᵐ x ∂(volume : Measure 𝔼), ‖F x‖ₑ ≤ cmxHLS_Md (fun y => ‖F y‖ₑ) x := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure 𝔼) hF 1]
    with x hx
  have hδ : Tendsto (fun n : ℕ => ((1 / 2 : ℝ)) ^ n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num), Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_Ioi]; positivity
  have h0 := hx (ι := ℕ) (l := atTop) (fun _ => x) _ hδ
    (Eventually.of_forall fun n => by
      simp only [mem_closedBall, dist_self, one_mul]; positivity)
  have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (⨍ y in closedBall x ((1 / 2 : ℝ) ^ n),
      ‖F y - F x‖)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h0
  have h2 := h1.const_add (cmxHLS_Md (fun y => ‖F y‖ₑ) x)
  rw [add_zero] at h2
  refine ge_of_tendsto h2 (Eventually.of_forall fun n => ?_)
  have hr : 0 < ((1 / 2 : ℝ)) ^ n := by positivity
  have hF2 : LocallyIntegrable (fun y => F y - F x) volume := hF.sub (locallyIntegrable_const _)
  rw [ofReal_setAverage_norm hF2 x hr]
  set B := closedBall x ((1 / 2 : ℝ) ^ n) with hB
  have h0' := cmxHLS_vol_closedBall_ne_zero x hr
  have h1' := cmxHLS_vol_closedBall_ne_top x ((1 / 2 : ℝ) ^ n)
  have hmeasF : AEStronglyMeasurable F volume := hF.aestronglyMeasurable
  have hmd : (volume B)⁻¹ * ∫⁻ y in B, ‖F y‖ₑ ≤ cmxHLS_Md (fun y => ‖F y‖ₑ) x := by
    have e : ((1 / 2 : ℝ)) ^ n = (2 : ℝ) ^ (-(n : ℤ)) := by simp [zpow_neg, one_div]
    rw [hB, e]
    exact le_iSup (fun j : ℤ => (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ *
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), ‖F y‖ₑ) (-(n : ℤ))
  have hc : (volume B)⁻¹ * ∫⁻ y in B, ‖F x‖ₑ = ‖F x‖ₑ := by
    rw [setLIntegral_const, mul_comm ((volume B)⁻¹), mul_assoc, ENNReal.mul_inv_cancel h0' h1',
      mul_one]
  have hpt : ∀ y, ‖F x‖ₑ ≤ ‖F y‖ₑ + ‖F y - F x‖ₑ := by
    intro y
    calc ‖F x‖ₑ = ‖F y - (F y - F x)‖ₑ := by congr 1; abel
      _ ≤ ‖F y‖ₑ + ‖F y - F x‖ₑ := enorm_sub_le
  calc ‖F x‖ₑ = (volume B)⁻¹ * ∫⁻ y in B, ‖F x‖ₑ := hc.symm
    _ ≤ (volume B)⁻¹ * ∫⁻ y in B, (‖F y‖ₑ + ‖F y - F x‖ₑ) :=
        mul_le_mul_right (lintegral_mono hpt) _
    _ = (volume B)⁻¹ * (∫⁻ y in B, ‖F y‖ₑ) + (volume B)⁻¹ * ∫⁻ y in B, ‖F y - F x‖ₑ := by
        rw [lintegral_add_left' hmeasF.enorm.restrict, mul_add]
    _ ≤ _ := add_le_add hmd le_rfl

/-! ### Tents -/

/-- `tent E j = {x | B(x, 2^{-j}) ⊆ E}` -/
def tent (E : Set 𝔼) (j : ℤ) : Set 𝔼 := {x | ∀ y, ‖y - x‖ < (2 : ℝ) ^ (-j) → y ∈ E}

lemma tent_subset (E : Set 𝔼) (j : ℤ) : tent E j ⊆ E := by
  intro x hx
  exact hx x (by simpa using zpow_pos (by norm_num : (0 : ℝ) < 2) (-j))

lemma isClosed_tent (E : Set 𝔼) (j : ℤ) : IsClosed (tent E j) := by
  have : tent E j = ⋂ y ∈ Eᶜ, {x : 𝔼 | (2 : ℝ) ^ (-j) ≤ ‖y - x‖} := by
    ext x
    simp only [tent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · intro h y hy
      by_contra hlt
      exact hy (h y (by rw [not_le] at hlt; simpa [norm_sub_rev] using hlt))
    · intro h y hy
      by_contra hy'
      have := h y hy'
      linarith
  rw [this]
  exact isClosed_biInter fun y _ => isClosed_le continuous_const (by fun_prop)

lemma measurableSet_tent (E : Set 𝔼) (j : ℤ) : MeasurableSet (tent E j) :=
  (isClosed_tent E j).measurableSet

/-- the geometric sum used in the tail estimate -/
lemma tail_geom_sum {t : ℝ} (ht : 0 < t) :
    ∑' j : ℤ, (if 1 ≤ (2 : ℝ) ^ j * t then ENNReal.ofReal (((2 : ℝ) ^ j * t)⁻¹) ^ 2 else 0) ≤ 2 := by
  by_cases hex : ∃ j : ℤ, 1 ≤ (2 : ℝ) ^ j * t
  swap
  · push_neg at hex
    have : ∀ j : ℤ, (if 1 ≤ (2 : ℝ) ^ j * t then ENNReal.ofReal (((2 : ℝ) ^ j * t)⁻¹) ^ 2 else 0) = 0 :=
      fun j => by rw [if_neg (not_le.2 (hex j))]
    calc _ = ∑' j : ℤ, (0 : ℝ≥0∞) := tsum_congr this
      _ = 0 := tsum_zero
      _ ≤ 2 := zero_le
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, t < (2 : ℝ) ^ N := pow_unbounded_of_one_lt _ (by norm_num)
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, 1 ≤ (2 : ℝ) ^ z * t → b ≤ z := by
    refine ⟨-(N : ℤ), fun z hz => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 : (2 : ℝ) ^ z ≤ (2 : ℝ) ^ (-(N : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (-(N : ℤ) - 1) * 2 ^ N = 1 / 2 := by
      rw [zpow_sub₀ (by norm_num), zpow_neg, zpow_natCast, zpow_one]
      field_simp
    have h3 : (2 : ℝ) ^ z * t ≤ (2 : ℝ) ^ (-(N : ℤ) - 1) * 2 ^ N := by
      calc (2 : ℝ) ^ z * t ≤ (2 : ℝ) ^ (-(N : ℤ) - 1) * t := by gcongr
        _ ≤ _ := by gcongr
    linarith
  obtain ⟨j0, hj0P, hj0min⟩ := Int.exists_least_of_bdd hbdd hex
  have hf : ∀ j : ℤ, (if 1 ≤ (2 : ℝ) ^ j * t then ENNReal.ofReal (((2 : ℝ) ^ j * t)⁻¹) ^ 2 else 0) ≤
      (if j0 ≤ j then ENNReal.ofReal ((1 / 4 : ℝ) ^ (j - j0).toNat) else 0) := by
    intro j
    by_cases hP : 1 ≤ (2 : ℝ) ^ j * t
    · rw [if_pos hP]
      have hj : j0 ≤ j := hj0min j hP
      rw [if_pos hj]
      rw [← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set n := (j - j0).toNat with hn
      have hjn : j = j0 + n := by omega
      have h2 : (2 : ℝ) ^ j * t = (2 : ℝ) ^ n * ((2 : ℝ) ^ j0 * t) := by
        rw [hjn, zpow_add₀ (by norm_num), zpow_natCast]; ring
      have h3 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ j * t := by
        rw [h2]
        calc (2 : ℝ) ^ n = (2 : ℝ) ^ n * 1 := by ring
          _ ≤ _ := by gcongr
      have h4 : (((2 : ℝ) ^ j * t)⁻¹) ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) h3
      calc (((2 : ℝ) ^ j * t)⁻¹) ^ 2 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 := by gcongr
        _ = (1 / 4 : ℝ) ^ n := by
          rw [← inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    · rw [if_neg hP]; exact zero_le
  have hsum : ∑' j : ℤ, (if j0 ≤ j then ENNReal.ofReal ((1 / 4 : ℝ) ^ (j - j0).toNat) else 0) =
      ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
    have hinj : Function.Injective (fun n : ℕ => j0 + (n : ℤ)) := by
      intro a b h; simpa using h
    have := hinj.tsum_eq (f := fun j : ℤ => if j0 ≤ j then ENNReal.ofReal ((1 / 4 : ℝ) ^ (j - j0).toNat) else 0)
      (by
        intro j hj
        simp only [Function.mem_support, ne_eq] at hj
        by_cases hj' : j0 ≤ j
        · exact ⟨(j - j0).toNat, by simp only; omega⟩
        · exfalso; exact hj (if_neg hj'))
    rw [← this]
    refine tsum_congr fun n => ?_
    simp
  calc _ ≤ ∑' j : ℤ, (if j0 ≤ j then ENNReal.ofReal ((1 / 4 : ℝ) ^ (j - j0).toNat) else 0) :=
        ENNReal.tsum_le_tsum hf
    _ = ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := hsum
    _ = ENNReal.ofReal (∑' n : ℕ, (1 / 4 : ℝ) ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))).symm
    _ ≤ 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

end HRS.Commutator.Whole.XLI
