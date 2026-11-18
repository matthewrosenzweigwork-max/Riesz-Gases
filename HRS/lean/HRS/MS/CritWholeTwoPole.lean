import HRS.MS.CritWholeTTDefs
import HRS.MS.CritWholeCap
import HRS.Commutator.Whole.ExternalAuxHLS5

/-!
# S8.1 XS, TT02: uniform finite moments of the integrated two-pole kernel

Route (replaces the Young step of the Pro note by the proved HLS inequality `cmxHLS_kernel`): with `k = 1_{|z|<1} g`,
`g ≤ k + 1`, so `J_x(z) ≤ M (I_{d/2} k(x-·))(z) + C`; `I_{d/2}` maps `L^p → L^Q`, `1/Q = 1/p - 1/2`, and `k ∈ L^p`
for `p < 2`.  The moment `q` is obtained from the moment `q+1 ≥ 3` by `J^q ≤ 1 + J^{q+1}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81b

variable {d : ℕ}

/-- `k = 1_{|z|<1} g` as an extended nonnegative function. -/
def kE (d : ℕ) : Euc d → ℝ≥0∞ := (Metric.ball (0 : Euc d) 1).indicator fun w => ENNReal.ofReal (critG d w)

theorem s81b_kE_meas (hd : 1 ≤ d) : Measurable (kE d) := by
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  exact (ENNReal.measurable_ofReal.comp (Q34.measurable_rieszKernel hs0)).indicator
    Metric.isOpen_ball.measurableSet

theorem s81b_kE_neg (w : Euc d) : kE d (-w) = kE d w := by
  simp only [kE, Set.indicator, Metric.mem_ball, dist_zero_right, norm_neg]
  have : critG d (-w) = critG d w := by simp [critG, rieszKernel, norm_neg]
  rw [this]

theorem s81b_critG_eq (hd : 1 ≤ d) (w : Euc d) : critG d w = ‖w‖ ^ (-((d : ℝ) / 2)) := by
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  exact Q34.rieszKernel_eq hs0 w

theorem s81b_ofReal_g_le (hd : 1 ≤ d) (w : Euc d) : ENNReal.ofReal (critG d w) ≤ kE d w + 1 := by
  by_cases hw : ‖w‖ < 1
  · have : w ∈ Metric.ball (0 : Euc d) 1 := by simpa using hw
    simp only [kE, Set.indicator_of_mem this]
    exact le_self_add
  · replace hw := not_lt.1 hw
    have h1 : critG d w ≤ 1 := by
      rw [s81b_critG_eq hd]
      exact Real.rpow_le_one_of_one_le_of_nonpos hw (by
        have : 0 ≤ (d : ℝ) / 2 := by positivity
        linarith)
    calc ENNReal.ofReal (critG d w) ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
      _ ≤ _ := le_add_self

theorem s81b_critG_nonneg (hd : 1 ≤ d) (w : Euc d) : 0 ≤ critG d w := by
  rw [s81b_critG_eq hd]; exact Real.rpow_nonneg (norm_nonneg _) _

theorem s81b_lintegral_kE (hd : 1 ≤ d) :
    ∫⁻ w, kE d w = ENNReal.ofReal (sphereArea d * (1 ^ ((d : ℝ) - (d : ℝ) / 2) / ((d : ℝ) - (d : ℝ) / 2))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [kE, lintegral_indicator Metric.isOpen_ball.measurableSet]
  rw [← Q34.lintegral_ball_rpow hd (a := (d : ℝ) / 2) one_pos (by linarith)]
  refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w _ => ?_
  rw [s81b_critG_eq hd]

theorem s81b_lintegral_kE_pow (hd : 1 ≤ d) {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    ∫⁻ w, kE d w ^ p = ENNReal.ofReal (sphereArea d * (1 ^ ((d : ℝ) - p * ((d : ℝ) / 2)) /
      ((d : ℝ) - p * ((d : ℝ) / 2)))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e : ∀ w : Euc d, kE d w ^ p = (Metric.ball (0 : Euc d) 1).indicator
      (fun w => ENNReal.ofReal (‖w‖ ^ (-(p * ((d : ℝ) / 2))))) w := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : Euc d) 1
    · simp only [kE, Set.indicator_of_mem hw]
      rw [s81b_critG_eq hd, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp0.le,
        ← Real.rpow_mul (norm_nonneg _)]
      congr 2; ring
    · simp [kE, Set.indicator_of_notMem hw, hp0]
  simp_rw [e]
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
  exact Q34.lintegral_ball_rpow hd (a := p * ((d : ℝ) / 2)) one_pos (by nlinarith)

open HRS.Commutator.Whole in
theorem s81b_twoPole_le (hd : 1 ≤ d) {M : ℝ} {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    (hbound : ∀ x, ρ x ≤ M) (x z : Euc d) :
    twoPole ρ x z ≤ ENNReal.ofReal M * cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z +
      (2 * (ENNReal.ofReal M * ∫⁻ w, kE d w) + 1) := by
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hm := s81b_kE_meas hd
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hbound 0)
  have m1 : Measurable fun y : Euc d => kE d (x - y) := hm.comp (measurable_const.sub measurable_id)
  have m2 : Measurable fun y : Euc d => kE d (y - z) := hm.comp (measurable_id.sub measurable_const)
  have step1 : twoPole ρ x z ≤ ∫⁻ y, (kE d (x - y) * kE d (y - z) + kE d (x - y) + kE d (y - z) + 1)
      ∂(withDensityReal ρ) := by
    refine lintegral_mono fun y => ?_
    rw [ENNReal.ofReal_mul (s81b_critG_nonneg hd _)]
    calc ENNReal.ofReal (critG d (x - y)) * ENNReal.ofReal (critG d (y - z))
        ≤ (kE d (x - y) + 1) * (kE d (y - z) + 1) :=
          mul_le_mul' (s81b_ofReal_g_le hd _) (s81b_ofReal_g_le hd _)
      _ = _ := by ring
  refine step1.trans ?_
  have mA : Measurable fun y => kE d (x - y) * kE d (y - z) := m1.mul m2
  have mAB : Measurable fun y => kE d (x - y) * kE d (y - z) + kE d (x - y) := mA.add m1
  have mABC : Measurable fun y => kE d (x - y) * kE d (y - z) + kE d (x - y) + kE d (y - z) :=
    mAB.add m2
  rw [lintegral_add_left mABC, lintegral_add_left mAB, lintegral_add_left mA]
  have hA : ∫⁻ y, kE d (x - y) * kE d (y - z) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal M * cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z := by
    rw [Q34.lintegral_nu hρ (fun y => kE d (x - y) * kE d (y - z)) mA]
    calc ∫⁻ y, ENNReal.ofReal (ρ y) * (kE d (x - y) * kE d (y - z))
        ≤ ∫⁻ y, ENNReal.ofReal M * (kE d (x - y) * kE d (y - z)) :=
          lintegral_mono fun y => by gcongr; exact hbound y
      _ = ENNReal.ofReal M * ∫⁻ y, kE d (x - y) * kE d (y - z) := lintegral_const_mul _ (m1.mul m2)
      _ ≤ _ := by
          gcongr
          unfold cmxHLS_I
          refine lintegral_mono fun y => ?_
          rw [mul_comm]
          gcongr
          unfold cmxHLS_k
          have e1 : (d : ℝ) / 2 - d = -((d : ℝ) / 2) := by ring
          calc kE d (y - z) ≤ ENNReal.ofReal (critG d (y - z)) := Set.indicator_le_self' (fun _ _ => bot_le) _
            _ = _ := by
              rw [s81b_critG_eq hd, e1, norm_sub_rev]
  have hB : ∫⁻ y, kE d (x - y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal M * ∫⁻ w, kE d w :=
    Q34.lintegral_conv_le hρ hbound (kE d) hm x
  have hC : ∫⁻ y, kE d (y - z) ∂(withDensityReal ρ) ≤ ENNReal.ofReal M * ∫⁻ w, kE d w := by
    have := Q34.lintegral_conv_le hρ hbound (kE d) hm z
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) this
    rw [← neg_sub, s81b_kE_neg]
  have hD : ∫⁻ y, (1 : ℝ≥0∞) ∂(withDensityReal ρ) = 1 := by simp
  calc _ ≤ ENNReal.ofReal M * cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z +
        ENNReal.ofReal M * (∫⁻ w, kE d w) + ENNReal.ofReal M * (∫⁻ w, kE d w) + 1 := by
        rw [hD]; exact add_le_add (add_le_add (add_le_add hA hB) hC) le_rfl
    _ = _ := by ring

theorem s81b_kE_ne_top (d : ℕ) (w : Euc d) : kE d w ≠ ⊤ := by
  unfold kE
  by_cases hw : w ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hw]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem hw]; exact ENNReal.zero_ne_top

open HRS.Commutator.Whole in
theorem s81b_hls_kE (hd : 1 ≤ d) {Q : ℝ} (hQ : 2 < Q) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ x : Euc d,
      ∫⁻ z, cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q ≤ K := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set p : ℝ := 2 * Q / (Q + 2) with hp
  have hQ0 : 0 < Q + 2 := by linarith
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hQ0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hQ0]; linarith
  have hpQ : p < Q := by rw [hp, div_lt_iff₀ hQ0]; nlinarith
  have hrel : 1 / Q = 1 / p - ((d : ℝ) / 2) / d := by
    rw [hp]; field_simp; ring
  obtain ⟨C, hC, hK⟩ := cmxHLS_kernel hd (σ := (d : ℝ) / 2) (p := p) (q := Q) (by positivity) hp1 hpQ hrel
  have hLp := s81b_lintegral_kE_pow hd (p := p) (by linarith) hp2
  refine ⟨ENNReal.ofReal C * (ENNReal.ofReal (sphereArea d * (1 ^ ((d : ℝ) - p * ((d : ℝ) / 2)) /
      ((d : ℝ) - p * ((d : ℝ) / 2))))) ^ (Q / p), ?_, fun x => ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by have : 0 < p := by linarith
                                         positivity) ENNReal.ofReal_ne_top)
  · have hm := s81b_kE_meas hd
    set f : Euc d → ℝ≥0 := fun y => (kE d (x - y)).toNNReal with hf
    have hfm : Measurable f := (hm.comp (measurable_const.sub measurable_id)).ennreal_toNNReal
    have hfe : ∀ y, (f y : ℝ≥0∞) = kE d (x - y) := fun y => ENNReal.coe_toNNReal (s81b_kE_ne_top d _)
    have := hK f hfm
    simp_rw [hfe] at this
    rw [lintegral_sub_left_eq_self (fun w => kE d w ^ p) x, hLp] at this
    exact this

theorem s81b_two_pole_moments (hd : 2 ≤ d) (M : ℝ) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ x : Euc d,
        Measurable (twoPole ρ x) ∧
        (∫⁻ z, twoPole ρ x z ^ q ∂(withDensityReal ρ)) ≤ ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by positivity
  set Q : ℝ := ((q + 1 : ℕ) : ℝ) with hQdef
  have hQ : 2 < Q := by
    rw [hQdef]; push_cast
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  obtain ⟨K, hKtop, hK⟩ := s81b_hls_kE hd1 hQ
  have hL1 : ∫⁻ w, kE d w ≠ ⊤ := by
    rw [s81b_lintegral_kE hd1]; exact ENNReal.ofReal_ne_top
  set L1 := ∫⁻ w, kE d w with hL1def
  have hMeasG : Measurable (critG d) := Q34.measurable_rieszKernel hs0
  -- the finite bound
  set a : ℝ≥0∞ := ENNReal.ofReal (max M 0) with ha
  set c0 : ℝ≥0∞ := 2 * (a * L1) + 1 with hc0
  have hc0top : c0 ≠ ⊤ := by
    rw [hc0]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL1), ENNReal.one_ne_top⟩
  set Bd : ℝ≥0∞ := 1 + 2 ^ (Q - 1) * (a ^ Q * (a * K) + c0 ^ Q) with hBd
  have hBdtop : Bd ≠ ⊤ := by
    rw [hBd]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)⟩
    · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop)
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) hc0top
  refine ⟨Bd.toReal, ENNReal.toReal_nonneg, fun ρ hρ hbound x => ?_⟩
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hbound 0)
  have hmax : max M 0 = M := max_eq_left hM0
  have hTm : Measurable (twoPole ρ x) := by
    unfold twoPole
    have : Measurable fun p : Euc d × Euc d =>
        ENNReal.ofReal (critG d (x - p.2) * critG d (p.2 - p.1)) :=
      ENNReal.measurable_ofReal.comp
        ((hMeasG.comp (measurable_const.sub measurable_snd)).mul
          (hMeasG.comp (measurable_snd.sub measurable_fst)))
    exact Measurable.lintegral_prod_right' this
  refine ⟨hTm, ?_⟩
  rw [ENNReal.ofReal_toReal hBdtop]
  have hm := s81b_kE_meas hd1
  have hIm : Measurable (HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y))) :=
    HRS.Commutator.Whole.cmxHLS_I_measurable _ (hm.comp (measurable_const.sub measurable_id))
  have ha' : a = ENNReal.ofReal M := by rw [ha, hmax]
  have hpt1 : ∀ z, twoPole ρ x z ^ q ≤ 1 + twoPole ρ x z ^ (q + 1) := by
    intro z
    by_cases h : twoPole ρ x z ≤ 1
    · exact (pow_le_one' h q).trans le_self_add
    · exact (pow_le_pow_right₀ (le_of_lt (not_le.1 h)) (Nat.le_succ q)).trans le_add_self
  have hpt2 : ∀ z, twoPole ρ x z ^ (q + 1) ≤ 2 ^ (Q - 1) *
      (a ^ Q * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q + c0 ^ Q) := by
    intro z
    have h1 := s81b_twoPole_le hd1 hρ hbound x z
    rw [← ha'] at h1
    have hQ0 : 0 ≤ Q := by linarith
    calc twoPole ρ x z ^ (q + 1) = twoPole ρ x z ^ Q := (ENNReal.rpow_natCast _ _).symm
      _ ≤ (a * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z + c0) ^ Q :=
          ENNReal.rpow_le_rpow h1 hQ0
      _ ≤ 2 ^ (Q - 1) * ((a * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z) ^ Q + c0 ^ Q) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hQ0]
  have hIQ : ∫⁻ z, HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q
      ∂(withDensityReal ρ) ≤ a * K := by
    rw [Q34.lintegral_nu hρ _ (hIm.pow_const Q)]
    calc _ ≤ ∫⁻ z, a * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q :=
          lintegral_mono fun z => by
            rw [ha']; gcongr; exact hbound z
      _ = a * ∫⁻ z, HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q :=
          lintegral_const_mul _ (hIm.pow_const Q)
      _ ≤ a * K := by gcongr; exact hK x
  have hmeasQ : Measurable fun z => a ^ Q * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2) (fun y => kE d (x - y)) z ^ Q :=
    (hIm.pow_const Q).const_mul _
  have hmeasS : Measurable fun z => a ^ Q * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2)
      (fun y => kE d (x - y)) z ^ Q + c0 ^ Q := hmeasQ.add measurable_const
  calc ∫⁻ z, twoPole ρ x z ^ q ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (1 + twoPole ρ x z ^ (q + 1)) ∂(withDensityReal ρ) := lintegral_mono hpt1
    _ = 1 + ∫⁻ z, twoPole ρ x z ^ (q + 1) ∂(withDensityReal ρ) := by
        rw [lintegral_add_left measurable_const]; simp
    _ ≤ 1 + ∫⁻ z, 2 ^ (Q - 1) * (a ^ Q * HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2)
          (fun y => kE d (x - y)) z ^ Q + c0 ^ Q) ∂(withDensityReal ρ) := by
        gcongr; exact hpt2 _
    _ = 1 + 2 ^ (Q - 1) * (a ^ Q * ∫⁻ z, HRS.Commutator.Whole.cmxHLS_I ((d : ℝ) / 2)
          (fun y => kE d (x - y)) z ^ Q ∂(withDensityReal ρ) + c0 ^ Q) := by
        rw [lintegral_const_mul _ hmeasS, lintegral_add_left hmeasQ,
          lintegral_const_mul _ (hIm.pow_const Q)]
        simp
    _ ≤ Bd := by
        rw [hBd]; gcongr

end HRS.Whole.S81b
