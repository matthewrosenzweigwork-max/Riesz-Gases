import HRS.MS.SharpBiasAux3

/-!
# HRS.MS.SharpBiasAux4 -- S7.1: the large-`N` `L²` estimate

Packet S71, namespace `HRS.Whole.S71`, helper prefix `s71_`.  The core of "Solving the first-marginal
response" (TeX S L5847-5917), for `N = n + 1` large, `β ∈ [βm, βp]` and a background `ρ ≤ M` satisfying the
sharp insertion bound (`sharp_insertion_rate`, taken as a hypothesis with constants `C0, N0`):

* the exact cavity equation `log θ + β g*(θ-1) μ = D_N + β g*(π_N - ν_n) + λ g*ν_n - log Z`
  (`wr13d_log_theta`) is turned into `z + β K_μ z = P_μ H`, `z = θ - 1`,
  `H = (z - log θ) + D_N + β g*(π_N - ν_n) + λ g*ν_n`;
* the quadratic remainder `|z - log θ| ≤ (log θ)² ≤ 2 ‖log θ‖_∞ |z|` (`‖log θ‖_∞ ≤ C N^{-τ}`, `Aux3`);
* the forcing `‖g*(π_N - ν_n)‖_{L²(μ)} ≤ C N^{-3p/4+1/2}` by `convolution_l2_bound` and the cavity total
  variation `K √(δ_N/N) = K N^{-p/2}`;
* the insertion term `‖D_N/δ_N - 2Aβ^p ρ‖_∞ ≤ C(N^{-θ} + N^{-1})`;
* `s71_main_bound` (positivity of `K_μ`) closes the estimate.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S71

open HRS.MS.Wr HRS.External

variable {d : ℕ} {s : ℝ}

/-! ### Elementary real-variable facts -/

theorem s71_abs_log_le {θ : ℝ} (hθ : 0 < θ) (h : |Real.log θ| ≤ 1) :
    |Real.log θ| ≤ 2 * |θ - 1| := by
  set L := Real.log θ with hL
  have hθe : θ = Real.exp L := (Real.exp_log hθ).symm
  rcases le_or_gt 0 L with h0 | h0
  · have := Real.add_one_le_exp L
    rw [abs_of_nonneg h0, hθe, abs_of_nonneg (by linarith)]
    linarith
  · set u := -L with hu
    have hu0 : 0 < u := by linarith
    have hu1 : u ≤ 1 := by
      have := neg_abs_le L
      have := abs_le.1 h
      linarith [this.1]
    have h1 := Real.add_one_le_exp u
    have hE : Real.exp L * (u + 1) ≤ 1 := by
      calc Real.exp L * (u + 1) ≤ Real.exp L * Real.exp u := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp [hu]
    have hEpos := Real.exp_pos L
    have hE1 : Real.exp L < 1 := Real.exp_lt_one_iff.2 h0
    rw [abs_of_neg h0, hθe, abs_of_neg (by linarith)]
    nlinarith

theorem s71_sub_log_le {θ : ℝ} (hθ : 0 < θ) (h : |Real.log θ| ≤ 1) :
    |θ - 1 - Real.log θ| ≤ (Real.log θ) ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le h
  rwa [Real.exp_log hθ] at this

theorem s71_rpow_mono {N : ℝ} (hN : 1 ≤ N) {a b : ℝ} (h : a ≤ b) : N ^ (-b) ≤ N ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem s71_sqrt_delta (hs : (d : ℝ) / 2 < s) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (deltaN d s N / (N : ℝ)) = (N : ℝ) ^ (-(biasP d s) / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [s74_deltaN hs N, Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0,
    ← Real.rpow_mul hN0.le]
  congr 1
  simp only [biasP]
  ring

theorem s71_kappa {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) {p : ℝ} :
    (((N : ℝ) - 1) * (β / N) ^ p) / (N : ℝ) ^ (1 - p) = β ^ p * (((N : ℝ) - 1) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.div_rpow hβ.le hN0.le, Real.rpow_sub hN0, Real.rpow_one]
  have : (N : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos hN0 p).ne'
  field_simp

/-! ### Reduction of the response estimate -/

section Reduce

variable {ρ : Euc d → ℝ} {M : ℝ}

theorem s71_reduce (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)] {β : ℝ}
    (hβ : 0 < β) {θ D F G : Euc d → ℝ} {lam c δ : ℝ} (hδ : 0 < δ) (hθm : Measurable θ)
    {Cθ : ℝ} (hθ0 : ∀ x, 0 < θ x) (hθC : ∀ x, θ x ≤ Cθ)
    (hθ1 : ∫ x, θ x ∂(withDensityReal ρ) = 1)
    (hH : MemLp (fun x => (θ x - 1 - Real.log (θ x)) + D x + β * F x + lam * G x) 2 (withDensityReal ρ))
    (heq : ∀ x, Real.log (θ x) + β * (∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂(withDensityReal ρ)) =
      D x + β * F x + lam * G x + -c) :
    l2Norm (withDensityReal ρ) (fun x => (θ x - 1) / δ -
        2 * biasConst d s * β ^ biasP d s * responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x) ≤
      l2Norm (withDensityReal ρ) (fun x =>
        ((θ x - 1 - Real.log (θ x)) + D x + β * F x + lam * G x) / δ -
          2 * biasConst d s * β ^ biasP d s * ρ x) := by
  have hθint : Integrable θ (withDensityReal ρ) :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 x)]; exact hθC x)
  have hzL : MemLp (fun x => θ x - 1) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hθm.sub_const 1).aestronglyMeasurable (Cθ + 1) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      have := hθ0 x
      have := hθC x
      constructor <;> linarith [hθ0 x, hθC x, (hθ0 x).le])
  have hz0 : MemL2Zero (withDensityReal ρ) (fun x => θ x - 1) := by
    refine ⟨hzL, ?_⟩
    rw [integral_sub hθint (integrable_const _), hθ1]
    simp
  have hHi : Integrable (fun x => (θ x - 1 - Real.log (θ x)) + D x + β * F x + lam * G x)
      (withDensityReal ρ) := hH.integrable one_le_two
  have h1 := s71_euler_to_response hq hβ hz0 hHi (-c) (fun x => by
    have := heq x
    linarith)
  exact s71_main_bound hq hβ hz0 hH hδ (2 * biasConst d s * β ^ biasP d s) h1

end Reduce

/-! ### The large-`N` estimate -/

theorem s71_l2Norm_add3_le {μ : Measure (Euc d)} {f g h : Euc d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    l2Norm μ (fun x => (f x + g x) + h x) ≤ l2Norm μ f + l2Norm μ g + l2Norm μ h := by
  have h1 : l2Norm μ (fun x => (f x + g x) + h x) ≤ l2Norm μ (fun x => f x + g x) + l2Norm μ h :=
    s71_l2Norm_add_le (f := fun x => f x + g x) (hf.add hg) hh
  have h2 := s71_l2Norm_add_le hf hg
  linarith

/-- Pure real form of the insertion estimate: from `|D/q - 2Aρ| ≤ C0 Y` (`q = (N-1)(β/N)^p`) to
`|D/δ_N - 2Aβ^p ρ| ≤ βp^p(|C0| + 2|A| Mr) Y`, `δ_N = N^{1-p}`. -/
theorem s71_P1_bound {N : ℕ} (hN : 2 ≤ N) {β βp : ℝ} (hβpos : 0 < β) (hββp : β ≤ βp) {p : ℝ} (hp0 : 0 ≤ p)
    {A C0 Mr D ρx Y : ℝ} (hρ0 : 0 ≤ ρx) (hρM : ρx ≤ Mr) (hY0 : 0 ≤ Y) (hinv : ((N : ℝ))⁻¹ ≤ Y)
    (h1 : |D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx| ≤ C0 * Y) :
    |D / (N : ℝ) ^ (1 - p) - 2 * A * β ^ p * ρx| ≤ βp ^ p * (|C0| + 2 * |A| * Mr) * Y := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq0 : 0 < ((N : ℝ) - 1) * (β / N) ^ p :=
    mul_pos (by linarith) (Real.rpow_pos_of_pos (div_pos hβpos hNpos) _)
  have hk := s71_kappa hN hβpos (p := p)
  have hδne : (N : ℝ) ^ (1 - p) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
  have hqne := hq0.ne'
  have hN1ne : (N : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hβNne : (β / (N : ℝ)) ^ p ≠ 0 := (Real.rpow_pos_of_pos (div_pos hβpos hNpos) _).ne'
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hMr0 : 0 ≤ Mr := hρ0.trans hρM
  have hβp0 : 0 ≤ βp := hβpos.le.trans hββp
  have hbp : β ^ p ≤ βp ^ p := Real.rpow_le_rpow hβpos.le hββp hp0
  have hbp0 : 0 ≤ β ^ p := Real.rpow_nonneg hβpos.le _
  have hfrac0 : 0 ≤ ((N : ℝ) - 1) / N := div_nonneg (by linarith) hNpos.le
  have hfrac1 : ((N : ℝ) - 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  have key : D / (N : ℝ) ^ (1 - p) - 2 * A * β ^ p * ρx =
      β ^ p * (((N : ℝ) - 1) / N) * (D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx) -
        β ^ p * (2 * A * ρx) / N := by
    have e1 : D / (N : ℝ) ^ (1 - p) = (D / (((N : ℝ) - 1) * (β / N) ^ p)) *
        ((((N : ℝ) - 1) * (β / N) ^ p) / (N : ℝ) ^ (1 - p)) := by
      field_simp
    rw [e1, hk]
    field_simp
    ring
  rw [key]
  have t1 : |β ^ p * (((N : ℝ) - 1) / N) * (D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx)| ≤
      βp ^ p * (|C0| * Y) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hbp0, abs_of_nonneg hfrac0]
    have h1' : |D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx| ≤ |C0| * Y :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hY0)
    calc β ^ p * (((N : ℝ) - 1) / N) * |D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx|
        ≤ β ^ p * 1 * (|C0| * Y) := by gcongr
      _ ≤ βp ^ p * (|C0| * Y) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right hbp (by positivity)
  have t2 : |β ^ p * (2 * A * ρx) / N| ≤ βp ^ p * (2 * |A| * Mr * Y) := by
    rw [abs_div, abs_of_pos hNpos, abs_mul, abs_of_nonneg hbp0, abs_mul, abs_mul,
      abs_of_nonneg hρ0, abs_two, div_eq_mul_inv]
    calc β ^ p * (2 * |A| * ρx) * ((N : ℝ))⁻¹ ≤ βp ^ p * (2 * |A| * Mr) * Y := by gcongr
      _ = βp ^ p * (2 * |A| * Mr * Y) := by ring
  calc _ ≤ |β ^ p * (((N : ℝ) - 1) / N) * (D / (((N : ℝ) - 1) * (β / N) ^ p) - 2 * A * ρx)| +
      |β ^ p * (2 * A * ρx) / N| := abs_sub _ _
    _ ≤ βp ^ p * (|C0| * Y) + βp ^ p * (2 * |A| * Mr * Y) := add_le_add t1 t2
    _ = _ := by ring


set_option maxHeartbeats 3200000 in
theorem s71_large (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M C0 : ℝ) (N0 : ℕ) :
    ∃ (C : ℝ) (N1 : ℕ), 2 ≤ N1 ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, N0 ≤ N → ∀ x : Euc d,
        |insertionDefect d s N β (withDensityReal ρ) x / (((N : ℝ) - 1) * (β / N) ^ biasP d s) -
            2 * biasConst d s * ρ x| ≤ C0 * (N : ℝ) ^ (-biasTheta d s)) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, N1 ≤ n + 1 →
        MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) / deltaN d s (n + 1) -
            biasDensity d s β ρ x) 2 (withDensityReal ρ) ∧
        l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
            deltaN d s (n + 1) - biasDensity d s β ρ x) ≤
          C * ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  have hpb1 : 1 < biasP d s := hp1
  have hpb2 : biasP d s < 2 := hp2
  obtain ⟨hθ'0, hθ'τ, hθ'2, hθ'1, hτ0, hτ2, hτle, hτ1⟩ := s71_theta_pos_exp hd hs hsd
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  set Mg : ℝ := max (potentialBound d s M) 0 with hMg
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  obtain ⟨C', hC'1, hνC'⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp0
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set Cν : ℝ := max Cθ C' with hCν
  have hCν1 : 1 ≤ Cν := hCθ1.trans (le_max_left _ _)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨K, hK0, hK⟩ := wr13d_event_bound hd hs0 hsd hβm βp M
  obtain ⟨Cc, Nc, hcore⟩ := wr13d_core_L2 hd hs0 hsd hβm hβ M
  obtain ⟨CD, hCD0, hD⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  obtain ⟨CL, Ns, hCL0, hNs2, hsup⟩ := s71_logtheta_sup hd hs hsd hβm hβ M
  obtain ⟨CBM, hCBM⟩ := convolution_l2_bound hd hs hsd (max M 0 * Cν) M
  set e₂ : ℝ := 3 / 2 - s / (d : ℝ) with he₂
  have hsdr : s / (d : ℝ) * biasP d s = 1 := by
    simp only [biasP]; field_simp
  have hsd1 : s / (d : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hsd
  have he₂0 : 0 < e₂ := by rw [he₂]; linarith
  obtain ⟨N2, hN2⟩ := s71_exists_N (2 * K) (biasP d s / 2) (by linarith)
  set C : ℝ := βp ^ biasP d s * (|C0| + 2 * |biasConst d s| * max M 0) + 2 * CL * |Cc| +
    βp * |CBM| * (2 * K) ^ e₂ + βp * Cν * Mg with hC
  refine ⟨C, max (max (max Nc Ns) (max N0 N2)) 2, le_max_right _ _, ?_⟩
  intro ρ hρ hM hIns β hβ1 hββp n hNn
  have h2 : 2 ≤ n + 1 := (le_max_right _ _).trans hNn
  have hAll : max (max Nc Ns) (max N0 N2) ≤ n + 1 := (le_max_left _ _).trans hNn
  have hNc : Nc ≤ n + 1 := ((le_max_left _ _).trans (le_max_left _ _)).trans hAll
  have hNs : Ns ≤ n + 1 := ((le_max_right _ _).trans (le_max_left _ _)).trans hAll
  have hN0' : N0 ≤ n + 1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hAll
  have hN2' : N2 ≤ n + 1 := ((le_max_right _ _).trans (le_max_right _ _)).trans hAll
  have hn : 1 ≤ n := by omega
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hN1r : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hδ : deltaN d s (n + 1) = ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s - 1)) := by
    rw [s74_deltaN hs]; congr 1; simp only [biasP]; ring
  have hδpos : 0 < deltaN d s (n + 1) := by rw [hδ]; exact Real.rpow_pos_of_pos hNpos _
  haveI hμp := wr13a_isProb_density hρ
  have hq : Q34.Q34Hyp d s ρ M := ⟨hd1, hs0, hsd, hρ, hM⟩
  -- the density
  have hθ0 : ∀ x, 0 < wr13d_theta d s n β (withDensityReal ρ) x := s71_theta_pos hd hs0 hsd hρ hM hβ0 n
  have hθm : Measurable (wr13d_theta d s n β (withDensityReal ρ)) := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hθCθ : ∀ x, wr13d_theta d s n β (withDensityReal ρ) x ≤ Cθ :=
    fun x => s71_theta_le hd hs0 hsd hρ hM hβ0 hββp n x
  have hθC : ∀ x, wr13d_theta d s n β (withDensityReal ρ) x ≤ Cν := fun x => (hθCθ x).trans (le_max_left _ _)
  have hθ1 : ∫ x, wr13d_theta d s n β (withDensityReal ρ) x ∂(withDensityReal ρ) = 1 :=
    s71_theta_integral hd hs0 hsd hρ hM hβ0 n
  -- the cavity marginal
  haveI hνp : IsProbabilityMeasure (cavityMarginal d s (n + 1) β (withDensityReal ρ)) :=
    wr13d_cavMarg_isProb hd hs0 hsd hρ hM hβ0 hn
  have hνle : cavityMarginal d s (n + 1) β (withDensityReal ρ) ≤ ENNReal.ofReal Cν • withDensityReal ρ := by
    refine (hνC' ρ hρ hM β hβ0 hββp (n + 1) (by omega)).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact le_max_right _ _
  -- L² bound of θ - 1
  obtain ⟨hz2, hznorm⟩ := hcore ρ hρ hM β hβ1 hββp n hn hNc
  have hzsq : Real.sqrt (∫ x, (wr13d_theta d s n β (withDensityReal ρ) x - 1) ^ 2 ∂(withDensityReal ρ)) ≤
      |Cc| * deltaN d s (n + 1) :=
    wr13d_sqrt_le_of_eLpNorm hz2 (by positivity)
      (hznorm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hδpos.le)))
  -- sup bound of log θ
  obtain ⟨hCLN, hLsup⟩ := hsup ρ hρ hM β hβ1 hββp n hNs
  have hL1 : ∀ x, |Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤ 1 := fun x => (hLsup x).trans hCLN
  -- the convolution term
  have hTV : ∀ A : Set (Euc d), MeasurableSet A →
      |((withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (wr13d_theta d s n β (withDensityReal ρ) y))).real A -
        (cavityMarginal d s (n + 1) β (withDensityReal ρ)).real A| ≤
        K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    have := hK ρ hρ hM β hβ1 hββp n hn A hA
    rwa [wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0 n] at this
  obtain ⟨w, hwm, hwb, hwi, hwL1, hid⟩ := wr13d_cv_prep hd1 hs0 hsd M hCν1 hρ hM hθm hθ0 hθC hνp hνle hTV
  have hsqrt : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) =
      ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2)) := by
    rw [s71_sqrt_delta hs (by omega : 1 ≤ n + 1), neg_div]
  have hε₂ : 2 * (K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) ≤ 1 := by
    have := hN2 (n + 1) hN2'
    rw [hsqrt]; linarith
  obtain ⟨hFL2, hFnorm⟩ := hCBM w hwm hwb hwi _ hε₂ hwL1 ρ hρ hM
  have hint : ∀ x, Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal ρ) :=
    fun x => (wr13a_potential_bound hd1 hs0 hsd hρ hM x).1
  have hDb : ∀ x, 0 ≤ insertionDefect d s (n + 1) β (withDensityReal ρ) x ∧
      insertionDefect d s (n + 1) β (withDensityReal ρ) x ≤ CD * deltaN d s (n + 1) := fun x => by
    obtain ⟨-, h1, h2, -⟩ := hD ρ hρ hM β hβ1 hββp (n + 1) (by omega) x
    exact ⟨h1, h2⟩
  have hQνm : Measurable fun x => ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)) :=
    RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2))
      ((wr13a_g_meas hs0).comp (measurable_fst.sub measurable_snd))
  have hQb : ∀ x, 0 ≤ ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)) ∧
      ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)) ≤ Cν * Mg := fun x => by
    obtain ⟨h1, h2⟩ := wr13d_conv_nu_le hd1 hs0 hsd hρ hM hCν0 hνle x
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCν0)⟩
  have hlogθ := wr13d_log_theta hd hs0 hsd hρ hM hβ0 hn
  have hDm : Measurable (fun x => insertionDefect d s (n + 1) β (withDensityReal ρ) x) := by
    have e : (fun x => insertionDefect d s (n + 1) β (withDensityReal ρ) x) = fun x =>
        Real.log (wr13d_theta d s n β (withDensityReal ρ) x) -
          β * convMeasure (rieszKernel d s) (withDensityReal ρ) x +
        (β / ((n + 1 : ℕ) : ℝ)) * n *
          (∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) +
          Real.log (wr13d_Z d s n β (withDensityReal ρ)) := by
      funext x
      have := hlogθ x
      linarith
    rw [e]
    exact (((Real.measurable_log.comp hθm).sub ((wr13a_conv_meas hs0 (withDensityReal ρ)).const_mul β)).add
      (hQνm.const_mul ((β / ((n + 1 : ℕ) : ℝ)) * n))).add measurable_const
  have hFm : Measurable (fun x => ∫ y, rieszKernel d s (x - y) * w y) :=
    RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * w p.2)
      (((wr13a_g_meas hs0).comp (measurable_fst.sub measurable_snd)).mul (hwm.comp measurable_snd))
  have heq : ∀ x, Real.log (wr13d_theta d s n β (withDensityReal ρ) x) +
      β * (∫ y, rieszKernel d s (x - y) * (wr13d_theta d s n β (withDensityReal ρ) y - 1) ∂(withDensityReal ρ)) =
      insertionDefect d s (n + 1) β (withDensityReal ρ) x +
        β * (∫ y, rieszKernel d s (x - y) * w y) +
        (β / ((n + 1 : ℕ) : ℝ)) * (∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) +
        -Real.log (wr13d_Z d s n β (withDensityReal ρ)) := by
    intro x
    have i1 : Integrable (fun y => rieszKernel d s (x - y) * wr13d_theta d s n β (withDensityReal ρ) y)
        (withDensityReal ρ) :=
      (hint x).mul_bdd hθm.aestronglyMeasurable (c := Cν)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθC y)
    have hKz : ∫ y, rieszKernel d s (x - y) * (wr13d_theta d s n β (withDensityReal ρ) y - 1) ∂(withDensityReal ρ) =
        (∫ y, rieszKernel d s (x - y) * w y) +
          (∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) -
          convMeasure (rieszKernel d s) (withDensityReal ρ) x := by
      have e1 : ∫ y, rieszKernel d s (x - y) * (wr13d_theta d s n β (withDensityReal ρ) y - 1) ∂(withDensityReal ρ) =
          (∫ y, rieszKernel d s (x - y) * wr13d_theta d s n β (withDensityReal ρ) y ∂(withDensityReal ρ)) -
            ∫ y, rieszKernel d s (x - y) ∂(withDensityReal ρ) := by
        rw [← integral_sub i1 (hint x)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring
      rw [e1]
      have := hid x
      unfold convMeasure
      linarith
    have hlog := hlogθ x
    have hlamN : β / ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) = β := by
      push_cast; field_simp
    rw [hKz]
    linear_combination hlog - (∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) * hlamN
  have hPa : MemLp (fun x => wr13d_theta d s n β (withDensityReal ρ) x - 1 -
      Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) 2 (withDensityReal ρ) :=
    MemLp.of_bound ((hθm.sub_const 1).sub (Real.measurable_log.comp hθm)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        refine (s71_sub_log_le (hθ0 x) (hL1 x)).trans ?_
        have := hL1 x
        nlinarith [abs_nonneg (Real.log (wr13d_theta d s n β (withDensityReal ρ) x)),
          sq_abs (Real.log (wr13d_theta d s n β (withDensityReal ρ) x))])
  have hPb : MemLp (fun x => insertionDefect d s (n + 1) β (withDensityReal ρ) x) 2 (withDensityReal ρ) :=
    MemLp.of_bound hDm.aestronglyMeasurable (CD * deltaN d s (n + 1))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDb x).1]; exact (hDb x).2)
  have hPc : MemLp (fun x => β * ∫ y, rieszKernel d s (x - y) * w y) 2 (withDensityReal ρ) :=
    hFL2.const_mul β
  have hPd : MemLp (fun x => (β / ((n + 1 : ℕ) : ℝ)) *
      ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hQνm.const_mul _).aestronglyMeasurable ((β / ((n + 1 : ℕ) : ℝ)) * (Cν * Mg))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg hβ0 hNpos.le) (hQb x).1)]
        exact mul_le_mul_of_nonneg_left (hQb x).2 (div_nonneg hβ0 hNpos.le))
  have hH := ((hPa.add hPb).add hPc).add hPd
  have hred := s71_reduce hq hβpos hδpos hθm hθ0 hθC hθ1 hH heq
  -- the final arithmetic
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hNpos _
  have hN2r : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h2
  have f1 : ((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ Y := by rw [hYdef]; exact s71_rpow_mono hN1r hθ'1
  have f2 : ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) ≤ Y := by rw [hYdef]; exact s71_rpow_mono hN1r hθ'τ
  have f3 : ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 2) ≤ Y := by
    rw [hYdef]
    have := s71_rpow_mono hN1r (a := biasTheta d s) (b := 2 - biasP d s) (by linarith)
    simpa using this
  have hexp : (biasP d s - 1) + (-(biasP d s / 2) * e₂) = -((2 - biasP d s) / 4) := by
    rw [he₂]; nlinarith [hsdr]
  have f4 : ((n + 1 : ℕ) : ℝ) ^ ((biasP d s - 1) + (-(biasP d s / 2) * e₂)) ≤ Y := by
    rw [hexp, hYdef]; exact s71_rpow_mono hN1r (by linarith)
  -- P1
  have hP1 : ∀ x, |insertionDefect d s (n + 1) β (withDensityReal ρ) x / deltaN d s (n + 1) -
      2 * biasConst d s * β ^ biasP d s * ρ x| ≤
      βp ^ biasP d s * (|C0| + 2 * |biasConst d s| * max M 0) * Y := by
    intro x
    have hδ' : deltaN d s (n + 1) = ((n + 1 : ℕ) : ℝ) ^ (1 - biasP d s) := by rw [hδ]; congr 1; ring
    rw [hδ']
    have hinv : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ Y := by
      have := f1
      rwa [Real.rpow_neg_one] at this
    refine s71_P1_bound h2 hβpos hββp (by linarith) (hρ.nonneg x) ((hM x).trans (le_max_left _ _)) hY0.le hinv ?_
    have := hIns β hβ1 hββp (n + 1) hN0' x
    rwa [← hYdef] at this
  -- P2
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ((n + 1 : ℕ) : ℝ) ^ (-biasTau d s) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hTdef]; exact Real.rpow_pos_of_pos hNpos _
  have hTY : T ≤ Y := by rw [hTdef]; exact f2
  have hLsup' : ∀ x, |Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤ CL * T := by
    intro x; rw [hTdef]; exact hLsup x
  have hP2 : l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1 -
      Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) / deltaN d s (n + 1)) ≤
      2 * CL * |Cc| * T := by
    have hg : MemLp (fun x => (2 * (CL * T) / deltaN d s (n + 1)) *
        (wr13d_theta d s n β (withDensityReal ρ) x - 1)) 2 (withDensityReal ρ) := hz2.const_mul _
    have hdom : ∀ x, |(wr13d_theta d s n β (withDensityReal ρ) x - 1 -
        Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) / deltaN d s (n + 1)| ≤
        |(2 * (CL * T) / deltaN d s (n + 1)) * (wr13d_theta d s n β (withDensityReal ρ) x - 1)| := by
      intro x
      have hc0 : 0 ≤ 2 * (CL * T) / deltaN d s (n + 1) := by positivity
      rw [abs_mul, abs_of_nonneg hc0, abs_div, abs_of_pos hδpos]
      have h1 := s71_sub_log_le (hθ0 x) (hL1 x)
      have h2 := s71_abs_log_le (hθ0 x) (hL1 x)
      have h3 := hLsup' x
      have h4 : (Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) ^ 2 ≤
          (CL * T) * (2 * |wr13d_theta d s n β (withDensityReal ρ) x - 1|) := by
        rw [← sq_abs, sq]
        exact mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      have h5 : |wr13d_theta d s n β (withDensityReal ρ) x - 1 -
          Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| ≤
          2 * (CL * T) * |wr13d_theta d s n β (withDensityReal ρ) x - 1| := by
        have := h1.trans h4
        linarith
      calc |wr13d_theta d s n β (withDensityReal ρ) x - 1 -
            Real.log (wr13d_theta d s n β (withDensityReal ρ) x)| / deltaN d s (n + 1)
          ≤ 2 * (CL * T) * |wr13d_theta d s n β (withDensityReal ρ) x - 1| / deltaN d s (n + 1) :=
            div_le_div_of_nonneg_right h5 hδpos.le
        _ = 2 * (CL * T) / deltaN d s (n + 1) * |wr13d_theta d s n β (withDensityReal ρ) x - 1| := by ring
    refine (s71_l2Norm_mono hg hdom).trans ?_
    rw [s71_l2Norm_const_mul, abs_of_nonneg (by positivity)]
    have hzn : l2Norm (withDensityReal ρ) (fun x => wr13d_theta d s n β (withDensityReal ρ) x - 1) ≤
        |Cc| * deltaN d s (n + 1) := hzsq
    calc 2 * (CL * T) / deltaN d s (n + 1) *
          l2Norm (withDensityReal ρ) (fun x => wr13d_theta d s n β (withDensityReal ρ) x - 1)
        ≤ 2 * (CL * T) / deltaN d s (n + 1) * (|Cc| * deltaN d s (n + 1)) :=
          mul_le_mul_of_nonneg_left hzn (by positivity)
      _ = 2 * CL * |Cc| * T := by field_simp
  -- P3
  have hδinv : 1 / deltaN d s (n + 1) = ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) := by
    rw [hδ, one_div, ← Real.rpow_neg hNpos.le, neg_neg]
  have hε₂eq : 2 * (K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) =
      (2 * K) * ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2)) := by rw [hsqrt]; ring
  have hε₂pow : (2 * (K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)))) ^ e₂ =
      (2 * K) ^ e₂ * ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2) * e₂) := by
    rw [hε₂eq, Real.mul_rpow (by positivity) (Real.rpow_nonneg hNpos.le _),
      ← Real.rpow_mul hNpos.le]
  have hA : (1 / deltaN d s (n + 1)) * (β * (|CBM| * (2 * (K * Real.sqrt (deltaN d s (n + 1) /
      ((n + 1 : ℕ) : ℝ)))) ^ e₂)) ≤ βp * |CBM| * (2 * K) ^ e₂ * Y := by
    rw [hε₂pow, hδinv]
    have hr : ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2) * e₂) ≤ Y := by
      rw [← Real.rpow_add hNpos]; exact f4
    calc ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * (β * (|CBM| * ((2 * K) ^ e₂ *
          ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2) * e₂))))
        = β * |CBM| * (2 * K) ^ e₂ * (((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) *
          ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s / 2) * e₂)) := by ring
      _ ≤ βp * |CBM| * (2 * K) ^ e₂ * Y := by
          gcongr
  have hB : (1 / deltaN d s (n + 1)) * ((β / ((n + 1 : ℕ) : ℝ)) * (Cν * Mg)) ≤ βp * Cν * Mg * Y := by
    rw [hδinv]
    have hr : ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * (((n + 1 : ℕ) : ℝ))⁻¹ ≤ Y := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]
      have : biasP d s - 1 + -1 = biasP d s - 2 := by ring
      rw [this]; exact f3
    calc ((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * (β / ((n + 1 : ℕ) : ℝ) * (Cν * Mg))
        = β * (Cν * Mg) * (((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * (((n + 1 : ℕ) : ℝ))⁻¹) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ βp * Cν * Mg * Y := by
          have : β * (Cν * Mg) ≤ βp * (Cν * Mg) := mul_le_mul_of_nonneg_right hββp (by positivity)
          calc β * (Cν * Mg) * (((n + 1 : ℕ) : ℝ) ^ (biasP d s - 1) * (((n + 1 : ℕ) : ℝ))⁻¹)
              ≤ βp * (Cν * Mg) * Y := mul_le_mul this hr (by positivity) (by positivity)
            _ = βp * Cν * Mg * Y := by ring
  have hP3 : l2Norm (withDensityReal ρ) (fun x => (1 / deltaN d s (n + 1)) *
      (β * (∫ y, rieszKernel d s (x - y) * w y) +
        (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)))) ≤
      βp * |CBM| * (2 * K) ^ e₂ * Y + βp * Cν * Mg * Y := by
    rw [s71_l2Norm_const_mul, abs_of_pos (by positivity)]
    have hsum := s71_l2Norm_add_le hPc hPd
    have hF1 : l2Norm (withDensityReal ρ) (fun x => β * ∫ y, rieszKernel d s (x - y) * w y) ≤
        β * (|CBM| * (2 * (K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)))) ^ e₂) := by
      rw [s71_l2Norm_const_mul, abs_of_nonneg hβ0]
      refine mul_le_mul_of_nonneg_left ?_ hβ0
      refine hFnorm.trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _)
    have hF2 : l2Norm (withDensityReal ρ) (fun x => (β / ((n + 1 : ℕ) : ℝ)) *
        ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) ≤
        (β / ((n + 1 : ℕ) : ℝ)) * (Cν * Mg) := by
      refine s71_l2Norm_le_of_bound (by positivity) (fun x => ?_)
      rw [abs_of_nonneg (mul_nonneg (div_nonneg hβ0 hNpos.le) (hQb x).1)]
      exact mul_le_mul_of_nonneg_left (hQb x).2 (div_nonneg hβ0 hNpos.le)
    calc 1 / deltaN d s (n + 1) * l2Norm (withDensityReal ρ) (fun x => β * (∫ y, rieszKernel d s (x - y) * w y) +
          (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)))
        ≤ 1 / deltaN d s (n + 1) * (β * (|CBM| * (2 * (K * Real.sqrt (deltaN d s (n + 1) /
            ((n + 1 : ℕ) : ℝ)))) ^ e₂) + (β / ((n + 1 : ℕ) : ℝ)) * (Cν * Mg)) :=
          mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hF1 hF2)) (by positivity)
      _ = (1 / deltaN d s (n + 1)) * (β * (|CBM| * (2 * (K * Real.sqrt (deltaN d s (n + 1) /
            ((n + 1 : ℕ) : ℝ)))) ^ e₂)) + (1 / deltaN d s (n + 1)) * ((β / ((n + 1 : ℕ) : ℝ)) * (Cν * Mg)) := by
          ring
      _ ≤ _ := add_le_add hA hB
  -- assembly
  have hρL : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact hM x)
  have hrL : MemLp (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ) 2 (withDensityReal ρ) :=
    (s71_resp_spec hq hβpos hρL).1.1
  have hEL : MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) / deltaN d s (n + 1) -
      biasDensity d s β ρ x) 2 (withDensityReal ρ) :=
    (s71_memLp_div hz2 _).sub (hrL.const_mul (2 * biasConst d s * β ^ biasP d s))
  have hP1m : MemLp (fun x => insertionDefect d s (n + 1) β (withDensityReal ρ) x / deltaN d s (n + 1) -
      2 * biasConst d s * β ^ biasP d s * ρ x) 2 (withDensityReal ρ) :=
    MemLp.of_bound ((hDm.div_const _).sub (hρ.measurable.const_mul _)).aestronglyMeasurable
      (βp ^ biasP d s * (|C0| + 2 * |biasConst d s| * max M 0) * Y)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hP1 x)
  have hP2m : MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1 -
      Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) / deltaN d s (n + 1)) 2 (withDensityReal ρ) :=
    s71_memLp_div hPa _
  have hP3m : MemLp (fun x => (1 / deltaN d s (n + 1)) *
      (β * (∫ y, rieszKernel d s (x - y) * w y) +
        (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))))
      2 (withDensityReal ρ) := (hPc.add hPd).const_mul _
  have hsplit : (fun x => ((wr13d_theta d s n β (withDensityReal ρ) x - 1 -
        Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) + insertionDefect d s (n + 1) β (withDensityReal ρ) x +
        β * (∫ y, rieszKernel d s (x - y) * w y) +
        (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) /
        deltaN d s (n + 1) - 2 * biasConst d s * β ^ biasP d s * ρ x) =
      fun x => ((insertionDefect d s (n + 1) β (withDensityReal ρ) x / deltaN d s (n + 1) -
        2 * biasConst d s * β ^ biasP d s * ρ x) +
        (wr13d_theta d s n β (withDensityReal ρ) x - 1 -
          Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) / deltaN d s (n + 1)) +
        (1 / deltaN d s (n + 1)) * (β * (∫ y, rieszKernel d s (x - y) * w y) +
          (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ))) := by
    funext x
    field_simp
    ring
  have hP1n : l2Norm (withDensityReal ρ) (fun x => insertionDefect d s (n + 1) β (withDensityReal ρ) x /
      deltaN d s (n + 1) - 2 * biasConst d s * β ^ biasP d s * ρ x) ≤
      βp ^ biasP d s * (|C0| + 2 * |biasConst d s| * max M 0) * Y :=
    s71_l2Norm_le_of_bound (by positivity) hP1
  refine ⟨hEL, ?_⟩
  rw [← hYdef]
  have hCY : C * Y = βp ^ biasP d s * (|C0| + 2 * |biasConst d s| * max M 0) * Y + 2 * CL * |Cc| * Y +
      (βp * |CBM| * (2 * K) ^ e₂ * Y + βp * Cν * Mg * Y) := by rw [hC]; ring
  have hT2 : 2 * CL * |Cc| * T ≤ 2 * CL * |Cc| * Y := mul_le_mul_of_nonneg_left hTY (by positivity)
  have htri := s71_l2Norm_add3_le hP1m hP2m hP3m
  have hred' : l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
      deltaN d s (n + 1) - biasDensity d s β ρ x) ≤ l2Norm (withDensityReal ρ) (fun x =>
      ((insertionDefect d s (n + 1) β (withDensityReal ρ) x / deltaN d s (n + 1) -
        2 * biasConst d s * β ^ biasP d s * ρ x) +
        (wr13d_theta d s n β (withDensityReal ρ) x - 1 -
          Real.log (wr13d_theta d s n β (withDensityReal ρ) x)) / deltaN d s (n + 1)) +
        (1 / deltaN d s (n + 1)) * (β * (∫ y, rieszKernel d s (x - y) * w y) +
          (β / ((n + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (n + 1) β (withDensityReal ρ)))) := by
    rw [← hsplit]; exact hred
  linarith [hred', htri, hP1n, hP2, hP3, hT2, hCY]


end HRS.Whole.S71
