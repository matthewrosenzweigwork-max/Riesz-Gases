import HRS.MS.CritWholeDefect
import HRS.MS.CritWholeCavityL2
import HRS.MS.CritWholeFullDensity
import HRS.MS.SharpBiasAux1
import HRS.MS.WrMargBAux2
import HRS.PDE.MeanFieldLinearResponse

/-!
# S8.1 XS (S81d), CR11: the relative response error `E_N = (I + βK_μ) z_N - P_μ D_N` is `O(√log N / N)` in `L²_0(μ)`

Route.  The exact cavity equation `wr13d_log_theta` and `θ μ = π`, `ν = q μ` (CR02) give the pointwise Euler equation
`z + β S = H + k`, `z = θ - 1`, `H = (θ - 1 - log θ) + D_N + β g*((θ-q) μ) + (β/N) g*ν`; `s71_euler_to_response` turns it into
`z + β K_μ z = P_μ H` a.e., so `E_N = P_μ H₁` with `H₁ = (θ - 1 - log θ) + β g*((θ-q)μ) + (β/N) g*ν`.
Bounds: `0 ≤ θ - 1 - log θ ≤ C (θ-1)²` (`θ ≥ C⁻¹`, CR10), the Schur test for `g*((θ-q)μ)` in `L²(μ)` and `g*ν ≤ C M_g`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-! ### Elementary `L²` facts -/

theorem s81d_l2_add {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ (fun x => f x + g x) ≤ l2Norm μ f + l2Norm μ g := by
  have hfg : MemLp (fun x => f x + g x) 2 μ := hf.add hg
  unfold l2Norm
  rw [wr13d_sqrt_eq hfg, wr13d_sqrt_eq hf, wr13d_sqrt_eq hg]
  have h : eLpNorm (fun x => f x + g x) 2 μ ≤ eLpNorm f 2 μ + eLpNorm g 2 μ :=
    eLpNorm_add_le one_le_two
  calc (eLpNorm (fun x => f x + g x) 2 μ).toReal ≤ (eLpNorm f 2 μ + eLpNorm g 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) h
    _ = _ := ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top

theorem s81d_l2_smul (μ : Measure (Euc d)) (c : ℝ) (f : Euc d → ℝ) :
    l2Norm μ (fun x => c * f x) = |c| * l2Norm μ f := by
  unfold l2Norm
  have : (fun x => (c * f x) ^ 2) = fun x => c ^ 2 * f x ^ 2 := by funext x; ring
  rw [this, integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem s81d_l2_le_bound {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x, |f x| ≤ B) (hm : Measurable f) : l2Norm μ f ≤ B := by
  unfold l2Norm
  refine Real.sqrt_le_iff.2 ⟨hB, ?_⟩
  calc ∫ x, f x ^ 2 ∂μ ≤ ∫ _x, B ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (integrable_const _)
          (Eventually.of_forall fun x => ?_)
        exact (sq_le_sq.2 (by rw [abs_of_nonneg hB]; exact hf x))
    _ = B ^ 2 := by simp

theorem s81d_l2_mono {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hg : MemLp g 2 μ) (hfm : AEStronglyMeasurable f μ)
    (h : ∀ x, |f x| ≤ |g x|) : l2Norm μ f ≤ l2Norm μ g := by
  unfold l2Norm
  refine Real.sqrt_le_sqrt ?_
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hg.integrable_sq
    (Eventually.of_forall fun x => sq_le_sq.2 (h x))

theorem s81d_log_quad {C θ : ℝ} (hC : 0 < C) (hθ : C⁻¹ ≤ θ) :
    0 ≤ θ - 1 - Real.log θ ∧ θ - 1 - Real.log θ ≤ C * (θ - 1) ^ 2 := by
  have hθ0 : 0 < θ := lt_of_lt_of_le (inv_pos.2 hC) hθ
  refine ⟨by linarith [Real.log_le_sub_one_of_pos hθ0], ?_⟩
  have h1 := Real.one_sub_inv_le_log_of_pos hθ0
  have h2 : θ⁻¹ ≤ C := by
    rw [inv_le_comm₀ hθ0 hC]; exact hθ
  have h3 : θ - 1 - Real.log θ ≤ (θ - 1) ^ 2 * θ⁻¹ := by
    have : (θ - 1) ^ 2 * θ⁻¹ = θ - 2 + θ⁻¹ := by field_simp; ring
    rw [this]; linarith
  exact h3.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _))

/-! ### Numerical facts -/

theorem s81d_num (hd : 1 ≤ d) : ∃ c1 c3 : ℝ, 0 ≤ c1 ∧ 0 ≤ c3 ∧ ∀ N : ℕ, 2 ≤ N →
    (N : ℝ)⁻¹ ≤ c1 * rate N ∧ deltaN d ((d : ℝ) / 2) N ≤ 1 ∧
      deltaN d ((d : ℝ) / 2) N * Real.sqrt (deltaN d ((d : ℝ) / 2) N) ≤ c3 * rate N := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hl2
  refine ⟨1 / Real.sqrt (Real.log 2), 2 * (1 + 1 / Real.log 2), by positivity, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLge : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  set L : ℝ := Real.log N with hL
  have hL0 : 0 < L := lt_of_lt_of_le hl2 hLge
  set s : ℝ := Real.sqrt L with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hL0
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have hsge : Real.sqrt (Real.log 2) ≤ s := Real.sqrt_le_sqrt hLge
  have hrate : rate N = s / N := rfl
  obtain ⟨hδ1, hδL⟩ := s81b_delta_facts hd hN
  obtain ⟨-, hδ1', -⟩ := s81c_num_facts hd hN
  have hδ := s81c_delta_eq hd hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) N with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  refine ⟨?_, hδ1', ?_⟩
  · rw [hrate]
    have : 1 ≤ s / Real.sqrt (Real.log 2) := by rw [le_div_iff₀ hr2]; linarith
    calc (N : ℝ)⁻¹ = (N : ℝ)⁻¹ * 1 := by ring
      _ ≤ (N : ℝ)⁻¹ * (s / Real.sqrt (Real.log 2)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / Real.sqrt (Real.log 2) * (s / N) := by field_simp
  · rw [hrate]
    have hsδ : Real.sqrt δ * s ≤ 2 := by
      rw [← Real.sqrt_mul hδ0]
      calc Real.sqrt (δ * L) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hδL
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hone : 1 ≤ L / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have key : (1 + L) * Real.sqrt δ ≤ 2 * (1 + 1 / Real.log 2) * s := by
      refine le_of_mul_le_mul_right ?_ hs0
      calc (1 + L) * Real.sqrt δ * s = (1 + L) * (Real.sqrt δ * s) := by ring
        _ ≤ (1 + L) * 2 := mul_le_mul_of_nonneg_left hsδ (by linarith)
        _ ≤ 2 * (1 + 1 / Real.log 2) * (s * s) := by
            rw [hss]
            have : 1 ≤ L * (1 / Real.log 2) := by rw [← div_eq_mul_one_div]; exact hone
            nlinarith
        _ = 2 * (1 + 1 / Real.log 2) * s * s := by ring
    calc δ * Real.sqrt δ = (N : ℝ)⁻¹ * ((1 + L) * Real.sqrt δ) := by rw [hδ]; ring
      _ ≤ (N : ℝ)⁻¹ * (2 * (1 + 1 / Real.log 2) * s) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = 2 * (1 + 1 / Real.log 2) * (s / N) := by field_simp

/-! ### The Schur test for `g * (w μ)` in `L²(μ)` -/

set_option maxHeartbeats 1600000 in
theorem s81d_schur (hd : 1 ≤ d) (D : Data d M βm βp) {w : Euc d → ℝ} (hwm : Measurable w)
    (hw : MemLp w 2 (mu D)) :
    MemLp (fun x => ∫ y, critG d (x - y) * w y ∂(mu D)) 2 (mu D) ∧
      l2Norm (mu D) (fun x => ∫ y, critG d (x - y) * w y ∂(mu D)) ≤
        max (potentialBound d ((d : ℝ) / 2) M) 0 * l2Norm (mu D) w := by
  have := s81c_prob D
  have hgm := s81b_critG_meas hd
  have hg0 : ∀ z, 0 ≤ critG d z := s81b_critG_nonneg hd
  set Mg : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hMg
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  have hconv : ∀ z, convMeasure (critG d) (mu D) z ≤ Mg := fun z => (s81c_conv_le hd D z).trans (le_max_left _ _)
  have hgi : ∀ x, Integrable (fun y => critG d (x - y)) (mu D) := fun x =>
    (wr13a_potential_bound hd (s81c_hs0 hd) (s81c_hsd hd) D.prob D.bound x).1
  have hgxm : ∀ x, Measurable fun y => critG d (x - y) := fun x => hgm.comp (measurable_const.sub measurable_id)
  have hgpm : Measurable fun p : Euc d × Euc d => critG d (p.1 - p.2) := hgm.comp (measurable_fst.sub measurable_snd)
  -- measurability of the two convolutions
  have hFm : ∀ v : Euc d → ℝ, Measurable v → Measurable fun x => ∫ y, critG d (x - y) * v y ∂(mu D) := by
    intro v hv
    have h : StronglyMeasurable (fun p : Euc d × Euc d => critG d (p.1 - p.2) * v p.2) :=
      (hgpm.mul (hv.comp measurable_snd)).stronglyMeasurable
    exact (h.integral_prod_right' (ν := mu D)).measurable
  set wa : Euc d → ℝ := fun y => |w y| with hwa
  have hwam : Measurable wa := hwm.abs
  -- Schur
  set wk : Euc d → Euc d → ℝ≥0∞ := fun x y => ENNReal.ofReal (critG d (x - y)) with hwk
  set u : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (wa y) with hu
  have hW1 : ∀ x, ∫⁻ y, wk x y ∂(mu D) ≤ ENNReal.ofReal Mg := by
    intro x
    simp only [hwk]
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi x) (Eventually.of_forall fun y => hg0 _)]
    exact ENNReal.ofReal_le_ofReal (hconv x)
  have hW2 : ∀ y, ∫⁻ x, wk x y ∂(mu D) ≤ ENNReal.ofReal Mg := by
    intro y
    simp only [hwk]
    have : ∀ x, critG d (x - y) = critG d (y - x) := fun x => by
      rw [← neg_sub]; exact rieszKernel_neg _
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi y) (Eventually.of_forall fun y => hg0 _)]
    exact ENNReal.ofReal_le_ofReal (hconv y)
  have hwkm : Measurable fun p : Euc d × Euc d => wk p.1 p.2 := hgpm.ennreal_ofReal
  have hsch := HRS.PDE.MFLinear.schur_sq (μ := mu D) wk (ENNReal.ofReal Mg) ENNReal.ofReal_ne_top hW1 hW2
    (fun x => (hwkm.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    (fun y => (hwkm.comp (measurable_id.prodMk measurable_const)).aemeasurable) hwkm.aemeasurable u
    hwam.ennreal_ofReal.aemeasurable
  set F : Euc d → ℝ := fun x => ∫ y, critG d (x - y) * w y ∂(mu D) with hF
  have hFmeas : Measurable F := hFm w hwm
  have hw2i : Integrable (fun y => w y ^ 2) (mu D) := hw.integrable_sq
  have hw2nn : 0 ≤ ∫ y, w y ^ 2 ∂(mu D) := integral_nonneg fun y => sq_nonneg _
  have hptw : ∀ x, ENNReal.ofReal (F x ^ 2) ≤ (∫⁻ y, wk x y * u y ∂(mu D)) ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal (F x ^ 2) = ‖F x‖ₑ ^ 2 := by
      rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    rw [h1]
    refine pow_le_pow_left' ?_ 2
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    simp only [hwk, hu, hwa, enorm_mul, Real.enorm_of_nonneg (hg0 _), Real.enorm_eq_ofReal_abs]
  have hlint : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂(mu D) ≤ ENNReal.ofReal (Mg ^ 2 * ∫ y, w y ^ 2 ∂(mu D)) := by
    refine (lintegral_mono hptw).trans (hsch.trans (le_of_eq ?_))
    have h2 : ∀ y, u y ^ 2 = ENNReal.ofReal (w y ^ 2) := fun y => by
      simp only [hu, hwa]
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    simp_rw [h2]
    rw [← ofReal_integral_eq_lintegral_ofReal hw2i (Eventually.of_forall fun y => sq_nonneg _),
      ← ENNReal.ofReal_pow hMg0, ← ENNReal.ofReal_mul (sq_nonneg _)]
  obtain ⟨hFi, hFle⟩ := Q34.integrable_of_lintegral_le (hFmeas.pow_const 2) (fun z => sq_nonneg _)
    (mul_nonneg (sq_nonneg _) hw2nn) hlint
  refine ⟨(memLp_two_iff_integrable_sq hFmeas.aestronglyMeasurable).2 hFi, ?_⟩
  unfold l2Norm
  calc Real.sqrt (∫ x, F x ^ 2 ∂(mu D)) ≤ Real.sqrt (Mg ^ 2 * ∫ y, w y ^ 2 ∂(mu D)) := Real.sqrt_le_sqrt hFle
    _ = Mg * Real.sqrt (∫ y, w y ^ 2 ∂(mu D)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hMg0]

/-! ### The exact cavity equation for `N ≥ 2` -/

theorem s81d_log_theta (hd : 2 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) (N : ℕ) (hN : 2 ≤ N) (y : Euc d) :
    Real.log (theta D N y) = D.beta * convMeasure (critG d) (mu D) y +
      (defect D N y + -(D.beta / (N : ℝ)) * ((N - 1 : ℕ) : ℝ) *
        ∫ z, critG d (y - z) ∂(firstMarginal (cavity D N))) -
      Real.log (wr13d_Z d ((d : ℝ) / 2) (N - 1) D.beta (mu D)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact wr13d_log_theta hd (s81c_hs0 hd1) (s81c_hsd hd1) D.prob D.bound hβ0.le (n := m + 1) (by omega) y

set_option maxHeartbeats 6400000 in
/-- **CR11** `relative_response_error` (statement = Pro skeleton, copied). -/
theorem s81d_relative_response_error (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      MemL2Zero (mu D) (responseError D N) ∧
      l2Norm (mu D) (responseError D N) ≤ C * rate N := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := s81c_hs0 hd1
  have hsd := s81c_hsd hd1
  obtain ⟨Cθ, hCθ1, hCθ⟩ := s81b_full_density_sup hd M βm βp hβm hβ
  obtain ⟨Cq, hCq1, hCq⟩ := s81b_cavity_relative_L2 hd M βm βp hβm hβ
  obtain ⟨Cd, hCd0, hCd⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  obtain ⟨c1, c3, hc10, hc30, hnum⟩ := s81d_num (d := d) hd1
  set Mg : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hMgdef
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  have hCθ0 : 0 < Cθ := by linarith
  have hCq0 : 0 ≤ Cq := by linarith
  have hβp : 0 < βp := hβm.trans_le hβ
  refine ⟨Cθ ^ 2 * Cq * (1 + c3) + βp * Mg * Cq + βp * Cq * Mg * c1, by positivity, fun D N hN => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have := s81c_prob D
  have hq : Q34.Q34Hyp d ((d : ℝ) / 2) D.rho M := ⟨hd1, hs0, hsd, D.prob, D.bound⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hc1N, hδ1, hc3N⟩ := hnum N hN
  obtain ⟨hδinv, -, -, -, -⟩ := s81c_num_facts hd1 hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) N with hδdef
  have hδ0 : 0 ≤ δ := (inv_nonneg.2 hN0.le).trans hδinv
  have hsδ1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.2 hδ1
  have hrate0 : 0 ≤ rate N := div_nonneg (Real.sqrt_nonneg _) hN0.le
  obtain ⟨q, hqm, hνq, hq0, hqL, hql, hwL, hwl, -⟩ := hCq D N hN
  have hθlow : ∀ x, Cθ⁻¹ ≤ theta D N x := fun x => (hCθ D N hN x).1
  have hθdev : ∀ x, |theta D N x - 1| ≤ Cθ * Real.sqrt δ := fun x => (hCθ D N hN x).2
  have hθ0 : ∀ x, 0 < theta D N x := fun x => lt_of_lt_of_le (inv_pos.2 hCθ0) (hθlow x)
  have hθle : ∀ x, theta D N x ≤ 1 + Cθ := fun x => by
    have := (abs_le.1 (hθdev x)).2
    nlinarith [mul_le_mul_of_nonneg_left hsδ1 hCθ0.le]
  have hθm : Measurable (theta D N) := wr13d_theta_meas hd hs0 hsd D.prob D.bound hβ0.le (N - 1)
  have hθint : Integrable (theta D N) (mu D) :=
    Integrable.of_bound hθm.aestronglyMeasurable (1 + Cθ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 x)]; exact hθle x)
  have hθ1 : ∫ x, theta D N x ∂(mu D) = 1 :=
    wr13d_theta_integral hd hs0 hsd D.prob D.bound hβ0.le (n := N - 1) (by omega)
  have hzbd : ∀ x, |theta D N x - 1| ≤ Cθ := fun x => (hθdev x).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hsδ1 hCθ0.le])
  have hzm : Measurable fun x => theta D N x - 1 := hθm.sub_const 1
  have hzL : MemLp (fun x => theta D N x - 1) 2 (mu D) :=
    MemLp.of_bound hzm.aestronglyMeasurable Cθ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hzbd x)
  have hz0 : MemL2Zero (mu D) (fun x => theta D N x - 1) := by
    refine ⟨hzL, ?_⟩
    rw [integral_sub hθint (integrable_const _), hθ1]; simp
  -- the pieces
  set w : Euc d → ℝ := fun y => theta D N y - q y with hwdef
  have hwm : Measurable w := hθm.sub hqm
  have hgm := s81b_critG_meas hd1
  have hg0 : ∀ z, 0 ≤ critG d z := s81b_critG_nonneg hd1
  have hgi : ∀ x, Integrable (fun y => critG d (x - y)) (mu D) := fun x =>
    (wr13a_potential_bound hd1 hs0 hsd D.prob D.bound x).1
  have hgxm : ∀ x, Measurable fun y => critG d (x - y) := fun x => hgm.comp (measurable_const.sub measurable_id)
  have hgpm : Measurable fun p : Euc d × Euc d => critG d (p.1 - p.2) := hgm.comp (measurable_fst.sub measurable_snd)
  have hFm : ∀ v : Euc d → ℝ, Measurable v → Measurable fun x => ∫ y, critG d (x - y) * v y ∂(mu D) := by
    intro v hv
    have h : StronglyMeasurable (fun p : Euc d × Euc d => critG d (p.1 - p.2) * v p.2) :=
      (hgpm.mul (hv.comp measurable_snd)).stronglyMeasurable
    exact (h.integral_prod_right' (ν := mu D)).measurable
  set F : Euc d → ℝ := fun x => ∫ y, critG d (x - y) * w y ∂(mu D) with hF
  set A : Euc d → ℝ := fun x => ∫ y, critG d (x - y) * q y ∂(mu D) with hA
  have hFmeas : Measurable F := hFm w hwm
  have hAmeas : Measurable A := hFm q hqm
  obtain ⟨hFL, hFn⟩ := s81d_schur hd1 D hwm hwL
  have hA0 : ∀ x, 0 ≤ A x := fun x => integral_nonneg fun y => mul_nonneg (hg0 _) (hq0 y).1
  have hCq' : ∀ y, q y ≤ Cq := fun y => (hq0 y).2
  have hAle : ∀ x, A x ≤ Cq * Mg := by
    intro x
    have hqg : Integrable (fun y => critG d (x - y) * q y) (mu D) :=
      (hgi x).mul_bdd hqm.aestronglyMeasurable (c := Cq) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hq0 y).1]; exact hCq' y)
    calc A x ≤ ∫ y, Cq * critG d (x - y) ∂(mu D) := by
          refine integral_mono hqg ((hgi x).const_mul Cq) fun y => ?_
          nlinarith [hg0 (x - y), (hq0 y).2, (hq0 y).1, mul_le_mul_of_nonneg_left (hq0 y).2 (hg0 (x - y))]
      _ = Cq * convMeasure (critG d) (mu D) x := integral_const_mul _ _
      _ ≤ Cq * Mg := mul_le_mul_of_nonneg_left ((s81c_conv_le hd1 D x).trans (le_max_left _ _)) hCq0
  -- the cavity marginal against the kernel
  have hAν : ∀ x, ∫ z, critG d (x - z) ∂(firstMarginal (cavity D N)) = A x := by
    intro x
    rw [hνq, s81b_integral_withDensity hqm (fun y => (hq0 y).1)]
    simp only [hA]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only; ring
  -- Euler equation
  have hqgi : ∀ x, Integrable (fun y => critG d (x - y) * q y) (mu D) := fun x =>
    (hgi x).mul_bdd hqm.aestronglyMeasurable (c := Cq) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 y).1]; exact hCq' y)
  have hθgi : ∀ x, Integrable (fun y => critG d (x - y) * theta D N y) (mu D) := fun x =>
    (hgi x).mul_bdd hθm.aestronglyMeasurable (c := 1 + Cθ) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθle y)
  have hSdec : ∀ x, ∫ y, critG d (x - y) * (theta D N y - 1) ∂(mu D) =
      F x + A x - convMeasure (critG d) (mu D) x := by
    intro x
    have e1 : ∫ y, critG d (x - y) * (theta D N y - 1) ∂(mu D) =
        (∫ y, critG d (x - y) * theta D N y ∂(mu D)) - ∫ y, critG d (x - y) ∂(mu D) := by
      rw [← integral_sub (hθgi x) (hgi x)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only; ring
    have e2 : F x = (∫ y, critG d (x - y) * theta D N y ∂(mu D)) - A x := by
      simp only [hF, hA, hwdef]
      rw [← integral_sub (hθgi x) (hqgi x)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [e1, e2]; unfold convMeasure; ring
  have hnR : ((N - 1 : ℕ) : ℝ) + 1 = N := by
    rw [← Nat.cast_succ]; congr 1; omega
  have hlam : D.beta / (N : ℝ) * ((N - 1 : ℕ) : ℝ) + D.beta / (N : ℝ) = D.beta := by
    have : D.beta / (N : ℝ) * (((N - 1 : ℕ) : ℝ) + 1) = D.beta := by rw [hnR]; field_simp
    linarith
  set Z : ℝ := wr13d_Z d ((d : ℝ) / 2) (N - 1) D.beta (mu D) with hZ
  set a : Euc d → ℝ := fun x => theta D N x - 1 - Real.log (theta D N x) with ha
  set lam : ℝ := D.beta / (N : ℝ) with hlamdef
  set Hf : Euc d → ℝ := fun x => a x + defect D N x + D.beta * F x + lam * A x with hHf
  have heq : ∀ x, (theta D N x - 1) + D.beta * (∫ y, critG d (x - y) * (theta D N y - 1) ∂(mu D)) =
      Hf x + (-Real.log Z) := by
    intro x
    have hlogθ := s81d_log_theta hd D hβ0 N hN x
    rw [hAν x] at hlogθ
    rw [hSdec x]
    simp only [hHf, ha]
    linear_combination hlogθ - A x * hlam
  -- membership
  have hDm : Measurable (defect D N) := s81d_defect_meas hd D hβ0 N hN
  have hDb : ∀ x, |defect D N x| ≤ Cd * deltaN d ((d : ℝ) / 2) N := fun x => by
    obtain ⟨-, h1, h2, -⟩ := hCd D.rho D.prob D.bound D.beta D.beta_mem.1 hββp N hN x
    have e : defect D N x = insertionDefect d ((d : ℝ) / 2) N D.beta (withDensityReal D.rho) x := rfl
    rw [e, abs_of_nonneg h1]; exact h2
  have hDL : MemLp (defect D N) 2 (mu D) :=
    MemLp.of_bound hDm.aestronglyMeasurable (Cd * δ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hDb x)
  have ham : Measurable a := (hθm.sub_const 1).sub (Real.measurable_log.comp hθm)
  have hab : ∀ x, |a x| ≤ Cθ * (Cθ * Real.sqrt δ) * |theta D N x - 1| := by
    intro x
    obtain ⟨h0, h1⟩ := s81d_log_quad hCθ0 (hθlow x)
    rw [abs_of_nonneg h0]
    calc a x ≤ Cθ * (theta D N x - 1) ^ 2 := h1
      _ = Cθ * (|theta D N x - 1| * |theta D N x - 1|) := by rw [← sq, sq_abs]
      _ ≤ Cθ * ((Cθ * Real.sqrt δ) * |theta D N x - 1|) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hθdev x) (abs_nonneg _)) hCθ0.le
      _ = _ := by ring
  have haL : MemLp a 2 (mu D) :=
    MemLp.of_bound ham.aestronglyMeasurable (Cθ * (Cθ * Real.sqrt δ) * Cθ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (hab x).trans (mul_le_mul_of_nonneg_left (hzbd x) (by positivity)))
  have hAL : MemLp A 2 (mu D) :=
    MemLp.of_bound hAmeas.aestronglyMeasurable (Cq * Mg) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hA0 x)]; exact hAle x)
  have hlam0 : 0 ≤ lam := by positivity
  have hH1L : MemLp (fun x => a x + D.beta * F x + lam * A x) 2 (mu D) :=
    (haL.add (hFL.const_mul D.beta)).add (hAL.const_mul lam)
  have hHfL : MemLp Hf 2 (mu D) := by
    have := ((haL.add hDL).add (hFL.const_mul D.beta)).add (hAL.const_mul lam)
    exact this
  -- the response equation
  have hresp := HRS.Whole.S71.s71_euler_to_response hq hβ0 hz0 (hHfL.integrable one_le_two) (-Real.log Z) heq
  have hE : responseError D N =ᵐ[mu D] projMean (mu D) (fun x => a x + D.beta * F x + lam * A x) := by
    filter_upwards [hresp] with x hx
    have hiH := hHfL.integrable one_le_two
    have hiD := hDL.integrable one_le_two
    have hH1 : (fun x => a x + D.beta * F x + lam * A x) = fun x => Hf x - defect D N x := by
      funext x; simp only [hHf]; ring
    have hpair : pair (mu D) (fun x => a x + D.beta * F x + lam * A x) = pair (mu D) Hf - pair (mu D) (defect D N) := by
      simp only [pair]
      rw [hH1]; exact integral_sub hiH hiD
    have e : responseError D N x = (theta D N x - 1) + D.beta * Kop (critG d) (mu D) (fun y => theta D N y - 1) x -
        projMean (mu D) (defect D N) x := rfl
    rw [e, hx]
    simp only [projMean, hpair, hHf]
    ring
  -- conclusion
  have hH1m := HRS.Whole.S71.s71_memL2Zero_projMean hH1L
  refine ⟨⟨hH1m.1.ae_eq hE.symm, by rw [integral_congr_ae hE]; exact hH1m.2⟩, ?_⟩
  have hn1 : l2Norm (mu D) (responseError D N) = l2Norm (mu D) (projMean (mu D) (fun x => a x + D.beta * F x + lam * A x)) := by
    unfold l2Norm
    congr 1
    refine integral_congr_ae (hE.mono fun x hx => ?_)
    simp only [hx]
  rw [hn1]
  refine (HRS.Whole.S71.s71_l2Norm_projMean_le hH1L).trans ?_
  -- triangle inequality
  have hFL' : MemLp (fun x => D.beta * F x) 2 (mu D) := hFL.const_mul D.beta
  have hAL' : MemLp (fun x => lam * A x) 2 (mu D) := hAL.const_mul lam
  have hAF : MemLp (fun x => a x + D.beta * F x) 2 (mu D) := haL.add hFL'
  have t1 := s81d_l2_add hAF hAL'
  have t2 := s81d_l2_add haL hFL'
  rw [s81d_l2_smul, abs_of_pos hβ0] at t2
  have t3 : l2Norm (mu D) (fun x => lam * A x) ≤ lam * (Cq * Mg) := by
    rw [s81d_l2_smul, abs_of_nonneg hlam0]
    exact mul_le_mul_of_nonneg_left (s81d_l2_le_bound (by positivity) (fun x => by
      rw [abs_of_nonneg (hA0 x)]; exact hAle x) hAmeas) hlam0
  -- bounds on the pieces
  have hwn : l2Norm (mu D) w ≤ Cq * rate N := hwl
  have hqn : l2Norm (mu D) (fun y => q y - 1) ≤ Cq * δ := hql
  have hzn : l2Norm (mu D) (fun x => theta D N x - 1) ≤ Cq * rate N + Cq * δ := by
    have e : (fun x => theta D N x - 1) = fun x => w x + (q x - 1) := by funext x; simp only [hwdef]; ring
    rw [e]
    exact (s81d_l2_add hwL hqL).trans (add_le_add hwn hqn)
  set Ka : ℝ := Cθ * (Cθ * Real.sqrt δ) with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  have hzL' : MemLp (fun x => Ka * (theta D N x - 1)) 2 (mu D) := hzL.const_mul Ka
  have hanorm : l2Norm (mu D) a ≤ Ka * (Cq * rate N + Cq * δ) := by
    have h1 : l2Norm (mu D) a ≤ l2Norm (mu D) (fun x => Ka * (theta D N x - 1)) :=
      s81d_l2_mono hzL' ham.aestronglyMeasurable (fun x => by
        rw [abs_mul, abs_of_nonneg hKa0]; exact hab x)
    rw [s81d_l2_smul, abs_of_nonneg hKa0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hzn hKa0)
  have hFnorm : l2Norm (mu D) F ≤ Mg * (Cq * rate N) := hFn.trans (mul_le_mul_of_nonneg_left hwn hMg0)
  have hsum : l2Norm (mu D) (fun x => a x + D.beta * F x + lam * A x) ≤
      Ka * (Cq * rate N + Cq * δ) + D.beta * (Mg * (Cq * rate N)) + lam * (Cq * Mg) := by
    calc _ ≤ l2Norm (mu D) (fun x => a x + D.beta * F x) + l2Norm (mu D) (fun x => lam * A x) := t1
      _ ≤ (l2Norm (mu D) a + D.beta * l2Norm (mu D) F) + lam * (Cq * Mg) := add_le_add t2 t3
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hFnorm hβ0.le
          linarith
  refine hsum.trans ?_
  have hA1 : Ka * (Cq * rate N + Cq * δ) ≤ Cθ ^ 2 * Cq * (1 + c3) * rate N := by
    have e : Ka * (Cq * rate N + Cq * δ) = Cθ ^ 2 * Cq * (Real.sqrt δ * rate N + δ * Real.sqrt δ) := by
      simp only [hKa]; ring
    rw [e]
    have h1 : Real.sqrt δ * rate N ≤ rate N := mul_le_of_le_one_left hrate0 hsδ1
    have h2 : Real.sqrt δ * rate N + δ * Real.sqrt δ ≤ (1 + c3) * rate N := by linarith
    calc _ ≤ Cθ ^ 2 * Cq * ((1 + c3) * rate N) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hA2 : D.beta * (Mg * (Cq * rate N)) ≤ βp * Mg * Cq * rate N := by
    have : D.beta * (Mg * (Cq * rate N)) ≤ βp * (Mg * (Cq * rate N)) :=
      mul_le_mul_of_nonneg_right hββp (by positivity)
    linarith
  have hA3 : lam * (Cq * Mg) ≤ βp * Cq * Mg * c1 * rate N := by
    have hl : lam ≤ βp * (c1 * rate N) := by
      have : lam = D.beta * (N : ℝ)⁻¹ := by simp only [hlamdef]; ring
      rw [this]
      exact mul_le_mul hββp hc1N (by positivity) hβp.le
    calc lam * (Cq * Mg) ≤ βp * (c1 * rate N) * (Cq * Mg) := mul_le_mul_of_nonneg_right hl (by positivity)
      _ = _ := by ring
  linarith

end HRS.Whole.S81b
