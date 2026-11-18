import HRS.MS.ThCorrRespAux3
import HRS.MS.ThCorrFarAux2
import HRS.MS.ThCorrSob
import HRS.MS.ThCorrSAux2
import HRS.MS.ThCorrSAux3

/-!
# TC-5, part 1: Sobolev / `C_b^m` utilities, estimates for the reference density `ρ`, the splitting of `K`

Namespace `HRS.MS.Tc5`.  Helper lemmas are prefixed `tc5_`.

* `tc5_cutoff`: a cutoff `θ` with `TcCutoff θ` exists.
* Sobolev utilities: `tc5_sob_l2` (`‖u‖_{L²}² ≤ ‖u‖²_{H^τ}`, `τ ≥ 0`), `tc5_sob_mono`, `tc5_sob_congr`, `tc5_sob_add`,
  `tc5_sob_smul`; `C_b^m` utilities `tc5_cb_add`, `tc5_cb_const`, `tc5_cb_sup_le`.
* `tc5_rho_sob`: for `TcRef d ρ M₀ c S J` (`c > 0`): `ρ ∈ H^J` with `‖ρ‖²_{H^J} ≤ B S²`, `B = B(d, J, c)`.
* `tc5_rho_W`: `∑_{j ≤ N} ∫‖D^jρ‖ ≤ W S`, `W = W(d, N, c)`, and `D^jρ` integrable.
* `tc5_Kt_ae`: for `f ∈ L²(μ)` and a.e. `x`: `∫ g(x-y) f(y) dμ(y) = locK f x + farK f x`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.Tc5

open HRS.Whole HRS.MS.TcDefs HRS.MS.TcF
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

local notation "MemSob" => HRS.PDE.ToolboxRd.MemSobolev
local notation "SobSq" => HRS.PDE.ToolboxRd.sobolevNormSq

variable {d : ℕ}

/-! ### A cutoff -/

theorem tc5_cutoff : ∃ θ : Euc d → ℝ, TcCutoff θ := by
  let b : ContDiffBump (0 : Euc d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b, ⟨b.contDiff, fun z hz => ?_, fun z hz => ?_⟩⟩
  · exact b.zero_of_le_dist (by simpa [dist_zero_right] using hz)
  · exact b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]; show ‖z‖ ≤ (1 / 2 : ℝ); exact hz)

/-! ### Sobolev utilities -/

theorem tc5_sob_l2 {τ : ℝ} (hτ : 0 ≤ τ) {u : Euc d → ℝ} (hu : MemSob τ u) :
    ∫ x, u x ^ 2 ≤ SobSq τ u := by
  rw [integral_sq_eq_norm_sq hu.1, sobolevNormSq_eq]
  refine integral_mono (integrable_norm_sq_fourierL2 hu.1) hu.2 fun ξ => ?_
  have h1 : 1 ≤ wt ξ ^ τ := Real.one_le_rpow (one_le_wt ξ) hτ
  show ‖fourierL2 u ξ‖ ^ 2 ≤ wt ξ ^ τ * ‖fourierL2 u ξ‖ ^ 2
  nlinarith [sq_nonneg ‖fourierL2 u ξ‖]

theorem tc5_sob_nonneg (τ : ℝ) (u : Euc d → ℝ) : 0 ≤ SobSq τ u := by
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  exact integral_nonneg fun ξ => by
    have := wt_pos (d := d) ξ
    unfold wt at this
    positivity

theorem tc5_sob_mono {τ τ' : ℝ} (h : τ' ≤ τ) {u : Euc d → ℝ} (hu : MemSob τ u) :
    MemSob τ' u ∧ SobSq τ' u ≤ SobSq τ u := by
  have hm := memSobolev_mono h hu
  refine ⟨hm, ?_⟩
  rw [sobolevNormSq_eq, sobolevNormSq_eq]
  refine integral_mono hm.2 hu.2 fun ξ => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) h) (by positivity)

theorem tc5_sob_congr {τ : ℝ} {u v : Euc d → ℝ} (h : u =ᵐ[volume] v) (hu : MemSob τ u) :
    MemSob τ v ∧ SobSq τ v = SobSq τ u := by
  have hf := fourierL2_congr_ae h
  refine ⟨⟨hu.1.ae_eq h, ?_⟩, ?_⟩
  · rw [← hf]; exact hu.2
  · unfold HRS.PDE.ToolboxRd.sobolevNormSq; rw [hf]

theorem tc5_sob_add {τ : ℝ} {u v : Euc d → ℝ} (hu : MemSob τ u) (hv : MemSob τ v) :
    MemSob τ (fun x => u x + v x) ∧
      SobSq τ (fun x => u x + v x) ≤ 2 * SobSq τ u + 2 * SobSq τ v := by
  have hw : MemLp (fun x => u x + v x) 2 volume := hu.1.add hv.1
  have hadd := fourierL2_add hu.1 hv.1
  have hpt : ∀ ξ : Euc d, wt ξ ^ τ * ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 ≤
      2 * (wt ξ ^ τ * ‖fourierL2 u ξ‖ ^ 2) + 2 * (wt ξ ^ τ * ‖fourierL2 v ξ‖ ^ 2) := by
    intro ξ
    have hw0 : 0 ≤ wt ξ ^ τ := (Real.rpow_pos_of_pos (wt_pos ξ) τ).le
    have h1 : ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 ≤ 2 * ‖fourierL2 u ξ‖ ^ 2 + 2 * ‖fourierL2 v ξ‖ ^ 2 := by
      have := norm_add_le (fourierL2 u ξ) (fourierL2 v ξ)
      have h2 : ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 ≤ (‖fourierL2 u ξ‖ + ‖fourierL2 v ξ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖)]
    calc wt ξ ^ τ * ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2
        ≤ wt ξ ^ τ * (2 * ‖fourierL2 u ξ‖ ^ 2 + 2 * ‖fourierL2 v ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = _ := by ring
  have hint : Integrable (fun ξ => wt ξ ^ τ * ‖fourierL2 (fun x => u x + v x) ξ‖ ^ 2) volume := by
    refine Integrable.mono' ((hu.2.const_mul 2).add (hv.2.const_mul 2))
      (aesm_wt_mul (aestronglyMeasurable_fourierL2 hw) τ) ?_
    filter_upwards [hadd] with ξ h
    rw [h]
    have h0 : 0 ≤ wt ξ ^ τ * ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ; positivity
    rw [Real.norm_of_nonneg h0]
    exact hpt ξ
  refine ⟨⟨hw, hint⟩, ?_⟩
  have hu2 : Integrable (fun ξ : Euc d => 2 * (wt ξ ^ τ * ‖fourierL2 u ξ‖ ^ 2)) volume := hu.2.const_mul 2
  have hv2 : Integrable (fun ξ : Euc d => 2 * (wt ξ ^ τ * ‖fourierL2 v ξ‖ ^ 2)) volume := hv.2.const_mul 2
  rw [sobolevNormSq_eq, sobolevNormSq_eq, sobolevNormSq_eq, ← integral_const_mul, ← integral_const_mul,
    ← integral_add hu2 hv2]
  refine integral_mono_ae hint (hu2.add hv2) ?_
  filter_upwards [hadd] with ξ h
  rw [h]
  exact hpt ξ

theorem tc5_sob_smul {τ : ℝ} (a : ℝ) {u : Euc d → ℝ} (hu : MemSob τ u) :
    MemSob τ (fun x => a * u x) ∧ SobSq τ (fun x => a * u x) = a ^ 2 * SobSq τ u := by
  have hw : MemLp (fun x => a * u x) 2 volume := hu.1.const_mul a
  have hs := fourierL2_smul hu.1 a
  have hpt : ∀ᵐ ξ ∂(volume : Measure (Euc d)), wt ξ ^ τ * ‖fourierL2 (fun x => a * u x) ξ‖ ^ 2 =
      a ^ 2 * (wt ξ ^ τ * ‖fourierL2 u ξ‖ ^ 2) := by
    filter_upwards [hs] with ξ h
    rw [h, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  refine ⟨⟨hw, ?_⟩, ?_⟩
  · exact (integrable_congr hpt).2 (hu.2.const_mul _)
  · rw [sobolevNormSq_eq, sobolevNormSq_eq, ← integral_const_mul]
    exact integral_congr_ae hpt

/-! ### `C_b^m` utilities -/

theorem tc5_cb_nonneg (m : ℕ) (u : Euc d → ℝ) : 0 ≤ HRS.cbNorm m u :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem tc5_cb_sup_le {m : ℕ} {u : Euc d → ℝ} (hu : HRS.MemCb m u) (x : Euc d) :
    ‖u x‖ ≤ HRS.cbNorm m u := by
  unfold HRS.cbNorm
  have h0 : ‖u x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 u z‖ := by
    have := le_ciSup (hu.2 0 (Nat.zero_le _)) x
    simpa [norm_iteratedFDeriv_zero] using this
  refine h0.trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j u z‖)
    (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos m))

theorem tc5_cb_add {m : ℕ} {u v : Euc d → ℝ} (hu : HRS.MemCb m u) (hv : HRS.MemCb m v) :
    HRS.MemCb m (fun x => u x + v x) ∧
      HRS.cbNorm m (fun x => u x + v x) ≤ HRS.cbNorm m u + HRS.cbNorm m v := by
  set a : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j u z‖ with ha
  set b : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j v z‖ with hb
  have hale : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j u z‖ ≤ a j := fun j hj z => le_ciSup (hu.2 j hj) z
  have hble : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j v z‖ ≤ b j := fun j hj z => le_ciSup (hv.2 j hj) z
  have key : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j (fun x => u x + v x) z‖ ≤ a j + b j := by
    intro j hj z
    have hu' : ContDiff ℝ j u := hu.1.of_le (by exact_mod_cast hj)
    have hv' : ContDiff ℝ j v := hv.1.of_le (by exact_mod_cast hj)
    have := iteratedFDeriv_add_apply (i := j) hu'.contDiffAt hv'.contDiffAt (x := z)
    have e : iteratedFDeriv ℝ j (fun x => u x + v x) z = iteratedFDeriv ℝ j u z + iteratedFDeriv ℝ j v z :=
      this
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hale j hj z) (hble j hj z))
  refine ⟨⟨hu.1.add hv.1, fun j hj => ⟨a j + b j, ?_⟩⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact key j hj z
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (m + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => u x + v x) z‖
        ≤ ∑ j ∈ Finset.range (m + 1), (a j + b j) :=
          Finset.sum_le_sum fun j hj => ciSup_le fun z => key j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) z
      _ = _ := Finset.sum_add_distrib

theorem tc5_cb_const (m : ℕ) (c : ℝ) :
    HRS.MemCb m (fun _ : Euc d => c) ∧ HRS.cbNorm m (fun _ : Euc d => c) ≤ |c| := by
  have key : ∀ j ≤ m, ∀ z : Euc d, ‖iteratedFDeriv ℝ j (fun _ : Euc d => c) z‖ ≤ if j = 0 then |c| else 0 := by
    intro j hj z
    by_cases h0 : j = 0
    · subst h0; simp [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne h0]; simp [h0]
  refine ⟨⟨contDiff_const, fun j hj => ⟨if j = 0 then |c| else 0, ?_⟩⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact key j hj z
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (m + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun _ : Euc d => c) z‖
        ≤ ∑ j ∈ Finset.range (m + 1), (if j = 0 then |c| else 0) :=
          Finset.sum_le_sum fun j hj => ciSup_le fun z => key j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) z
      _ = |c| := by simp

/-! ### Estimates for the reference density -/

/-- `k! e^{1 + 1/(4c)}`: `sup_r (1+r)^k e^{-c r²} ≤ tc5_Kp c k`. -/
def tc5_Kp (c : ℝ) (k : ℕ) : ℝ := (k.factorial : ℝ) * Real.exp (1 + 1 / (4 * c))

theorem tc5_Kp_nonneg (c : ℝ) (k : ℕ) : 0 ≤ tc5_Kp c k := by unfold tc5_Kp; positivity

theorem tc5_poly {c : ℝ} (hc : 0 < c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ k * Real.exp (-c * r ^ 2) ≤ tc5_Kp c k := by
  have h1 : (1 + r) ^ k ≤ k.factorial * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + r) (by linarith) k
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : 1 + r + -c * r ^ 2 ≤ 1 + 1 / (4 * c) := by
    have : r - c * r ^ 2 ≤ 1 / (4 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * c * r - 1)]
    linarith
  calc (1 + r) ^ k * Real.exp (-c * r ^ 2)
      ≤ (k.factorial * Real.exp (1 + r)) * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = k.factorial * Real.exp (1 + r + -c * r ^ 2) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ tc5_Kp c k := by
        unfold tc5_Kp
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)

theorem tc5_S_nonneg {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) : 0 ≤ S := by
  have := hρ.deriv 0 (Nat.zero_le _) 0
  simp only [norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, neg_zero,
    Real.exp_zero, mul_one, pow_zero] at this
  exact (norm_nonneg _).trans this

theorem tc5_rho_dbound {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {j : ℕ} (hj : j ≤ N) (x : Euc d) :
    ‖iteratedFDeriv ℝ j ρ x‖ ≤ S * tc5_Kp (c / 2) j * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  have hS := tc5_S_nonneg hρ
  have h1 := tc5_poly (half_pos hc) j (norm_nonneg x)
  have e : Real.exp (-c * ‖x‖ ^ 2) = Real.exp (-(c / 2) * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖iteratedFDeriv ℝ j ρ x‖ ≤ S * (1 + ‖x‖) ^ j * Real.exp (-c * ‖x‖ ^ 2) := hρ.deriv j hj x
    _ = S * ((1 + ‖x‖) ^ j * Real.exp (-(c / 2) * ‖x‖ ^ 2)) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
        rw [e]; ring
    _ ≤ S * tc5_Kp (c / 2) j * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
        gcongr

theorem tc5_cont_D {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (j : ℕ) :
    Continuous fun x => iteratedFDeriv ℝ j ρ x :=
  (hρ.smooth.of_le (by exact_mod_cast le_top) : ContDiff ℝ j ρ).continuous_iteratedFDeriv le_rfl

/-- `G(c) = ∫ e^{-(c/2)|x|²}`. -/
def tc5_G (d : ℕ) (c : ℝ) : ℝ := ∫ x : Euc d, Real.exp (-(c / 2) * ‖x‖ ^ 2)

theorem tc5_G_nonneg (d : ℕ) (c : ℝ) : 0 ≤ tc5_G d c :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- `W(d, N, c) = (∑_{j ≤ N} K_j(c/2)) G(c)`. -/
def tc5_W (d : ℕ) (c : ℝ) (N : ℕ) : ℝ := (∑ j ∈ Finset.range (N + 1), tc5_Kp (c / 2) j) * tc5_G d c

theorem tc5_W_nonneg (d : ℕ) (c : ℝ) (N : ℕ) : 0 ≤ tc5_W d c N :=
  mul_nonneg (Finset.sum_nonneg fun j _ => tc5_Kp_nonneg _ _) (tc5_G_nonneg d c)

theorem tc5_rho_Dint {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {j : ℕ} (hj : j ≤ N) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j ρ x‖) ∧
      ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ S * tc5_Kp (c / 2) j * tc5_G d c := by
  have hS := tc5_S_nonneg hρ
  have hg := (tc4_integrable_gauss (d := d) (half_pos hc)).const_mul (S * tc5_Kp (c / 2) j)
  have hint : Integrable (fun x => ‖iteratedFDeriv ℝ j ρ x‖) :=
    hg.mono' (tc5_cont_D hρ j).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact tc5_rho_dbound hρ hc hj x)
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖iteratedFDeriv ℝ j ρ x‖
      ≤ ∫ x : Euc d, S * tc5_Kp (c / 2) j * Real.exp (-(c / 2) * ‖x‖ ^ 2) :=
        integral_mono hint hg fun x => tc5_rho_dbound hρ hc hj x
    _ = S * tc5_Kp (c / 2) j * tc5_G d c := by
        rw [integral_const_mul]; rfl

theorem tc5_rho_W {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    (∀ j ≤ N, Integrable (fun x => ‖iteratedFDeriv ℝ j ρ x‖) volume) ∧
      ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ tc5_W d c N * S := by
  refine ⟨fun j hj => (tc5_rho_Dint hρ hc hj).1, ?_⟩
  calc ∑ j ∈ Finset.range (N + 1), ∫ x, ‖iteratedFDeriv ℝ j ρ x‖
      ≤ ∑ j ∈ Finset.range (N + 1), S * tc5_Kp (c / 2) j * tc5_G d c :=
        Finset.sum_le_sum fun j hj =>
          (tc5_rho_Dint hρ hc (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).2
    _ = tc5_W d c N * S := by
        unfold tc5_W
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring

/-- `ρ ∈ H^J` with `‖ρ‖²_{H^J} ≤ B S²`. -/
theorem tc5_rho_sob (J : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ρ : Euc d → ℝ) (M₀ S : ℝ), TcRef d ρ M₀ c S J →
      MemSob (J : ℝ) ρ ∧ SobSq (J : ℝ) ρ ≤ B * S ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.TcS.tcs_sobolev_of_hsmooth d J
  set Gc : ℝ := ∫ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) with hGc
  have hGc0 : 0 ≤ Gc := integral_nonneg fun _ => (Real.exp_pos _).le
  set Ks : ℝ := ∑ j ∈ Finset.range (J + 1), tc5_Kp (c / 2) j with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun j _ => tc5_Kp_nonneg _ _
  refine ⟨C * (Ks * Real.sqrt Gc) ^ 2, by positivity, fun ρ M₀ S hρ => ?_⟩
  have hS := tc5_S_nonneg hρ
  -- derivative bounds
  have hsq : ∀ j ≤ J, ∀ x : Euc d, ‖iteratedFDeriv ℝ j ρ x‖ ^ 2 ≤
      (S * tc5_Kp (c / 2) j) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
    intro j hj x
    have h1 := tc5_rho_dbound hρ hc hj x
    have h0 := norm_nonneg (iteratedFDeriv ℝ j ρ x)
    calc ‖iteratedFDeriv ℝ j ρ x‖ ^ 2
        ≤ (S * tc5_Kp (c / 2) j * Real.exp (-(c / 2) * ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (S * tc5_Kp (c / 2) j) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hgc := tc4_integrable_gauss (d := d) hc
  have hint : ∀ j ≤ J, Integrable (fun x : Euc d => ‖iteratedFDeriv ℝ j ρ x‖ ^ 2) := fun j hj =>
    (hgc.const_mul ((S * tc5_Kp (c / 2) j) ^ 2)).mono'
      ((tc5_cont_D hρ j).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hsq j hj x)
  have hmem : HRS.Whole.MemHSmooth J ρ := by
    refine ⟨hρ.smooth.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩
    rw [memLp_two_iff_integrable_sq_norm (tc5_cont_D hρ j).aestronglyMeasurable]
    exact hint j hj
  obtain ⟨h1, h2⟩ := hC ρ hmem
  refine ⟨h1, h2.trans ?_⟩
  have hW : HRS.Whole.sobolevWNorm J 2 ρ ≤ S * (Ks * Real.sqrt Gc) := by
    unfold HRS.Whole.sobolevWNorm
    calc ∑ j ∈ Finset.range (J + 1), (∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        ≤ ∑ j ∈ Finset.range (J + 1), (S * tc5_Kp (c / 2) j) * Real.sqrt Gc := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have e1 : (∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ (2 : ℝ)) = ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ 2 := by
            simp only [Real.rpow_two]
          rw [e1, ← Real.sqrt_eq_rpow]
          have : ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ 2 ≤ (S * tc5_Kp (c / 2) j) ^ 2 * Gc := by
            calc ∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ 2
                ≤ ∫ x : Euc d, (S * tc5_Kp (c / 2) j) ^ 2 * Real.exp (-c * ‖x‖ ^ 2) :=
                  integral_mono (hint j hj') (hgc.const_mul _) fun x => hsq j hj' x
              _ = _ := by rw [integral_const_mul]
          calc Real.sqrt (∫ x, ‖iteratedFDeriv ℝ j ρ x‖ ^ 2)
              ≤ Real.sqrt ((S * tc5_Kp (c / 2) j) ^ 2 * Gc) := Real.sqrt_le_sqrt this
            _ = (S * tc5_Kp (c / 2) j) * Real.sqrt Gc := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hS (tc5_Kp_nonneg _ _))]
      _ = S * (Ks * Real.sqrt Gc) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  have hW0 : 0 ≤ HRS.Whole.sobolevWNorm J 2 ρ := by
    unfold HRS.Whole.sobolevWNorm
    exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  calc C * HRS.Whole.sobolevWNorm J 2 ρ ^ 2 ≤ C * (S * (Ks * Real.sqrt Gc)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW 2) hC0
    _ = C * (Ks * Real.sqrt Gc) ^ 2 * S ^ 2 := by ring

/-! ### Decomposition of `K` -/

theorem tc5_Kt_ae {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {θ : Euc d → ℝ} (h : TcCutoff θ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ) =
        locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x := by
  filter_upwards [tc4_ae_integrable hρ hc h hs0 hsd hf] with x hx using tc4_split_pt hρ.prob h hx


/-! ### Generic facts about `ρ` and `μ = ρ dx` -/

theorem tc5_ref_mono {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N N' : ℕ} (hρ : TcRef d ρ M₀ c S N) (h : N' ≤ N) :
    TcRef d ρ M₀ c S N' :=
  ⟨hρ.prob, hρ.pos, hρ.smooth, hρ.gauss, fun k hk x => hρ.deriv k (hk.trans h) x⟩

theorem tc5_rho_integrable {ρ : Euc d → ℝ} (h : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  refine Integrable.of_integral_ne_zero ?_
  rw [h.integral_one]; norm_num

theorem tc5_rho_le {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) (x : Euc d) :
    ρ x ≤ M₀ :=
  HRS.MS.TcR.tc2_le_M0 hρ.prob hc hρ.gauss x

theorem tc5_M0_nonneg {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) : 0 ≤ M₀ :=
  HRS.MS.TcR.tc2_M0_nonneg hρ.prob hρ.gauss

theorem tc5_rho_sq_integrable {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    Integrable (fun x => ρ x ^ 2) := by
  refine ((tc5_rho_integrable hρ.prob).const_mul M₀).mono'
    ((hρ.prob.measurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by have := hρ.prob.nonneg x; positivity)]
  have := hρ.prob.nonneg x
  have h2 := tc5_rho_le hρ hc x
  nlinarith

theorem tc5_rho_memLp2 {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    MemLp ρ 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hρ.prob.measurable.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs, sq_abs] using tc5_rho_sq_integrable hρ hc

theorem tc5_int_rho_sq {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    ∫ x, ρ x ^ 2 ≤ M₀ := by
  have h1 : ∫ x, ρ x ^ 2 ≤ ∫ x, M₀ * ρ x :=
    integral_mono (tc5_rho_sq_integrable hρ hc) ((tc5_rho_integrable hρ.prob).const_mul M₀) fun x => by
      have := hρ.prob.nonneg x
      have h2 := tc5_rho_le hρ hc x
      nlinarith
  rw [integral_const_mul, hρ.prob.integral_one, mul_one] at h1
  exact h1

/-- `L ∈ L²(dx)` implies `L ∈ L²(μ)` and `∫ L² dμ ≤ M₀ ∫ L² dx`. -/
theorem tc5_L_mu {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {L : Euc d → ℝ} (hL : MemLp L 2 volume) :
    MemLp L 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, L x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ M₀ * ∫ x, L x ^ 2 := by
  have hL2 : Integrable (fun x => L x ^ 2) := hL.integrable_sq
  have hint : Integrable (fun x => L x ^ 2) (HRS.Whole.withDensityReal ρ) := by
    rw [tc4_integrable_iff hρ.prob]
    refine (hL2.const_mul M₀).mono' (hρ.prob.measurable.aestronglyMeasurable.mul hL2.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hρ.prob.nonneg x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (tc5_rho_le hρ hc x) (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq_norm
      (hL.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _))).2 ?_
    have e : (fun x => ‖L x‖ ^ 2) = fun x => L x ^ 2 := by
      funext x; simp only [Real.norm_eq_abs, sq_abs]
    rw [e]; exact hint
  · rw [tc4_integral_wd hρ.prob.measurable hρ.prob.nonneg, ← integral_const_mul]
    refine integral_mono ((tc4_integrable_iff hρ.prob).1 hint) (hL2.const_mul M₀) fun x => ?_
    exact mul_le_mul_of_nonneg_right (tc5_rho_le hρ hc x) (sq_nonneg _)

/-- Bound for the centering constant `pair μ (L + F)`. -/
theorem tc5_pair_bound {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {L F : Euc d → ℝ} (hL : MemLp L 2 volume) (hFc : Continuous F) {B : ℝ} (hB : ∀ x, |F x| ≤ B) :
    (HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (fun x => L x + F x)) ^ 2 ≤
      2 * M₀ * (∫ x, L x ^ 2) + 2 * B ^ 2 := by
  have hρ2 := tc5_rho_memLp2 hρ hc
  have hM0 := tc5_M0_nonneg hρ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hρint := tc5_rho_integrable hρ.prob
  have hI1 : Integrable (fun x => ρ x * L x) := by
    refine ((hρ2.integrable_sq.add hL.integrable_sq).div_const 2).mono'
      (hρ.prob.measurable.aestronglyMeasurable.mul hL.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (ρ x), sq_abs (L x), sq_nonneg (|ρ x| - |L x|), abs_nonneg (ρ x), abs_nonneg (L x)]
  have hI2 : Integrable (fun x => ρ x * F x) := by
    refine (hρint.const_mul B).mono' (hρ.prob.measurable.aestronglyMeasurable.mul hFc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ.prob.nonneg x)]
    calc ρ x * |F x| ≤ ρ x * B := mul_le_mul_of_nonneg_left (hB x) (hρ.prob.nonneg x)
      _ = B * ρ x := mul_comm _ _
  have hpair : HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (fun x => L x + F x) =
      (∫ x, ρ x * L x) + ∫ x, ρ x * F x := by
    unfold HRS.Whole.pair
    rw [tc4_integral_wd hρ.prob.measurable hρ.prob.nonneg, ← integral_add hI1 hI2]
    congr 1; ext x; ring
  rw [hpair]
  set a := ∫ x, ρ x * L x with ha
  set b := ∫ x, ρ x * F x with hb
  have hLn : MemLp (fun x => |L x|) 2 volume := by simpa using hL.norm
  have hcs := tc4_cs (μ := volume) (u := ρ) (v := fun x => |L x|) hρ.prob.nonneg (fun x => abs_nonneg _)
    hρ2 hLn
  have ha1 : |a| ≤ ∫ x, ρ x * |L x| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; ext x
    rw [abs_mul, abs_of_nonneg (hρ.prob.nonneg x)]
  have hLL : ∫ x, |L x| ^ 2 = ∫ x, L x ^ 2 := by simp only [sq_abs]
  have hq0 : 0 ≤ ∫ x, L x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hp0 : 0 ≤ ∫ x, ρ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have ha2 : a ^ 2 ≤ M₀ * ∫ x, L x ^ 2 := by
    rw [hLL] at hcs
    have h1 : |a| ≤ Real.sqrt (∫ x, ρ x ^ 2) * Real.sqrt (∫ x, L x ^ 2) := ha1.trans hcs
    have h2 : |a| ^ 2 ≤ (Real.sqrt (∫ x, ρ x ^ 2) * Real.sqrt (∫ x, L x ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hq0] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right (tc5_int_rho_sq hρ hc) hq0)
  have hb1 : |b| ≤ B := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |ρ x * F x| ≤ ∫ x, B * ρ x := by
          refine integral_mono hI2.abs (hρint.const_mul B) fun x => ?_
          rw [abs_mul, abs_of_nonneg (hρ.prob.nonneg x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hB x) (hρ.prob.nonneg x)
      _ = B := by rw [integral_const_mul, hρ.prob.integral_one, mul_one]
  have hb2 : b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
  have hfin : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := hfin
    _ ≤ 2 * (M₀ * ∫ x, L x ^ 2) + 2 * B ^ 2 := by linarith
    _ = _ := by ring


/-- For `f ∈ L²(μ)`: `ρ f ∈ L² = H⁰` with `‖ρ f‖²_{L²} ≤ M₀ ∫ f² dμ`. -/
theorem tc5_rho_f_sob0 {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    {f : Euc d → ℝ} (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    MemSob 0 (fun y => ρ y * f y) ∧
      SobSq 0 (fun y => ρ y * f y) ≤ M₀ * ∫ y, f y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have := tc4_isProb hρ.prob
  have hf2 : Integrable (fun y => f y ^ 2) (HRS.Whole.withDensityReal ρ) := hf.integrable_sq
  have hI : Integrable (fun y => ρ y * f y ^ 2) := (tc4_integrable_iff hρ.prob).1 hf2
  have hmeas : AEStronglyMeasurable (fun y => ρ y * f y) volume :=
    ((tc4_integrable_iff hρ.prob).1 (hf.integrable (by norm_num))).aestronglyMeasurable
  have hsq : ∀ y, (ρ y * f y) ^ 2 ≤ M₀ * (ρ y * f y ^ 2) := fun y => by
    have h0 := hρ.prob.nonneg y
    have h1 := tc5_rho_le hρ hc y
    calc (ρ y * f y) ^ 2 = ρ y * (ρ y * f y ^ 2) := by ring
      _ ≤ M₀ * (ρ y * f y ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hint : Integrable (fun y => (ρ y * f y) ^ 2) :=
    (hI.const_mul M₀).mono' ((continuous_pow 2).comp_aestronglyMeasurable hmeas)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hsq y)
  have hmem : MemLp (fun y => ρ y * f y) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    simpa only [Real.norm_eq_abs, sq_abs] using hint
  refine ⟨⟨hmem, ?_⟩, ?_⟩
  · simpa using integrable_norm_sq_fourierL2 hmem
  · have e : SobSq 0 (fun y => ρ y * f y) = ∫ y, (ρ y * f y) ^ 2 := by
      unfold HRS.PDE.ToolboxRd.sobolevNormSq
      simp only [Real.rpow_zero, one_mul]
      exact integral_norm_sq_fourierL2 hmem
    rw [e, tc4_integral_wd hρ.prob.measurable hρ.prob.nonneg, ← integral_const_mul]
    exact integral_mono hint ((hI.const_mul M₀)) hsq

end HRS.MS.Tc5

end
