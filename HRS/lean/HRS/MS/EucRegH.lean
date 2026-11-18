import HRS.MS.EucRegHAux3
import HRS.MS.EucReg

/-!
# C-REG-h: `euc_thermal_regularity` in the hard regime `d - 1 ≤ s < d`, and the full frozen theorem

Namespace `HRS.MS.Thm`, helper prefix `regh_`.

Route (Hölder gain, no Littlewood-Paley).  `U = ∫ ‖x-y‖^{-s} ρ(y) dy = T ρ` and `ρ = e^{-β(a‖x‖²/2+U)}/Z`.
* `regh_Tk_hold`/`regh_T_hold` (Aux2): for `F` bounded, rapidly decaying and `θ`-Hölder, `T F` is
  `(θ + a)`-Hölder, `a = d - σ`, `σ = (s+d)/2` (the localised kernel `k = ‖z‖^{-s} - (1+‖z‖²)^{-s/2}` is integrable and
  `∫ (k(z+h) - k(z)) dz = 0`).
* `regh_cross` (Aux3): if moreover `θ > 1 - (d - s)`, `T F` is `C¹` with a Hölder derivative (second-order Taylor
  estimate of `k` for the remainder, Hölder-interpolation `[Δ_h F]_{θ'} ≲ |h|^{θ-θ'}` for the derivative).
* The recursive class `regh_C` (`C^k` with Hölder `D^k`) is closed under sums, products and `exp` (Aux3); `regh_gain_rec`,
  `regh_cross_rec` lift both facts to all orders (the derivative of `T F` is `T (DF)`).
* `regh_bootstrap`: `U ∈ C^k_{b}` with Hölder `D^k U` for every `k`, by induction, alternating gain and crossing.
* `euc_thermal_regularity_proof`: cases `s < d - 1` (`euc_thermal_regularity_easy`) and `d - 1 ≤ s` (this file).

No statement was adjusted.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

variable {d : ℕ}

lemma regh_U_eq (s : ℝ) (F : Euc d → ℝ) : rege_U s F = regh_T s F := by
  funext x
  have := integral_sub_left_eq_self (fun z : Euc d => ‖z‖ ^ (-s) * F (x - z)) volume x
  simp only [sub_sub_cancel] at this
  unfold rege_U regh_T
  simp only [smul_eq_mul]
  rw [← this]

/-- From the class for `U` to the class for `ρ` (and decay of all its derivatives). -/
lemma regh_rho_of_U {s a β Z C0 θ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hZ : 0 < Z) {ρ : Euc d → ℝ}
    (heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) / Z)
    (hup : ∀ x, ρ x ≤ C0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (k : ℕ)
    (hU : regh_Cl θ k (rege_U s ρ)) : regh_Cl θ k ρ ∧ regh_Rl k ρ := by
  have hb2 : 0 < β * a / 2 := by positivity
  obtain ⟨hUk, M, hM⟩ := regh_Cl_contDiff hθ k hU
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  obtain ⟨C, hC, hD⟩ := rege_exponent_bound a β hUk hM0 (fun i _ hik x => (hM i hik x).trans (le_max_left _ _))
  have hφ : ContDiff ℝ k (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) :=
    contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUk)
  obtain ⟨-, hρD⟩ := rege_rho_deriv hZ heq hup hφ hC hD
  refine ⟨?_, regh_R_of_iter k fun j hj => ?_⟩
  · have e : ρ = fun x => (Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z) *
        Real.exp ((-β) • rege_U s ρ x) := funext fun x => by
      rw [heq x, smul_eq_mul, show -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x) =
        -β * (a * ‖x‖ ^ 2 / 2 + 0) + -β * rege_U s ρ x by ring, Real.exp_add]
      ring
    rw [e]
    exact regh_Cl_prod hθ.le hθ1 k (ContinuousLinearMap.mul ℝ ℝ) (regh_gauss_Cl ha hβ hZ hθ.le hθ1 k)
      (regh_Cl_exp hθ.le hθ1 k (regh_Cl_smul (-β) k hU))
  · obtain ⟨K, hK, hKb⟩ := hρD j hj
    exact rege_rdec_of_gauss (j := j) hb2 hK (fun x => by rw [← rege_exp_form]; exact hKb x)

/-- **Bootstrap in the hard regime**: `U = ∫ ‖x-y‖^{-s} ρ(y) dy` is `C^∞` with bounded derivatives of every
positive order (`d - 1 ≤ s < d`). -/
theorem regh_bootstrap {s a β Z C0 : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d)
    (hs1 : (d : ℝ) - 1 ≤ s) (ha : 0 < a) (hβ : 0 < β) (hZ : 0 < Z) {ρ : Euc d → ℝ}
    (hm : Measurable ρ) (heq : ∀ x, ρ x = Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) / Z)
    (hup : ∀ x, ρ x ≤ C0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) :
    ∀ k : ℕ, ContDiff ℝ k (rege_U s ρ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ i (rege_U s ρ) x‖ ≤ M := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (d : ℝ) - s := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 - α / 4 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; linarith
  have hT1 : T < 1 := by rw [hT]; linarith
  have hs2 : (d : ℝ) < s + 2 := by linarith
  have hσe : (d : ℝ) - (s + α / 2) = α / 2 := by rw [hα]; ring
  have hUeq : rege_U s ρ = regh_T s ρ := regh_U_eq s ρ
  have hb2 : 0 < β * a / 2 := by positivity
  have hdec : lreg_RDec ρ := by
    have hρpos : ∀ x, 0 ≤ ρ x := fun x => by rw [heq x]; positivity
    refine rege_rdec_of_gauss (j := 0) hb2 (K := max C0 0) (le_max_right _ _) (fun x => ?_)
    rw [Real.norm_of_nonneg (hρpos x), pow_zero, mul_one, ← rege_exp_form]
    exact (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hgain : ∀ (k : ℕ) (θ θ' : ℝ), 0 < θ → regh_Cl θ k ρ → regh_Rl k ρ → 0 ≤ θ' → θ' ≤ θ →
      θ' + α / 2 < 1 → regh_Cl (θ' + α / 2) k (regh_T s ρ) := by
    intro k θ θ' hθ hρC hρR h0 h1 h2
    have := regh_gain_rec hd1 hs hsd hs2 (σ := s + α / 2) (by linarith) (by linarith) (by rw [hα] at *; linarith)
      hθ k hρC hρR θ' h0 h1 (by rw [hσe]; exact h2)
    rwa [hσe] at this
  -- raising the Hölder exponent
  have hlift : ∀ (k : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → regh_Cl θ k (rege_U s ρ) →
      regh_Cl (min (θ + α / 2) T) k (rege_U s ρ) := by
    intro k θ hθ hθT hU
    obtain ⟨hρC, hρR⟩ := regh_rho_of_U ha hβ hZ heq hup hθ (by linarith) k hU
    have := hgain k θ (min θ (T - α / 2)) hθ hρC hρR (le_min hθ.le (by rw [hT]; linarith))
      (min_le_left _ _) (by have := min_le_right θ (T - α / 2); linarith)
    rw [← hUeq] at this
    have e : min θ (T - α / 2) + α / 2 = min (θ + α / 2) T := by
      simp only [min_def]; split_ifs <;> linarith
    rwa [e] at this
  have hloopn : ∀ (k n : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → regh_Cl θ k (rege_U s ρ) →
      T ≤ θ + n * (α / 2) → regh_Cl T k (rege_U s ρ) := by
    intro k n
    induction n with
    | zero =>
      intro θ hθ hθT hU hle
      have : θ = T := le_antisymm hθT (by simpa using hle)
      rwa [this] at hU
    | succ n ih =>
      intro θ hθ hθT hU hle
      have h1 := hlift k θ hθ hθT hU
      by_cases hc : T ≤ θ + α / 2
      · rwa [min_eq_right hc] at h1
      · push_neg at hc
        rw [min_eq_left hc.le] at h1
        exact ih (θ + α / 2) (by linarith) hc.le h1 (by push_cast at hle; linarith)
  have hloop : ∀ (k : ℕ) (θ : ℝ), 0 < θ → θ ≤ T → regh_Cl θ k (rege_U s ρ) →
      regh_Cl T k (rege_U s ρ) := by
    intro k θ hθ hθT hU
    obtain ⟨n, hn⟩ := exists_nat_ge (T / (α / 2))
    refine hloopn k n θ hθ hθT hU ?_
    have : T ≤ n * (α / 2) := by rwa [div_le_iff₀ (by positivity)] at hn
    linarith
  -- base: level 0
  have hbase : regh_Cl (α / 2) 0 (rege_U s ρ) := by
    obtain ⟨C1, hC1, h1⟩ := lreg_bound_of_rdec hdec 0
    have hB : ∀ x, ‖ρ x‖ ≤ C1 := fun x =>
      (by simpa using h1 x : ‖ρ x‖ ≤ C1 * lreg_phi d x).trans (by nlinarith [lreg_phi_le_one (d := d) x])
    have hK : ∀ x h, ‖ρ (x + h) - ρ x‖ ≤ (2 * C1) * ‖h‖ ^ (0 : ℝ) := fun x h => by
      rw [Real.rpow_zero, mul_one]
      calc _ ≤ ‖ρ (x + h)‖ + ‖ρ x‖ := norm_sub_le _ _
        _ ≤ C1 + C1 := add_le_add (hB _) (hB _)
        _ = _ := by ring
    obtain ⟨⟨Bt, hBt⟩, K', hK'0, hK'⟩ := regh_T_hold hd1 hs hsd hs2 (σ := s + α / 2) (by linarith)
      (by linarith) (by rw [hα] at *; linarith) le_rfl (by rw [hσe]; linarith) hm.aestronglyMeasurable hdec
      (by positivity) hK
    rw [hσe, zero_add] at hK'
    rw [hUeq]
    exact ⟨(regh_hol_cont (by positivity) hK').aestronglyMeasurable, ⟨Bt, hBt⟩, K', hK'0, hK'⟩
  have hcross : ∀ k : ℕ, regh_Cl T k (rege_U s ρ) → regh_Cl (α / 4) (k + 1) (rege_U s ρ) := by
    intro k hU
    obtain ⟨hρC, hρR⟩ := regh_rho_of_U ha hβ hZ heq hup hT0 hT1.le k hU
    have := regh_cross_rec hd1 hs hsd hs2 (θ := T) (θ' := 1 - α / 2) hT0 hT1.le (by linarith)
      (by rw [hT]; linarith) (by rw [← hα]; linarith) (by rw [← hα]; linarith) k hρC hρR
    rw [← hUeq] at this
    have e : T - (1 - α / 2) = α / 4 := by rw [hT]; ring
    rwa [e] at this
  have hmain : ∀ k : ℕ, regh_Cl T k (rege_U s ρ) := by
    intro k
    induction k with
    | zero => exact hloop 0 (α / 2) (by positivity) (by rw [hT]; linarith) hbase
    | succ k ih => exact hloop (k + 1) (α / 4) (by positivity) (by rw [hT]; linarith) (hcross k ih)
  intro k
  obtain ⟨hc, M, hM⟩ := regh_Cl_contDiff hT0 k (hmain k)
  exact ⟨hc, max M 0, le_max_right _ _, fun i _ hik x => (hM i hik x).trans (le_max_left _ _)⟩

/-- The thermal regularity theorem for `d - 1 ≤ s < d`. -/
theorem regh_euc_thermal_regularity_hard {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hs1 : (d : ℝ) - 1 ≤ s) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ContDiff ℝ ∞ (thermalDensity d s a β) ∧
    ContDiff ℝ ∞ (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x‖ ≤ C) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) ∧
    (∀ k : ℕ, Integrable (fun x => ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) ∧
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤ C) ∧
    ∀ (k : ℕ) (p : ℝ), 0 ≤ p →
      Integrable (fun x => ‖x‖ ^ p * ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Z, C0, hZ, hC0, hρ0, hρm, heq, hup, hU⟩ := rege_data hd hs0 hsd ha hβ
  set ρ := thermalDensity d s a β with hρdef
  have hb2 : 0 < β * a / 2 := by positivity
  have boot := regh_bootstrap hd1 hs0 hsd hs1 ha hβ hZ hρm heq hup
  have hfun : HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) = rege_U s ρ := funext hU
  have hρn : ∀ n : ℕ, ContDiff ℝ n ρ ∧ ∀ j ≤ n, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖iteratedFDeriv ℝ j ρ x‖ ≤ K * (1 + ‖x‖) ^ j * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by
    intro n
    obtain ⟨hUn, M, hM0, hM⟩ := boot n
    obtain ⟨C, hC, hD⟩ := rege_exponent_bound a β hUn hM0 hM
    have hφ : ContDiff ℝ n (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUn)
    exact rege_rho_deriv hZ heq hup hφ hC hD
  have hρinf : ContDiff ℝ ∞ ρ := contDiff_infty.2 fun n => (hρn n).1
  -- Gaussian envelope for every `k`
  have henv : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤
      K * (1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
    intro k
    obtain ⟨K, hK, hKb⟩ := (hρn k).2 k le_rfl
    exact ⟨K, hK, fun x => by rw [← rege_exp_form]; exact hKb x⟩
  rw [hfun]
  refine ⟨hρinf, contDiff_infty.2 fun k => (boot k).1, fun k => ?_, fun k => ?_, fun k => ?_,
    fun k p hp => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨Cb, hCb, h0⟩ := lreg_bound_of_rdec
        (rege_rdec_of_gauss (j := 0) hb2 (K := max C0 0) (le_max_right _ _) (fun x => by
          rw [Real.norm_of_nonneg (hρ0 x), pow_zero, mul_one, ← rege_exp_form]
          exact (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)))
        0
      refine ⟨Cb * lreg_A d s, fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      exact rege_U_bound hd1 hs0 hsd hρm.aestronglyMeasurable hCb (fun y => by simpa using h0 y) x
    · obtain ⟨_, M, _, hM⟩ := boot k
      exact ⟨M, fun x => hM k hk le_rfl x⟩
  · obtain ⟨K, hK, hKb⟩ := (hρn k).2 k le_rfl
    exact ⟨K, hKb⟩
  · obtain ⟨K, hK, hKb⟩ := henv k
    have hcont : Continuous (iteratedFDeriv ℝ k ρ) := (hρn k).1.continuous_iteratedFDeriv le_rfl
    refine ⟨?_, ?_⟩
    · have := rege_weighted_integrable hb2 (G := iteratedFDeriv ℝ k ρ) (j := k) (K := K)
        hcont.aestronglyMeasurable hKb 0 le_rfl
      simpa using this
    · obtain ⟨C, hC, hCb⟩ := rege_poly_gauss_bdd hb2 k
      refine ⟨K * C, fun x => ?_⟩
      calc ‖iteratedFDeriv ℝ k ρ x‖ ≤ K * (1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := hKb x
        _ = K * ((1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) := by ring
        _ ≤ K * C := mul_le_mul_of_nonneg_left (hCb _ (norm_nonneg x)) hK
  · obtain ⟨K, hK, hKb⟩ := henv k
    have hcont : Continuous (iteratedFDeriv ℝ k ρ) := (hρn k).1.continuous_iteratedFDeriv le_rfl
    exact rege_weighted_integrable hb2 (G := iteratedFDeriv ℝ k ρ) (j := k) (K := K)
      hcont.aestronglyMeasurable hKb p hp

/-- **C-REG.**  `euc_thermal_regularity`, all `0 < s < d`: the easy regime `s < d - 1` and the hard regime
`d - 1 ≤ s` (Hölder gain). -/
theorem euc_thermal_regularity_proof : type_of% @HRS.Whole.euc_thermal_regularity := by
  intro d s hd hs0 hsd a β ha hβ
  by_cases hs1 : s < (d : ℝ) - 1
  · exact euc_thermal_regularity_easy hd hs0 hsd hs1 a β ha hβ
  · exact regh_euc_thermal_regularity_hard hd hs0 hsd (not_lt.1 hs1) a β ha hβ

end HRS.MS.Thm

end
