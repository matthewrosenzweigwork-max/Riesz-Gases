import HRS.MS.MovAdjAux22

/-!
# S6.7 (packet P4, part 9): the derivatives of the Duhamel integral

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_duh_bound`: if `Φ(x) = ∫_0^τ sg_{τ-s}(S_s)(x) ds` with `‖D^i S_s‖ ≤ A e^{-bs}` (`i ≤ m`), `Φ ∈ C^K`, then
`‖D^k Φ‖ ≤ C e^{-(min(c₀,b)/2) τ} A` for `1 ≤ k ≤ K` (`s67_param_deriv` and `s67_sg_decay`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow
  HRS.MS.PoisMax

universe w

variable {d : ℕ}

theorem s67_tau_exp_le {μ : ℝ} (hμ : 0 < μ) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ * Real.exp (-μ * τ) ≤ 2 / μ * Real.exp (-(μ / 2) * τ) := by
  have h1 : μ * τ / 2 ≤ Real.exp (μ * τ / 2) := by
    have := Real.add_one_le_exp (μ * τ / 2); linarith
  have h2 : τ ≤ 2 / μ * Real.exp (μ * τ / 2) := by
    have : τ = 2 / μ * (μ * τ / 2) := by field_simp
    calc τ = 2 / μ * (μ * τ / 2) := this
      _ ≤ 2 / μ * Real.exp (μ * τ / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : Real.exp (μ * τ / 2) * Real.exp (-μ * τ) = Real.exp (-(μ / 2) * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  calc τ * Real.exp (-μ * τ) ≤ 2 / μ * Real.exp (μ * τ / 2) * Real.exp (-μ * τ) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 / μ * Real.exp (-(μ / 2) * τ) := by rw [mul_assoc, h3]

set_option maxHeartbeats 1600000 in
theorem s67_duh_bound (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (K : ℕ) (hK1 : 1 ≤ K)
    (hKm : K ≤ m) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type w} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
      ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ A : ℝ, 0 ≤ A → ∀ τ : ℝ, 0 ≤ τ →
      ∀ S : ℝ → Euc d → ℝ, (∀ s ∈ Icc (0 : ℝ) τ, ContDiff ℝ (m : WithTop ℕ∞) (S s)) →
      (∀ s ∈ Icc (0 : ℝ) τ, ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i (S s) y‖ ≤ A * Real.exp (-b * s)) →
      (∀ x, ContinuousOn (fun s => sg P W q B (τ - s) (S s) x) (Icc 0 τ)) →
      ∀ Φ : Euc d → ℝ, (∀ x, Φ x = ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S s) x) →
      ContDiff ℝ (K : WithTop ℕ∞) Φ →
      ∀ k, 1 ≤ k → k ≤ K → ∀ x, ‖iteratedFDeriv ℝ k Φ x‖ ≤
        C * Real.exp (-(min (pm_c0 q Mb) b / 2) * τ) * A := by
  obtain ⟨Cd, hCd0, hCd⟩ := s67_sg_decay.{w} (d := d) q Mb hq hMb m hm
  have hc0pos : 0 < pm_c0 q Mb := by
    unfold pm_c0 pm_kappa
    exact mul_pos (Real.exp_pos _) (lt_min zero_lt_one (by positivity))
  set c0 := pm_c0 q Mb with hc0
  set μ := min c0 b with hμ
  have hμpos : 0 < μ := lt_min hc0pos hb
  refine ⟨Cd * K * (2 / μ), by positivity, ?_⟩
  intro Ω mΩ P _ ℱ W hW B hBm A hA τ hτ S hS hSb hGc Φ hΦ hΦK k hk1 hkK x
  have hWs := sgNoise_of_brownian hW
  set gf : ℝ → ℝ := fun s => Cd * Real.exp (-c0 * (τ - s)) * (K * (A * Real.exp (-b * s))) with hgf
  have hgf0 : ∀ s, 0 ≤ gf s := fun s => by simp only [hgf]; positivity
  have hgfc : Continuous gf := by simp only [hgf]; fun_prop
  have hgi : IntervalIntegrable gf volume 0 τ := hgfc.intervalIntegrable _ _
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm τ hτ K hKm
  have hGk : ∀ s ∈ Icc (0 : ℝ) τ, ContDiff ℝ (K : WithTop ℕ∞) (fun y => sg P W q B (τ - s) (S s) y) := by
    intro s hs
    exact (hCsg P W hWs B hBm (S s) ((hS s hs).of_le (by exact_mod_cast hKm)) (A * Real.exp (-b * s))
      (fun i hi y => hSb s hs i (hi.trans hKm) y) (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).1
  have hg : ∀ s ∈ Icc (0 : ℝ) τ, ∀ i, 1 ≤ i → i ≤ K → ∀ y,
      ‖iteratedFDeriv ℝ i (fun y => sg P W q B (τ - s) (S s) y) y‖ ≤ gf s := by
    intro s hs i hi1 hiK y
    have h1 := hCd i hi1 (hiK.trans hKm) P ℱ W hW B hBm (S s) (hS s hs) (fun _ => A * Real.exp (-b * s))
      (fun i' hi' y' => hSb s hs i' hi' y') (τ - s) (by linarith [hs.2]) y
    refine h1.trans ?_
    have hsum : ∑ i' ∈ Finset.Icc 1 i, A * Real.exp (-b * s) = (i : ℝ) * (A * Real.exp (-b * s)) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    rw [hsum]
    simp only [hgf]
    have : (i : ℝ) ≤ K := by exact_mod_cast hiK
    have e : -c0 * (τ - s) = -pm_c0 q Mb * (τ - s) := rfl
    rw [e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by positivity)) (by positivity)
  have hpd := s67_param_deriv hτ (G := fun s y => sg P W q B (τ - s) (S s) y) (g := gf) (K := K) hGc hGk hg
    hgi hΦ hΦK
  -- the operator norm bound
  have hint0 : 0 ≤ ∫ s in (0 : ℝ)..τ, gf s := intervalIntegral.integral_nonneg hτ (fun s _ => hgf0 s)
  have hnorm : ‖iteratedFDeriv ℝ k Φ x‖ ≤ ∫ s in (0 : ℝ)..τ, gf s := by
    refine ContinuousMultilinearMap.opNorm_le_bound hint0 fun w => ?_
    obtain ⟨hI, hE⟩ := hpd k hkK x w
    rw [hE]
    set Pw : ℝ := ∏ l : Fin k, ‖w l‖ with hPw
    have hPw0 : 0 ≤ Pw := Finset.prod_nonneg fun l _ => norm_nonneg _
    have hle := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := τ) hτ
      (f := fun s => iteratedFDeriv ℝ k (fun y => sg P W q B (τ - s) (S s) y) x w)
      (g := fun s => gf s * Pw)
      (Eventually.of_forall fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) τ := ⟨hs.1.le, hs.2⟩
        exact ((iteratedFDeriv ℝ k (fun y => sg P W q B (τ - s) (S s) y) x).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hg s hs' k hk1 hkK x) hPw0))
      (hgi.mul_const Pw)
    rw [intervalIntegral.integral_mul_const] at hle
    exact hle
  -- the integral of `gf`
  have hbd : ∀ s ∈ Icc (0 : ℝ) τ, gf s ≤ Cd * K * A * Real.exp (-μ * τ) := by
    intro s hs
    simp only [hgf]
    have h1 : Real.exp (-c0 * (τ - s)) * Real.exp (-b * s) ≤ Real.exp (-μ * τ) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hc : μ ≤ c0 := min_le_left _ _
      have hb' : μ ≤ b := min_le_right _ _
      nlinarith [hs.1, hs.2]
    calc Cd * Real.exp (-c0 * (τ - s)) * (K * (A * Real.exp (-b * s)))
        = Cd * K * A * (Real.exp (-c0 * (τ - s)) * Real.exp (-b * s)) := by ring
      _ ≤ Cd * K * A * Real.exp (-μ * τ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint1 : ∫ s in (0 : ℝ)..τ, gf s ≤ τ * (Cd * K * A * Real.exp (-μ * τ)) := by
    have := intervalIntegral.integral_mono_on hτ hgi (intervalIntegrable_const (c := Cd * K * A * Real.exp (-μ * τ)))
      hbd
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact this
  have h2 := s67_tau_exp_le hμpos hτ
  calc ‖iteratedFDeriv ℝ k Φ x‖ ≤ τ * (Cd * K * A * Real.exp (-μ * τ)) := hnorm.trans hint1
    _ = Cd * K * A * (τ * Real.exp (-μ * τ)) := by ring
    _ ≤ Cd * K * A * (2 / μ * Real.exp (-(μ / 2) * τ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Cd * K * (2 / μ) * Real.exp (-(min (pm_c0 q Mb) b / 2) * τ) * A := by rw [hμ]; ring

end HRS.MS.MovAdj
