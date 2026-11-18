import HRS.MS.SA12X5D4D

/-!
# S.A.12 X5 D4: paired periodic coefficients

For two admissible coefficient sets with the same `(M, V)` whose densities differ by `δ` in `coeffNormE d s m`, the explicit periodic
approximants (`sa12x5_periodic_coefficients_explicit`, same `L, ε`, same `VL`) satisfy: the density difference `a = μL₁ - μL₂`
has jets up to order `m+2` and nearest-lattice decay `≤ Kd δ`, and the drift difference has jets up to order `m` `≤ Kd δ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_perApprox_mono {s : ℝ} {m : ℕ} {MB Λ' ΛV' νbar Cb T : ℝ} {D : WholeDyn d}
    {μ : ℝ → Euc d → ℝ} {γ : ℝ → Euc d → ℝ} {t L₀ L₀' : ℝ} {μL : ℝ → ℝ → ℝ → Euc d → ℝ}
    {VL : ℝ → ℝ → Euc d → ℝ} (h : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (hle : L₀ ≤ L₀') :
    PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀' μL VL :=
  ⟨fun L hL ε hε => h.1 L (le_trans (max_le_max le_rfl hle) hL) ε hε, h.2⟩

set_option maxHeartbeats 3200000 in
theorem sa12x5_paired_coeff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' ΛV' Cb L₀ Kd : ℝ, 0 ≤ Kd ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ →
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ → D₁.M = D₂.M → D₁.V = D₂.V →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ (μL₁ μL₂ : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ),
        PerApprox s (m + 2) MB Λ' ΛV' νbar Cb T D₁ μ₁ γ t L₀ μL₁ VL ∧
        PerApprox s (m + 2) MB Λ' ΛV' νbar Cb T D₂ μ₂ γ t L₀ μL₂ VL ∧
        (∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε ∈ Ioc (0 : ℝ) 1, PeriodicTimeSmooth T (μL₁ L ε)) ∧
        (∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε ∈ Ioc (0 : ℝ) 1, PeriodicTimeSmooth T (μL₂ L ε)) ∧
        ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) T,
          (∀ j ≤ m + 2, ∀ y : Euc d,
            ‖iteratedFDeriv ℝ j (fun x => μL₁ L ε τ x - μL₂ L ε τ x) y‖ ≤ Kd * δ) ∧
          (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
            jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
              ‖iteratedFDeriv ℝ j (fun x => μL₁ L ε τ x - μL₂ L ε τ x) x‖ ≤ Kd * δ) ∧
          (∀ j ≤ m, ∀ x : Euc d,
            ‖iteratedFDeriv ℝ j (fun x => torusDriftL D₁.M L (γ L) (μL₁ L ε τ) (VL L ε) x -
              torusDriftL D₁.M L (γ L) (μL₂ L ε τ) (VL L ε) x) x‖ ≤ Kd * δ) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm2 : 1 ≤ m' + 1 + 2 := by omega
  obtain ⟨Λ', ΛV', Cb, L₀', hC1⟩ :=
    sa12x5_periodic_coefficients_explicit hd s hs0 hsd (m' + 1 + 2) hm2 MB Λ ΛV G₀ νbar T ζ hζ
  obtain ⟨Bd, Bc, L₁, hBd0, hBc0, hL₁, hbase⟩ := sa12k_base s (m' + 1 + 2) T Λ ζ hζ
  choose Kz hKz0 hKz using fun i : ℕ => tca_bdd_iter ζ hζ i
  obtain ⟨P, hP0, hP⟩ := sa12x5_drift_diff hd hs0 hsd m' MB
  set Ig : ℝ := ∫ w : Euc d, tca_g w with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg fun w => tca_g_nonneg w
  set Bfac : ℝ := sa12x5_Bfac d Kz (m' + 1 + 2) |Λ| with hBfdef
  have hBf0 : 0 ≤ Bfac := by
    rw [hBfdef]
    unfold sa12x5_Bfac
    exact mul_nonneg (Finset.sum_nonneg fun j _ => by linarith [tca_S_nonneg d Kz hKz0 1 zero_le_one j])
      (by nlinarith [mul_nonneg hIg0 (abs_nonneg Λ)])
  set Cc : ℝ := 1 + 2 ^ d * Ig with hCc
  have hCc1 : 1 ≤ Cc := by
    have : 0 ≤ (2 : ℝ) ^ d * Ig := by positivity
    linarith
  set Kd : ℝ := ((2 : ℝ) ^ ((d : ℝ) + 3) + 1 + 2 * P * Cc) * Bfac with hKd
  have h2p : 0 ≤ (2 : ℝ) ^ ((d : ℝ) + 3) := by positivity
  have hKd0 : 0 ≤ Kd := by
    rw [hKd]
    have : 0 ≤ 2 * P * Cc := by positivity
    positivity
  refine ⟨Λ', ΛV', Cb, max L₀' L₁, Kd, hKd0, ?_⟩
  intro D₁ D₂ μ₁ μ₂ hD₁ hD₂ hM hV δ hδ hdist γ hγ t ht
  obtain ⟨μL₁, VL₁, hA₁, hT₁, he₁, hV₁⟩ := hC1 D₁ μ₁ hD₁ γ hγ t ht
  obtain ⟨μL₂, VL₂, hA₂, hT₂, he₂, hV₂⟩ := hC1 D₂ μ₂ hD₂ γ hγ t ht
  have hVL : VL₂ = VL₁ := by
    funext L ε
    rw [hV₁ L ε, hV₂ L ε, hV]
  have hA₂' := hVL ▸ hA₂
  refine ⟨μL₁, μL₂, VL₁, sa12x5_perApprox_mono hA₁ (le_max_left _ _),
    sa12x5_perApprox_mono hA₂' (le_max_left _ _),
    fun L hL ε hε => hT₁ L ((max_le_max le_rfl (le_max_left _ _)).trans hL) ε hε,
    fun L hL ε hε => hT₂ L ((max_le_max le_rfl (le_max_left _ _)).trans hL) ε hε, ?_⟩
  intro L hL ε hε τ hτ
  have hL' : max 1 L₀' ≤ L := (max_le_max le_rfl (le_max_left _ _)).trans hL
  have hLL1 : L₁ ≤ L := (le_max_right L₀' L₁).trans ((le_max_right 1 _).trans hL)
  have hL7 : 7 ≤ L := hL₁.trans hLL1
  have hL1 : 1 ≤ L := by linarith
  have hPD₁ := hA₁.1 L hL' ε hε
  have hPD₂ := hA₂'.1 L hL' ε hε
  have hρ₁ := sa12k_rev_hyp hD₁.hμ ht
  have hρ₂ := sa12k_rev_hyp hD₂.hμ ht
  have hrm : max (t - τ) 0 ∈ Icc (0 : ℝ) T :=
    ⟨le_max_right _ _, max_le (by linarith [ht.2, hτ.1]) (by linarith [ht.1, ht.2])⟩
  obtain ⟨hcd₁, -, -⟩ := sa12k_den_facts hρ₁ hτ
  obtain ⟨hcd₂, hWk₂, -⟩ := sa12k_den_facts hρ₂ hτ
  have hZ₁ := (hbase _ hρ₁ L hLL1 τ hτ).1
  have hZ₂ := (hbase _ hρ₂ L hLL1 τ hτ).1
  have hdist' := hdist _ hrm
  unfold coeffNormE at hdist'
  have hW : weightedSupE (m' + 1 + 2) ((d : ℝ) + 3) (μ₁ (max (t - τ) 0) - μ₂ (max (t - τ) 0)) ≤
      ENNReal.ofReal δ := le_trans le_add_self (le_trans le_self_add hdist')
  have hWne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hu : ∀ k : ℕ, k ≤ m' + 1 + 2 → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) *
        ‖iteratedFDeriv ℝ k (fun x => μ₁ (max (t - τ) 0) x - μ₂ (max (t - τ) 0) x) w‖ ≤
        (d : ℝ) ^ k * δ := fun k hk w =>
    (tca_weight_le (m' + 1 + 2) ((d : ℝ) + 3) _ hWne k hk w).trans
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hδ hW) (by positivity))
  obtain ⟨-, -, hsup, hdec, hcube⟩ := sa12x5_density_diff hζ L hL7 (sa12k_etaL_moll L)
    (sa12k_rad_le_one L) (m' + 1 + 2) Kz hKz hKz0 (μ₁ (max (t - τ) 0)) (μ₂ (max (t - τ) 0))
    (hcd₁.of_le (by exact_mod_cast (by omega))) (hcd₂.of_le (by exact_mod_cast (by omega)))
    |Λ| δ (abs_nonneg Λ) hδ (fun k hk w => hWk₂ k (by omega) w) hu hZ₁ hZ₂
  have ha : (fun x => μL₁ L ε τ x - μL₂ L ε τ x) =
      sa12x5_adiff (sa12k_etaL L) ζ (μ₁ (max (t - τ) 0)) (μ₂ (max (t - τ) 0)) L := by
    funext x
    rw [he₁ L ε τ, he₂ L ε τ]
    rfl
  rw [ha]
  have hBd : 0 ≤ δ * Bfac := mul_nonneg hδ hBf0
  have hPc : 0 ≤ Bfac * δ * (P * Cc) := by positivity
  have hKδ : Kd * δ = 2 ^ ((d : ℝ) + 3) * (δ * Bfac) + δ * Bfac + 2 * (Bfac * δ * (P * Cc)) := by
    rw [hKd]; ring
  refine ⟨fun j hj y => (hsup j hj y).trans ?_, fun j hj x => ?_, fun j hj x => ?_⟩
  · nlinarith [mul_nonneg h2p hBd]
  · obtain ⟨k, hk⟩ := hdec j hj x
    refine ⟨k, hk.trans ?_⟩
    nlinarith
  · have hμ₁s := (hPD₁.μ_smooth τ hτ).of_le (sa12k_le_infty (m' + 3))
    have hμ₂s := (hPD₂.μ_smooth τ hτ).of_le (sa12k_le_infty (m' + 3))
    have hB₁ : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i (μL₁ L ε τ) y‖ ≤ Λ' := fun i hi y =>
      hPD₁.μ_bdd τ hτ i (by omega) y
    have hB₂ : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i (μL₂ L ε τ) y‖ ≤ Λ' := fun i hi y =>
      hPD₂.μ_bdd τ hτ i (by omega) y
    have hAj : ∀ i ≤ m' + 3, ∀ y, ‖iteratedFDeriv ℝ i (fun x => μL₁ L ε τ x - μL₂ L ε τ x) y‖ ≤
        δ * Bfac * Cc := by
      intro i hi y
      rw [ha]
      refine (hsup i (by omega) y).trans ?_
      nlinarith [mul_nonneg hBd (sub_nonneg.2 hCc1)]
    have hAc : ∀ i ≤ m' + 1, ∀ x, ∫ z in tcb_Q d L,
        ‖iteratedFDeriv ℝ i (fun x => μL₁ L ε τ x - μL₂ L ε τ x) (x - z)‖ ≤ δ * Bfac * Cc := by
      intro i hi x
      rw [ha]
      refine (hcube i (by omega) x).trans ?_
      have : (2 : ℝ) ^ d * (δ * Bfac) * Ig = δ * Bfac * (2 ^ d * Ig) := by ring
      rw [this, hCc]
      nlinarith [mul_nonneg hBd (by norm_num : (0 : ℝ) ≤ 1)]
    have hmain := hP L hL1 (γ L) (hγ L hL1) D₁.M hPD₁.hM (μL₁ L ε τ) (μL₂ L ε τ) (VL₁ L ε) Λ'
      (δ * Bfac * Cc) (by positivity) hμ₁s hμ₂s hB₁ hB₂ hAj hAc j (by omega) x
    refine hmain.trans ?_
    nlinarith [hPc]

end HRS.MH.AdjointRd.Phase2SA12X5
