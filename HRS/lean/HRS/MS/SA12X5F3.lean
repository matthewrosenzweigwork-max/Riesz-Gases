import HRS.MS.SA12X5F2
import HRS.MS.SA12X5D5
import HRS.MS.SA12X5D5E
import HRS.MS.SA12X5D2
import HRS.MS.SA12X5P0
import HRS.MS.SA12X3C15
import HRS.MS.SA12X3C10
import HRS.MS.SA12X3C7D3
import HRS.MS.SA12X3P2A
import HRS.MS.SA12Z3NearN7E

/-!
# S.A.12 X5 F3: the difference of two periodic solutions in `H^m_uloc`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction
  HRS.MH.AdjointRd.Phase2SA12Assembly

variable {d : ℕ}

theorem sa12x5_periodic_diff_uloc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν₁ ν₂ : ℝ)
      (μ₁ μ₂ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b₁ b₂ : ℝ → Euc d → Euc d) (A : ℝ), 0 ≤ A → L₁ ≤ L →
      PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₁ μ₁ V b₁ →
      PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₂ μ₂ V b₂ →
      RdRegimeHolds Rg d s M ν₁ ν₀ → RdRegimeHolds Rg d s M ν₂ ν₀ →
      PeriodicTimeSmooth T μ₁ → PeriodicTimeSmooth T μ₂ →
      (∀ τ ∈ Icc (0 : ℝ) T,
        (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun x => μ₁ τ x - μ₂ τ x) y‖ ≤ A) ∧
        (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
          jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
            ‖iteratedFDeriv ℝ j (fun x => μ₁ τ x - μ₂ τ x) x‖ ≤ A) ∧
        (∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j (fun x => b₁ τ x - b₂ τ x) y‖ ≤ A)) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ F₁ F₂ : ℝ → Euc d → ℝ,
        IsPerSol (m + 2) L γ M ν₁ μ₁ b₁ (fun _ _ => 0) t F₁ →
        IsPerSol (m + 2) L γ M ν₂ μ₂ b₂ (fun _ _ => 0) t F₂ → F₁ 0 = F₂ 0 →
        ulocNormE (m + 2) χ (F₁ 0) < ⊤ →
        ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * (|ν₁ - ν₂| + A)) *
            ulocNormE (m + 2) χ (F₁ 0) := by
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨C2, L2, hC2, h2⟩ := sa12x5_periodic_source_bound hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨C15, L15, hC15, h15⟩ := periodic_uloc_bound hd s hs0 hsd (m + 2) (by omega) Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨C3, L3, hC30, h3⟩ := sa12x5_source_cell_bound hd hs0 hsd m hm MB Cb T χ χh hχp E hE
  set C : ℝ := C2 + C15 + 1 + C2 * C3 * C15 ^ 2 with hCdef
  have hCge : C2 + C15 + 1 ≤ C := by rw [hCdef]; nlinarith [mul_nonneg (mul_nonneg hC2.le hC30) (sq_nonneg C15)]
  have hCge2 : C2 * C3 * C15 ^ 2 ≤ C := by rw [hCdef]; linarith
  have hC1 : 1 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, max (max L2 L15) L3, hCpos, ?_⟩
  intro ν₀ L γ M ν₁ ν₂ μ₁ μ₂ V b₁ b₂ A hA0 hL hPD₁ hPD₂ hR₁ hR₂ hT₁ hT₂ hdiff t ht F₁ F₂ hF₁ hF₂ hF0 hU τ hτ
  have hL2 : L2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL15 : L15 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL3 : L3 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hPD₁.hL
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  obtain ⟨k, hk1, hklam⟩ := sa12x3_lam_lin hR₁ (PDE.thetaOrder d s)
  have hk0 : 0 ≤ k := by linarith
  set U₀ : ℝ := (ulocNormE (m + 2) χ (F₁ 0)).toReal with hU₀
  have hUfin : ulocNormE (m + 2) χ (F₁ 0) = ENNReal.ofReal U₀ := (ENNReal.ofReal_toReal hU.ne).symm
  have hU00 : 0 ≤ U₀ := ENNReal.toReal_nonneg
  -- the bound for F₂
  have hb2 := h15 ν₀ L γ M ν₂ μ₂ V b₂ hL15 hPD₂ hR₂ t ht F₂ hF₂
  have hUσ : ∀ σ ∈ Icc (0 : ℝ) t, ulocNormE (m + 2) χ (F₂ σ) ≤
      ENNReal.ofReal (C15 * Real.exp (C15 * k * σ) * U₀) := by
    intro σ hσ
    have h := hb2 σ hσ
    rw [← hF0, hUfin, hklam C15, ← ENNReal.ofReal_mul (by positivity)] at h
    exact h
  have hUσr : ∀ σ ∈ Icc (0 : ℝ) t, (ulocNormE (m + 2) χ (F₂ σ)).toReal ≤ C15 * Real.exp (C15 * k * σ) * U₀ :=
    fun σ hσ => ENNReal.toReal_le_of_le_ofReal (by positivity) (hUσ σ hσ)
  have hUσfin : ∀ σ ∈ Icc (0 : ℝ) t, ulocNormE (m + 2) χ (F₂ σ) < ⊤ :=
    fun σ hσ => lt_of_le_of_lt (hUσ σ hσ) ENNReal.ofReal_lt_top
  -- the difference is a periodic solution
  have hG := sa12x5_diff_isPerSol hd hs0 hsd hPD₁.toPerSmooth hPD₂.toPerSmooth hT₁ hT₂ htT hF₁ hF₂
  have hGm := sa12x3p_isPerSol_mono (N' := m) (Nat.le_add_right m 2) hG
  have hF2s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F₂ σ) := fun σ hσ => (hF₂.sol.smooth σ hσ).1
  have hmem : ∀ σ ∈ Icc (0 : ℝ) t, σ ∈ Icc (0 : ℝ) T := fun σ hσ => ⟨hσ.1, hσ.2.trans ht.2⟩
  have hdbs : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (fun x => b₁ σ x - b₂ σ x) := fun σ hσ =>
    (sa12x5_drift_smooth hd hs0 hsd hPD₁.toPerSmooth hT₁ ht.2 hσ).sub
      (sa12x5_drift_smooth hd hs0 hsd hPD₂.toPerSmooth hT₂ ht.2 hσ)
  have hSs : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ σ) := by
    intro σ hσ
    have hσT := hmem σ hσ
    have e1 := sa12x5_perNonlocal_smooth hL0 hPD₁.hγ.locInt hPD₁.hγ.periodic M
      (hPD₁.μ_smooth σ hσT) (hF2s σ hσ) (hPD₁.μ_periodic σ hσT) (hF₂.periodic σ hσ)
    have e2 := sa12x5_perNonlocal_smooth hL0 hPD₁.hγ.locInt hPD₁.hγ.periodic M
      (hPD₂.μ_smooth σ hσT) (hF2s σ hσ) (hPD₂.μ_periodic σ hσT) (hF₂.periodic σ hσ)
    show ContDiff ℝ ∞ (fun x => (ν₁ - ν₂) * Laplacian.laplacian (F₂ σ) x +
      inner ℝ (b₁ σ x - b₂ σ x) (gradient (F₂ σ) x) -
      (perNonlocal L γ M (μ₁ σ) (F₂ σ) x - perNonlocal L γ M (μ₂ σ) (F₂ σ) x))
    exact ((contDiff_const.mul (sa12x5_lap_smooth (hF2s σ hσ))).add
      ((hdbs σ hσ).inner ℝ (sa12y_grad_contDiff (hF2s σ hσ)))).sub (e1.sub e2)
  -- the source bound
  set Δ : ℝ := |ν₁ - ν₂| + A with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  set Hf : ℝ → ℝ := fun σ => C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * σ) * U₀) ^ 2 with hHf
  have hHf0 : ∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ Hf σ := fun σ _ => by positivity
  have hHfc : Continuous Hf := by rw [hHf]; fun_prop
  have hsrc : ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b₁ Ψ → ∀ σ ∈ Icc (0 : ℝ) t, ∀ z : Fin d → ℤ,
      cellEnergy m χ Ψ σ (cellPt d z) (sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ σ) ≤ Hf σ := by
    intro Ψ hΨ σ hσ z
    have hσT := hmem σ hσ
    obtain ⟨hj, hdc, hdb⟩ := hdiff σ hσT
    have hmus : ContDiff ℝ ∞ (fun x => μ₁ σ x - μ₂ σ x) := (hPD₁.μ_smooth σ hσT).sub (hPD₂.μ_smooth σ hσT)
    have hmup : ∀ (x : Euc d) (k : Fin d → ℤ), (fun x => μ₁ σ x - μ₂ σ x) (x + L • latticePt k) =
        (fun x => μ₁ σ x - μ₂ σ x) x := fun x k => by
      simp only [hPD₁.μ_periodic σ hσT x k, hPD₂.μ_periodic σ hσT x k]
    have hbdd : BddJets m (F₂ σ) := ⟨(hF₂.bdd σ hσ).1, fun j hj => (hF₂.bdd σ hσ).2 j (by omega)⟩
    have h := h3 b₁ Ψ hPD₁.b_drift hΨ σ hσT L γ hL3 hPD₁.hγ M hPD₁.hM ν₁ ν₂ (fun x => μ₁ σ x - μ₂ σ x)
      (F₂ σ) (fun x => b₁ σ x - b₂ σ x) hmus (hF2s σ hσ) (hdbs σ hσ) hmup (hF₂.periodic σ hσ) hbdd A hA0
      hj hdc hdb (hUσfin σ hσ) z
    have e : sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ σ = fun x => (ν₁ - ν₂) * Laplacian.laplacian (F₂ σ) x +
        inner ℝ (b₁ σ x - b₂ σ x) (gradient (F₂ σ) x) -
        perNonlocal L γ M (fun x => μ₁ σ x - μ₂ σ x) (F₂ σ) x := by
      funext x
      unfold sa12x5_src
      rw [sa12x5_perNonlocal_sub_mu hL0 hPD₁.hγ.locInt hPD₁.hγ.periodic M (hPD₁.μ_smooth σ hσT)
        (hPD₂.μ_smooth σ hσT) (hF2s σ hσ) (hPD₁.μ_periodic σ hσT) (hPD₂.μ_periodic σ hσT)
        (hF₂.periodic σ hσ) x]
    rw [e]
    refine h.trans ?_
    rw [hHf]
    have hsq : (ulocNormE (m + 2) χ (F₂ σ)).toReal ^ 2 ≤ (C15 * Real.exp (C15 * k * σ) * U₀) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hUσr σ hσ) 2
    have : C3 * Δ ^ 2 * (ulocNormE (m + 2) χ (F₂ σ)).toReal ^ 2 ≤
        C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * σ) * U₀) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  have hG0 : (fun τ x => F₁ τ x - F₂ τ x) 0 = (fun _ => (0 : ℝ)) := by
    funext x
    show F₁ 0 x - F₂ 0 x = 0
    rw [hF0]; ring
  have hd2 := h2 ν₀ L γ M ν₁ μ₁ V b₁ hL2 (sa12x5_perData_mono hPD₁) hR₁ t ht
    (sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂) (fun τ x => F₁ τ x - F₂ τ x) hGm hSs hG0 Hf hHf0
    hHfc.integrableOn_Icc hsrc τ hτ
  -- the integral
  have hτ0 : 0 ≤ τ := hτ.1
  have hint : ∫ σ in Icc (0 : ℝ) τ, Hf σ ≤
      (C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * τ) * U₀) ^ 2) * τ := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) τ)
      (C := C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * τ) * U₀) ^ 2) measure_Icc_lt_top (f := Hf)
      (fun σ hσ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hHf0 σ ⟨hσ.1, hσ.2.trans hτ.2⟩)]
        rw [hHf]
        have h1 : Real.exp (C15 * k * σ) ≤ Real.exp (C15 * k * τ) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2 (by positivity))
        have h2 : C15 * Real.exp (C15 * k * σ) * U₀ ≤ C15 * Real.exp (C15 * k * τ) * U₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC15.le) hU00
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) (by positivity))
    have := (le_abs_self _).trans (by simpa using hb)
    simpa [Measure.real, Real.volume_Icc, hτ0, mul_comm] using this
  -- combine
  have hlam2 : Rg.lambdaM C2 ν₀ (PDE.thetaOrder d s) = C2 * k := hklam C2
  rw [hlam2] at hd2
  set q : ℝ := C * τ * Real.exp (C * k * τ) * Δ * U₀ with hq
  have hq0 : 0 ≤ q := by positivity
  have hZ : C2 * Real.exp (2 * (C2 * k) * τ) * τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ ≤ q ^ 2 := by
    have h1 : C2 * Real.exp (2 * (C2 * k) * τ) * τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ ≤
        C2 * Real.exp (2 * (C2 * k) * τ) * τ *
          ((C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * τ) * U₀) ^ 2) * τ) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    refine h1.trans ?_
    have hex : Real.exp (2 * (C2 * k) * τ) * Real.exp (C15 * k * τ) ^ 2 ≤ Real.exp (C * k * τ) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      have : (C2 + C15) * k * τ ≤ C * k * τ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hk0) hτ0
      nlinarith [this, mul_nonneg hC2.le (mul_nonneg hk0 hτ0), mul_nonneg hC15.le (mul_nonneg hk0 hτ0)]
    have hcc : C2 * C3 * C15 ^ 2 ≤ C ^ 2 := by nlinarith
    have e : C2 * Real.exp (2 * (C2 * k) * τ) * τ *
          ((C3 * Δ ^ 2 * (C15 * Real.exp (C15 * k * τ) * U₀) ^ 2) * τ) =
        (C2 * C3 * C15 ^ 2) * (Real.exp (2 * (C2 * k) * τ) * Real.exp (C15 * k * τ) ^ 2) *
          (τ ^ 2 * Δ ^ 2 * U₀ ^ 2) := by ring
    rw [e, hq]
    have e2 : (C * τ * Real.exp (C * k * τ) * Δ * U₀) ^ 2 =
        C ^ 2 * Real.exp (C * k * τ) ^ 2 * (τ ^ 2 * Δ ^ 2 * U₀ ^ 2) := by ring
    rw [e2]
    have hr : 0 ≤ τ ^ 2 * Δ ^ 2 * U₀ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hr
    exact mul_le_mul hcc hex (by positivity) (by positivity)
  have hsq : (ulocNormE m χ (fun x => F₁ τ x - F₂ τ x)) ^ 2 ≤ ENNReal.ofReal q ^ 2 := by
    rw [← ENNReal.ofReal_pow hq0]
    exact hd2.trans (ENNReal.ofReal_le_ofReal hZ)
  have hle : ulocNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤ ENNReal.ofReal q :=
    by
      by_contra hcon
      exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hcon)))
  rw [hklam C, hUfin, ← ENNReal.ofReal_mul (by positivity)]
  refine hle.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  first | rfl | ring | (rw [hq]; ring) | (simp only [hq, hΔ]; ring)

end HRS.MH.AdjointRd.Phase2SA12X5
