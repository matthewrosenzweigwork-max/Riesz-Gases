import HRS.MS.SA12X5G1
import HRS.MS.SA12X5G0
import HRS.MS.SA12X5D2W
import HRS.MS.SA12X5D5
import HRS.MS.SA12X5D5E
import HRS.MS.SA12X5F1
import HRS.MS.SA12X5P0
import HRS.MS.SA12X4V3
import HRS.MS.QMul
import HRS.MS.SA12X3C15E
import HRS.MS.SA12X3C15K
import HRS.MS.SA12X3P2A
import HRS.MS.SA12Z3NearN7E

/-!
# S.A.12 X5 G2: the weighted difference bound for two periodic solutions

`varpiNormE m (F₁ τ - F₂ τ) ≤ C τ e^{Λτ} (|ν₁-ν₂| + A) varpiNormE (m+2) (F₁ 0)`: the difference solves the periodic
problem with the source `sa12x5_src` (D5), whose weighted cell energy is bounded by G1 and G0 in terms of the weighted
norm of `F₂ σ`, which grows at most like `e^{Λσ}` (V4); then the weighted source-energy bound D2w.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12X4
  HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Assembly

variable {d : ℕ}

theorem sa12x5_varpi_zero (m : ℕ) (χ : Euc d → ℝ) : varpiNormE m χ (fun _ => (0 : ℝ)) = 0 := by
  unfold varpiNormE
  simp only [mul_zero]
  simp [HRS.MS.QMul.qm_sobE_zero]

/-- The sqrt step. -/
theorem sa12x5_sq_le_sqrt {X : ℝ≥0∞} {R : ℝ} (hR : 0 ≤ R) (h : X ^ 2 ≤ ENNReal.ofReal (R ^ 2)) :
    X ≤ ENNReal.ofReal R := by
  calc X = (X ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ (ENNReal.ofReal (R ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal R := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hR]

/-- The real arithmetic of the final constant. -/
theorem sa12x5_G2_real {CD Cv c0 k Δ V τ : ℝ} (hCD : 0 < CD) (hCv : 0 < Cv) (hc0 : 0 ≤ c0) (hk : 1 ≤ k)
    (hΔ : 0 ≤ Δ) (hV : 0 ≤ V) (hτ : 0 ≤ τ) :
    Real.sqrt (CD * c0) * Cv * τ * Real.exp ((CD + Cv) * k * τ) * Δ * V ≤
      (CD + Cv + Real.sqrt (CD * c0) * Cv + 1) * τ *
        Real.exp ((CD + Cv + Real.sqrt (CD * c0) * Cv + 1) * k * τ) * Δ * V := by
  set sq := Real.sqrt (CD * c0) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hexp : Real.exp ((CD + Cv) * k * τ) ≤ Real.exp ((CD + Cv + sq * Cv + 1) * k * τ) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ (sq * Cv + 1) * k * τ := by positivity
    nlinarith
  have hE0 : 0 < Real.exp ((CD + Cv) * k * τ) := Real.exp_pos _
  have h1 : sq * Cv ≤ CD + Cv + sq * Cv + 1 := by linarith
  have hA : 0 ≤ τ * Δ * V := by positivity
  calc sq * Cv * τ * Real.exp ((CD + Cv) * k * τ) * Δ * V
      = (sq * Cv) * Real.exp ((CD + Cv) * k * τ) * (τ * Δ * V) := by ring
    _ ≤ (CD + Cv + sq * Cv + 1) * Real.exp ((CD + Cv + sq * Cv + 1) * k * τ) * (τ * Δ * V) := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact mul_le_mul h1 hexp hE0.le (by positivity)
    _ = _ := by ring

theorem sa12x5_periodic_diff_varpi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν₁ ν₂ : ℝ)
      (μ₁ μ₂ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b₁ b₂ : ℝ → Euc d → Euc d) (A : ℝ), 0 ≤ A → L₁ ≤ L →
      PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₁ μ₁ V b₁ →
      PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₂ μ₂ V b₂ →
      RdRegimeHolds Rg d s M ν₁ ν₀ → RdRegimeHolds Rg d s M ν₂ ν₀ →
      PeriodicTimeSmooth T μ₁ → PeriodicTimeSmooth T μ₂ → ∀ t ∈ Ioc (0 : ℝ) T,
      (∀ τ ∈ Icc (0 : ℝ) T,
        (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun x => μ₁ τ x - μ₂ τ x) y‖ ≤ A) ∧
        (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ, jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
          ‖iteratedFDeriv ℝ j (fun x => μ₁ τ x - μ₂ τ x) x‖ ≤ A) ∧
        (∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j (fun x => b₁ τ x - b₂ τ x) y‖ ≤ A)) →
      ∀ F₁ F₂ : ℝ → Euc d → ℝ, IsPerSol (m + 2) L γ M ν₁ μ₁ b₁ (fun _ _ => 0) t F₁ →
        IsPerSol (m + 2) L γ M ν₂ μ₂ b₂ (fun _ _ => 0) t F₂ → F₁ 0 = F₂ 0 →
        ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * (|ν₁ - ν₂| + A)) *
            varpiNormE (m + 2) χ (F₁ 0) := by
  classical
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨C1, L1, hC10, hG1⟩ := sa12x5_source_weighted_bound hd hs0 hsd m hm MB Cb T χ χh hχ hχp E hE
  obtain ⟨CD, LD, hCD, hD⟩ := sa12x5_periodic_source_varpi hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨Cv, Lv, hCv, hV⟩ := sa12x4_periodic_varpi hd s hs0 hsd (m + 2) (by omega) Rg MB Λ ΛV νbar Cb T χ hχ
  obtain ⟨KW, hKW0, hKW⟩ := sa12x5_W_le_J hd m χ hχ (m + 2) Cb T
  obtain ⟨KB, hKB0, hKB⟩ := sa12x4_J_le_varpi hd (m + 2) χ hχ
  set c0 : ℝ := C1 * KW * KB with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  set Cfin : ℝ := CD + Cv + Real.sqrt (CD * c0) * Cv + 1 with hCfin
  have hCfin0 : 0 < Cfin := by
    have := Real.sqrt_nonneg (CD * c0)
    positivity
  refine ⟨Cfin, max (max L1 LD) Lv, hCfin0, ?_⟩
  intro ν₀ L γ M ν₁ ν₂ μ₁ μ₂ V b₁ b₂ A hA0 hL hP₁ hP₂ hR₁ hR₂ hT₁ hT₂ t ht hjet F₁ F₂ h₁ h₂ h0 τ hτ
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLD : LD ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLv : Lv ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP₁.hL
  have hsub : ∀ σ ∈ Icc (0 : ℝ) t, σ ∈ Icc (0 : ℝ) T := fun σ hσ => ⟨hσ.1, hσ.2.trans ht.2⟩
  have hP₁s : PerSmooth s T L γ M ν₁ μ₁ V b₁ := hP₁.toPerSmooth
  have hP₂s : PerSmooth s T L γ M ν₂ μ₂ V b₂ := hP₂.toPerSmooth
  set Δ : ℝ := |ν₁ - ν₂| + A with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  obtain ⟨k, hk1, hklam⟩ := sa12x3_lam_lin hR₁ (PDE.thetaOrder d s)
  have hb₁ : IsAdvectingDrift m Cb T b₁ := sa12x5_advDrift_mono (sa12x5_advDrift_mono hP₁.b_drift)
  have hP₁m := sa12x5_perData_mono hP₁
  have hγloc : LocallyIntegrable γ volume := hP₁.hγ.locInt
  have hγper : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x := hP₁.hγ.periodic
  -- the difference solves the periodic problem with the source
  have hGsol := sa12x3p_isPerSol_mono (show m ≤ m + 2 by omega)
    (sa12x5_diff_isPerSol hd hs0 hsd hP₁s hP₂s hT₁ hT₂ ⟨ht.1.le, ht.2⟩ h₁ h₂)
  have hG0 : (fun τ x => F₁ τ x - F₂ τ x) 0 = (fun _ => (0 : ℝ)) := by
    funext x; exact sub_eq_zero.2 (congrFun h0 x)
  have hF₂s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (F₂ σ) := fun σ hσ => (h₂.bdd σ hσ).1
  have hμ₁s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (μ₁ σ) := fun σ hσ => hP₁s.μ_smooth σ (hsub σ hσ)
  have hμ₂s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (μ₂ σ) := fun σ hσ => hP₂s.μ_smooth σ (hsub σ hσ)
  have hb₁s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (b₁ σ) := fun σ hσ =>
    sa12x5_drift_smooth hd hs0 hsd hP₁s hT₁ ht.2 hσ
  have hb₂s : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (b₂ σ) := fun σ hσ =>
    sa12x5_drift_smooth hd hs0 hsd hP₂s hT₂ ht.2 hσ
  have hNL : ∀ (σ : ℝ), σ ∈ Icc (0 : ℝ) t → ∀ (μ : Euc d → ℝ), ContDiff ℝ ∞ μ →
      (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      ContDiff ℝ ∞ (fun x => perNonlocal L γ M μ (F₂ σ) x) := fun σ hσ μ hμ hμp =>
    sa12x5_perNonlocal_smooth hL0 hγloc hγper M hμ (hF₂s σ hσ) hμp (h₂.periodic σ hσ)
  set Sc : ℝ → Euc d → ℝ := sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ with hSc
  have hSsm : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Sc σ) := by
    intro σ hσ
    obtain ⟨hs1, hs2⟩ := sa12x5_g1_source_smooth (hF₂s σ hσ) ((hb₁s σ hσ).sub (hb₂s σ hσ)) (ν₁ - ν₂)
    have := hs1.add hs2 |>.sub ((hNL σ hσ (μ₁ σ) (hμ₁s σ hσ) (hP₁s.μ_periodic σ (hsub σ hσ))).sub
      (hNL σ hσ (μ₂ σ) (hμ₂s σ hσ) (hP₂s.μ_periodic σ (hsub σ hσ))))
    exact this
  -- the weighted cell energy of the source
  have hsrc : ∀ σ ∈ Icc (0 : ℝ) t, ∀ Ψ : ℝ → Euc d → Euc d, HRS.Whole.IsNegDriftFlow T b₁ Ψ →
      ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ σ (cellPt d z) (Sc σ)) ≤
      ENNReal.ofReal (C1 * Δ ^ 2) * cellWeighted (m + 2) χ Ψ σ (F₂ σ) := by
    intro σ hσ Ψ hΨ
    have hfun : Sc σ = fun x => (ν₁ - ν₂) * Laplacian.laplacian (F₂ σ) x +
        inner ℝ ((fun x => b₁ σ x - b₂ σ x) x) (gradient (F₂ σ) x) -
          perNonlocal L γ M (fun x => μ₁ σ x - μ₂ σ x) (F₂ σ) x := by
      funext x
      simp only [hSc, sa12x5_src]
      rw [sa12x5_perNonlocal_sub_mu hL0 hγloc hγper M (hμ₁s σ hσ) (hμ₂s σ hσ) (hF₂s σ hσ)
        (hP₁s.μ_periodic σ (hsub σ hσ)) (hP₂s.μ_periodic σ (hsub σ hσ)) (h₂.periodic σ hσ) x]
    rw [hfun]
    have hbdd : BddJets m (F₂ σ) := ⟨(h₂.bdd σ hσ).1, fun j hj => (h₂.bdd σ hσ).2 j (by omega)⟩
    exact hG1 b₁ Ψ hb₁ hΨ σ (hsub σ hσ) L γ (hL1) hP₁.hγ M hP₁.hM ν₁ ν₂ (fun x => μ₁ σ x - μ₂ σ x)
      (fun x => b₁ σ x - b₂ σ x) (F₂ σ) ((hμ₁s σ hσ).sub (hμ₂s σ hσ)) (hF₂s σ hσ)
      (fun x k => by simp only [hP₁s.μ_periodic σ (hsub σ hσ), hP₂s.μ_periodic σ (hsub σ hσ)])
      (h₂.periodic σ hσ) hbdd ((hb₁s σ hσ).sub (hb₂s σ hσ))
      (by
        have := hNL σ hσ (fun x => μ₁ σ x - μ₂ σ x) ((hμ₁s σ hσ).sub (hμ₂s σ hσ))
          (fun x k => by simp only [hP₁s.μ_periodic σ (hsub σ hσ), hP₂s.μ_periodic σ (hsub σ hσ)])
        exact this) A hA0 (hjet σ (hsub σ hσ)).1 (hjet σ (hsub σ hσ)).2.1 (hjet σ (hsub σ hσ)).2.2
  -- D2w
  have key : ∀ Hf : ℝ → ℝ, (∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ Hf σ) → IntegrableOn Hf (Icc (0 : ℝ) t) →
      (∀ Ψ : ℝ → Euc d → Euc d, HRS.Whole.IsNegDriftFlow T b₁ Ψ → ∀ σ ∈ Icc (0 : ℝ) t,
        ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (cellEnergy m χ Ψ σ (cellPt d z) (Sc σ)) ≤ ENNReal.ofReal (Hf σ)) →
      varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ^ 2 ≤
        ENNReal.ofReal (CD * Real.exp (2 * (CD * k) * τ) * τ * ∫ σ in Icc (0 : ℝ) τ, Hf σ) := by
    intro Hf h1 h2 h3
    have := hD ν₀ L γ M ν₁ μ₁ V b₁ hLD hP₁m hR₁ t ht Sc (fun τ x => F₁ τ x - F₂ τ x) hGsol hSsm hG0
      Hf h1 h2 h3 τ hτ
    rwa [hklam CD] at this
  have hτT : τ ∈ Icc (0 : ℝ) T := hsub τ hτ
  by_cases hVtop : varpiNormE (m + 2) χ (F₁ 0) = ⊤
  · by_cases hpos : 0 < Cfin * τ * Real.exp (Rg.lambdaM Cfin ν₀ (PDE.thetaOrder d s) * τ) * Δ
    · rw [hVtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
      exact le_top
    · have hz : Cfin * τ * Real.exp (Rg.lambdaM Cfin ν₀ (PDE.thetaOrder d s) * τ) * Δ = 0 :=
        le_antisymm (not_lt.1 hpos) (by have := Real.exp_pos (Rg.lambdaM Cfin ν₀ (PDE.thetaOrder d s) * τ);
                                        have := hτ.1; positivity)
      have hE0 := Real.exp_pos (Rg.lambdaM Cfin ν₀ (PDE.thetaOrder d s) * τ)
      rcases mul_eq_zero.1 hz with h | h
      · have hτ0 : τ = 0 := by
          rcases mul_eq_zero.1 h with h' | h'
          · rcases mul_eq_zero.1 h' with h'' | h''
            · exact absurd h'' hCfin0.ne'
            · exact h''
          · exact absurd h' hE0.ne'
        have hfun : (fun x => F₁ τ x - F₂ τ x) = fun _ => (0 : ℝ) := by
          funext x; rw [hτ0]; exact sub_eq_zero.2 (congrFun h0 x)
        rw [hfun, sa12x5_varpi_zero]; exact bot_le
      · have hA00 : A = 0 := by
          have : |ν₁ - ν₂| = 0 ∧ A = 0 := by
            have h1 := abs_nonneg (ν₁ - ν₂)
            constructor <;> linarith
          exact this.2
        have hΔz : Δ = 0 := h
        have hk := key (fun _ => 0) (fun _ _ => le_rfl) (integrableOn_const (by simp)) (fun Ψ hΨ σ hσ => by
          refine (hsrc σ hσ Ψ hΨ).trans ?_
          rw [hΔz]; simp)
        have hk0 : varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤ ENNReal.ofReal 0 := by
          refine sa12x5_sq_le_sqrt le_rfl ?_
          refine hk.trans ?_
          simp
        exact hk0.trans (by simp)
  · -- the finite case
    set V' : ℝ := (varpiNormE (m + 2) χ (F₁ 0)).toReal with hV'
    have hVe : varpiNormE (m + 2) χ (F₁ 0) = ENNReal.ofReal V' := (ENNReal.ofReal_toReal hVtop).symm
    have hV'0 : 0 ≤ V' := ENNReal.toReal_nonneg
    set Hf : ℝ → ℝ := fun σ => c0 * Δ ^ 2 * (Cv * Real.exp (Cv * k * σ)) ^ 2 * V' ^ 2 with hHf
    have hHfc : Continuous Hf := by
      rw [hHf]; fun_prop
    have hHf0 : ∀ σ, 0 ≤ Hf σ := fun σ => by rw [hHf]; positivity
    have hsrc2 : ∀ Ψ : ℝ → Euc d → Euc d, HRS.Whole.IsNegDriftFlow T b₁ Ψ → ∀ σ ∈ Icc (0 : ℝ) t,
        ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (cellEnergy m χ Ψ σ (cellPt d z) (Sc σ)) ≤ ENNReal.ofReal (Hf σ) := by
      intro Ψ hΨ σ hσ
      have hF2 := hF₂s σ hσ
      have hint : ∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
          Integrable (fun x => (advCutoff χ Ψ σ (cellPt d z) x * partialDeriv idx (F₂ σ) x) ^ 2) :=
        fun z j idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb₁ hΨ (hsub σ hσ) (cellPt d z) hF2 idx
      have hW := hKW b₁ Ψ hb₁ hΨ σ (hsub σ hσ) hF2 hint
      have hJ := hKB hF2
      have hv := hV ν₀ L γ M ν₂ μ₂ V b₂ hLv hP₂ hR₂ t ht F₂ h₂ σ hσ
      rw [← h0, hklam Cv, hVe] at hv
      have hv2 : varpiNormE (m + 2) χ (F₂ σ) ^ 2 ≤
          ENNReal.ofReal ((Cv * Real.exp (Cv * k * σ) * V') ^ 2) := by
        calc varpiNormE (m + 2) χ (F₂ σ) ^ 2 ≤ (ENNReal.ofReal (Cv * Real.exp (Cv * k * σ)) * ENNReal.ofReal V') ^ 2 :=
              pow_le_pow_left₀ bot_le hv 2
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      calc _ ≤ ENNReal.ofReal (C1 * Δ ^ 2) * cellWeighted (m + 2) χ Ψ σ (F₂ σ) := hsrc σ hσ Ψ hΨ
        _ ≤ ENNReal.ofReal (C1 * Δ ^ 2) * (ENNReal.ofReal KW * sa12x4_J (m + 2) (F₂ σ)) := by
            gcongr
            exact hW
        _ ≤ ENNReal.ofReal (C1 * Δ ^ 2) * (ENNReal.ofReal KW * (ENNReal.ofReal KB *
              varpiNormE (m + 2) χ (F₂ σ) ^ 2)) := by gcongr
        _ ≤ ENNReal.ofReal (C1 * Δ ^ 2) * (ENNReal.ofReal KW * (ENNReal.ofReal KB *
              ENNReal.ofReal ((Cv * Real.exp (Cv * k * σ) * V') ^ 2))) := by gcongr
        _ = ENNReal.ofReal (Hf σ) := by
            rw [← ENNReal.ofReal_mul hKB0, ← ENNReal.ofReal_mul hKW0, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hHf, hc0def]; ring
    have hk2 := key Hf (fun σ _ => hHf0 σ) (hHfc.integrableOn_Icc) hsrc2
    -- the integral
    set H0 : ℝ := c0 * Δ ^ 2 * (Cv * Real.exp (Cv * k * τ)) ^ 2 * V' ^ 2 with hH0
    have hle : ∀ σ ∈ Icc (0 : ℝ) τ, Hf σ ≤ H0 := by
      intro σ hσ
      have h1 : Real.exp (Cv * k * σ) ≤ Real.exp (Cv * k * τ) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2 (by positivity))
      rw [hHf, hH0]
      have h2 : (Cv * Real.exp (Cv * k * σ)) ^ 2 ≤ (Cv * Real.exp (Cv * k * τ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h1 hCv.le) 2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    have hint : ∫ σ in Icc (0 : ℝ) τ, Hf σ ≤ τ * H0 := by
      calc ∫ σ in Icc (0 : ℝ) τ, Hf σ ≤ ∫ σ in Icc (0 : ℝ) τ, H0 :=
            setIntegral_mono_on (hHfc.integrableOn_Icc) (integrableOn_const (by simp)) measurableSet_Icc hle
        _ = τ * H0 := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le hτ.1]
            simp
    set R : ℝ := Real.sqrt (CD * c0) * Cv * τ * Real.exp ((CD + Cv) * k * τ) * Δ * V' with hR
    have hR0 : 0 ≤ R := by
      have := hτ.1
      rw [hR]; positivity
    have hRsq : CD * Real.exp (2 * (CD * k) * τ) * τ * (τ * H0) = R ^ 2 := by
      have e1 := Real.sq_sqrt (mul_nonneg hCD.le hc0)
      have e2 : Real.exp (2 * (CD * k) * τ) * Real.exp (Cv * k * τ) ^ 2 = Real.exp ((CD + Cv) * k * τ) ^ 2 := by
        rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have : R ^ 2 = Real.sqrt (CD * c0) ^ 2 * Cv ^ 2 * τ ^ 2 * Real.exp ((CD + Cv) * k * τ) ^ 2 * Δ ^ 2 * V' ^ 2 := by
        rw [hR]; ring
      rw [this, e1, ← e2, hH0]; ring
    have hX : varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤ ENNReal.ofReal R := by
      refine sa12x5_sq_le_sqrt hR0 (hk2.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [← hRsq]
      have : 0 ≤ CD * Real.exp (2 * (CD * k) * τ) * τ := by have := hτ.1; positivity
      exact mul_le_mul_of_nonneg_left hint this
    refine hX.trans ?_
    rw [hVe, hklam Cfin, ← ENNReal.ofReal_mul (by have := hτ.1; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := sa12x5_G2_real hCD hCv hc0 hk1 hΔ0 hV'0 hτ.1
    rw [hR]
    exact this

end HRS.MH.AdjointRd.Phase2SA12X5
