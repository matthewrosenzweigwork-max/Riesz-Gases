import HRS.MS.SA12X3P2
import HRS.MS.SA12X4V4
import HRS.MS.SA12CompB11

/-!
# S.A.12 B6 (SA12X4): the weighted periodic approximation sequence (copy of P2 with the varpi bound added)

The periodic approximation sequence: `L_n = max (max 1 L₀) L₁ + n + 1`, `ε_n = 1/(n+1)`, the data of C1 (`sa12k_periodic_coefficients_time`),
the initial data `periodicDatum ζ η L_n ε_n φ` (C2), the smooth solution `F_n` of C5 at level `max m 2`, the energy bound C15, the
weak identity C17, the operator estimates L8/L7, and the scalar equicontinuity (uniform for `L_n ≥ Lmin(ψ)`, per `n` by `sa12x3p_lip` before).
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4Seq

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Assembly

variable {d : ℕ}

theorem sa12x4_weighted_sequence_aux (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s<d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0<C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE m χ φ<⊤ →
        ∃ a : ApproximationSequence (d := d) χ m (D.coeff μ) t φ (rdProfile Rg C ν₀ s m χ φ),
          ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (a.F n τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ φ := by
  obtain ⟨ζ, hζ⟩ := sa12x3p_zeta (d := d)
  obtain ⟨η, hη⟩ := sa12x3p_eta (d := d)
  obtain ⟨γ, hγ⟩ := sa12x3p_gamma hd hs0 hsd
  obtain ⟨Λ', ΛV', Cb, L₀, hC1⟩ := sa12k_periodic_coefficients_time hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T ζ hζ
  obtain ⟨C2, hC2, hinit⟩ := HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_periodic_initial_bounds hd m χ ζ η hχ hζ hη
  obtain ⟨C15, L15, hC15, h15⟩ := periodic_uloc_bound hd s hs0 hsd m hm Rg MB Λ' ΛV' νbar Cb T χ hχ
  obtain ⟨Cv, Lv, hCv, hv⟩ := HRS.MH.AdjointRd.Phase2SA12X4.sa12x4_periodic_varpi hd s hs0 hsd m hm Rg MB Λ' ΛV' νbar Cb T χ hχ
  set M0 : ℝ := max (max (C15 * C2) C15) (max (Cv * C2) Cv) with hM0
  have hM1 : C15 * C2 ≤ M0 := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : C15 ≤ M0 := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : Cv * C2 ≤ M0 := (le_max_left _ _).trans (le_max_right _ _)
  have hM4 : Cv ≤ M0 := (le_max_right _ _).trans (le_max_right _ _)
  set C : ℝ := M0 + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ M0 := hM2.trans' hC15.le
    linarith
  refine ⟨C, hCpos, fun D ν₀ μ hD hR t ht φ hφ => ?_⟩
  obtain ⟨μL, VL, hApp, hTime⟩ := hC1 D μ hD γ hγ t ht
  have hT0 : 0 ≤ T := ht.1.le.trans ht.2
  have htT : t ≤ T := ht.2
  set Lb : ℝ := max (max (max 1 L₀) L15) Lv with hLb
  set Ln : ℕ → ℝ := fun n => Lb + n + 1 with hLn
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hLn1 : ∀ n, max 1 L₀ ≤ Ln n := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hLn, hLb]; linarith [le_max_left (max 1 L₀) L15, le_max_left (max (max 1 L₀) L15) Lv]
  have hLn15 : ∀ n, L15 ≤ Ln n := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hLn, hLb]; linarith [le_max_right (max 1 L₀) L15, le_max_left 1 L₀, le_max_left (max (max 1 L₀) L15) Lv]
  have hLnv : ∀ n, Lv ≤ Ln n := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hLn, hLb]; linarith [le_max_right (max (max 1 L₀) L15) Lv, le_max_left 1 L₀,
      (le_max_left 1 L₀).trans ((le_max_left (max 1 L₀) L15).trans (le_max_left (max (max 1 L₀) L15) Lv))]
  have hLnge1 : ∀ n, 1 ≤ Ln n := fun n => (le_max_left 1 L₀).trans (hLn1 n)
  have hεnI : ∀ n, εn n ∈ Ioc (0 : ℝ) 1 := fun n => by
    have : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine ⟨by simp only [hεn]; positivity, ?_⟩
    simp only [hεn]
    rw [div_le_one (by linarith)]; exact this
  set U : ℝ := (ulocNormE m χ φ).toReal with hU
  have hUfin : ulocNormE m χ φ = ENNReal.ofReal U := (ENNReal.ofReal_toReal hφ.ne).symm
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  -- the periodic initial data
  set dat : ℕ → Euc d → ℝ := fun n => periodicDatum ζ η (Ln n) (εn n) φ with hdat
  have hi := (hinit φ hφ)
  have hdat_reg : ∀ n, BddJets m (dat n) ∧ (∀ (x : Euc d) (k : Fin d → ℤ), dat n (x + Ln n • latticePt k) = dat n x) ∧
      ulocNormE m χ (dat n) ≤ ENNReal.ofReal C2 * ulocNormE m χ φ := fun n => by
    obtain ⟨h1, h2, h3, -⟩ := hi.1 (Ln n) (εn n) (hLnge1 n) (hεnI n).1
    exact ⟨h1, h2, h3⟩
  -- the smooth solutions
  set bn : ℕ → ℝ → Euc d → Euc d := fun n τ =>
    torusDriftL D.M (Ln n) (γ (Ln n)) (μL (Ln n) (εn n) τ) (VL (Ln n) (εn n)) with hbn
  have hPD : ∀ n, PerData s m MB Λ' ΛV' νbar Cb T (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n))
      (VL (Ln n) (εn n)) (bn n) := fun n => hApp.1 (Ln n) (hLn1 n) (εn n) (hεnI n)
  have hex : ∀ n, ∃ F : ℝ → Euc d → ℝ, IsPerSol (max m 2) (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n))
      (bn n) (fun _ _ => 0) t F ∧ F 0 = dat n := fun n =>
    periodic_smooth_solution hd s hs0 hsd Rg (max m 2) T (Ln n) (γ (Ln n)) D.M D.invβ ν₀ (μL (Ln n) (εn n))
      (VL (Ln n) (εn n)) (bn n) (hPD n).toPerSmooth (hTime (Ln n) (hLn1 n) (εn n) (hεnI n)) hR t ht (dat n)
      (hdat_reg n).1.1 (hdat_reg n).2.1
  choose Fs hFs using hex
  have hsol : ∀ n, IsPerSol m (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n) (fun _ _ => 0) t (Fs n) :=
    fun n => sa12x3p_isPerSol_mono (le_max_left m 2) (hFs n).1
  have hsol2 : ∀ n, IsPerSol 2 (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n) (fun _ _ => 0) t (Fs n) :=
    fun n => sa12x3p_isPerSol_mono (le_max_right m 2) (hFs n).1
  -- the profile
  have hlam : Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by
    have hCC : C15 ≤ C := by
      linarith
    have := sa12x3_lam_ge hR hCC (PDE.thetaOrder d s)
    linarith
  have hprof : ∀ τ, rdProfile Rg C ν₀ s m χ φ τ = C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * U :=
    fun τ => rfl
  have hbound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t,
      ulocNormE m χ (Fs n τ) ≤ ENNReal.ofReal (rdProfile Rg C ν₀ s m χ φ τ) := by
    intro n τ hτ
    have h1 := h15 ν₀ (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (VL (Ln n) (εn n)) (bn n) (hLn15 n)
      (hPD n) hR t ht (Fs n) (hsol n) τ hτ
    rw [(hFs n).2] at h1
    have h2 : ulocNormE m χ (dat n) ≤ ENNReal.ofReal C2 * ENNReal.ofReal U := by
      rw [← hUfin]; exact (hdat_reg n).2.2
    calc ulocNormE m χ (Fs n τ) ≤ ENNReal.ofReal (C15 * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ)) *
          ulocNormE m χ (dat n) := h1
      _ ≤ ENNReal.ofReal (C15 * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ)) *
          (ENNReal.ofReal C2 * ENNReal.ofReal U) := by gcongr
      _ = ENNReal.ofReal (C15 * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ) * (C2 * U)) := by
          rw [← ENNReal.ofReal_mul hC2.le, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (rdProfile Rg C ν₀ s m χ φ τ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hprof]
          have hexp : Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ) ≤
              Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hlam hτ.1)
          have hCC2 : C15 * C2 ≤ C := by
            linarith
          have e0 := Real.exp_pos (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ)
          calc C15 * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ) * (C2 * U)
              = (C15 * C2) * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ) * U := by ring
            _ ≤ C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * U := by
                refine mul_le_mul_of_nonneg_right ?_ hU0
                exact mul_le_mul hCC2 hexp e0.le hCpos.le
  set Bd : ℝ := C * Real.exp (|Rg.lambdaM C ν₀ (PDE.thetaOrder d s)| * t) * U with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hprofB : ∀ τ ∈ Icc (0 : ℝ) t, rdProfile Rg C ν₀ s m χ φ τ ≤ Bd := by
    intro τ hτ
    rw [hprof]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCpos.le) hU0
    calc Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ ≤ |Rg.lambdaM C ν₀ (PDE.thetaOrder d s)| * τ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
  have hweak : ∀ n, IsWeakSol (weakOpPer (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n)) t (dat n) (Fs n) :=
    fun n => by
      have := periodic_weak_identity hd s hs0 hsd T (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n))
        (VL (Ln n) (εn n)) (bn n) (hPD n).toPerSmooth (hTime (Ln n) (hLn1 n) (εn n) (hεnI n)) t ht (Fs n) (hsol2 n)
      rwa [(hFs n).2] at this
  have hmeasn : ∀ n, ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      AEStronglyMeasurable (weakOpPer (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n) σ ψ) volume := by
    intro n ψ hψ σ hσ
    have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans htT⟩
    exact sa12x3p_weakOpPer_aesm (hγ (Ln n) (hLnge1 n)).locInt
      ((hPD n).μ_smooth σ hσT |>.of_le (by simp))
      (((hPD n).b_drift.smooth σ hσT).of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))) hψ
  -- the weak-operator estimates (L8)
  have hL8 : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ Lmin : ℝ, max 1 L₀ ≤ Lmin ∧
      (∃ K : ℝ, ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
        cellL2Sum (weakOpPer L (γ L) D.M D.invβ (μL L ε)
          (fun τ => torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ) ≤ ENNReal.ofReal K) ∧
      ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ σ ∈ Icc (0 : ℝ) t,
        cellL2Sum (fun x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
          (fun τ => torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x -
            weakOp (D.coeff μ) t σ ψ x) ≤ ENNReal.ofReal δ := fun ψ hψ =>
    sa12x3_weak_operator_convergence hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht γ μL VL
      hApp ψ hψ
  -- large `n`
  have hLge : ∀ (a : ℝ), ∃ N : ℕ, ∀ n ≥ N, a ≤ Ln n := fun a => by
    refine ⟨⌈a⌉₊, fun n hn => ?_⟩
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ Lb := (le_max_left 1 L₀).trans ((le_max_left _ _).trans (le_max_left _ _))
    simp only [hLn]; linarith
  have hεge : ∀ (e : ℝ), 0 < e → ∃ N : ℕ, ∀ n ≥ N, εn n ≤ e := fun e he => by
    refine ⟨⌈1 / e⌉₊, fun n hn => ?_⟩
    have h1 : 1 / e ≤ (⌈1 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / e⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hεn]
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ e * (n + 1) := by
      have := (div_le_iff₀ he).1 (h1.trans h2 |>.trans (by linarith : (n : ℝ) ≤ n + 1))
      linarith
    linarith
  have hvarpi : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (Fs n τ) ≤
      ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ φ := by
    intro n τ hτ
    have h1 := hv ν₀ (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (VL (Ln n) (εn n)) (bn n) (hLnv n)
      (hPD n) hR t ht (Fs n) (hsol n) τ hτ
    rw [(hFs n).2] at h1
    have h4 : varpiNormE m χ (dat n) ≤ ENNReal.ofReal C2 * varpiNormE m χ φ := by
      obtain ⟨-, -, -, h4⟩ := hi.1 (Ln n) (εn n) (hLnge1 n) (hεnI n).1
      exact h4
    have hCvC : Cv ≤ C := by rw [hCdef]; linarith
    have hlamv : Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by
      have := sa12x3_lam_ge hR hCvC (PDE.thetaOrder d s)
      linarith
    have hexp : Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ) ≤
        Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hlamv hτ.1)
    have hCC3 : Cv * C2 ≤ C := by rw [hCdef]; linarith
    calc varpiNormE m χ (Fs n τ)
        ≤ ENNReal.ofReal (Cv * Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ (dat n) := h1
      _ ≤ ENNReal.ofReal (Cv * Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ)) *
            (ENNReal.ofReal C2 * varpiNormE m χ φ) := by gcongr
      _ = ENNReal.ofReal (Cv * Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ) * C2) * varpiNormE m χ φ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ φ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have e0 := Real.exp_pos (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ)
          calc Cv * Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ) * C2
              = (Cv * C2) * Real.exp (Rg.lambdaM Cv ν₀ (PDE.thetaOrder d s) * τ) := by ring
            _ ≤ C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) :=
                mul_le_mul hCC3 hexp e0.le hCpos.le
  refine ⟨⟨Fs, dat, (fun n => weakOpPer (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n)), Bd, hBd0,
    hprofB, hbound, hweak, ?_, ?_, ?_, ?_, ?_⟩, hvarpi⟩
  · -- equicontinuity
    intro ψ hψ
    obtain ⟨Lmin, -, ⟨K0, hK0⟩, -⟩ := hL8 ψ hψ
    choose Kn hKn using fun n => sa12x3p_lip (m := m) (Nat.zero_le m) (hPD n).b_drift (hsol n).sol htT hψ
    set c : ℝ := max K0 0 with hc
    have hc0 : 0 ≤ c := le_max_right _ _
    have hF0 : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fs n τ) ≤ ENNReal.ofReal Bd := fun n τ hτ =>
      (HRS.MS.SA12BD.sa12_uloc_mono d m 0 (Nat.zero_le m) χ _).trans
        ((hbound n τ hτ).trans (ENNReal.ofReal_le_ofReal (hprofB τ hτ)))
    refine ⟨max (Bd * c) (∑ n ∈ Finset.range ⌈Lmin⌉₊, |Kn n|), fun n τ hτ σ hσ => ?_⟩
    by_cases hn : Lmin ≤ Ln n
    · have := sa12x3p_time_pair hd χ hχ (hweak n) hBd0 (hF0 n) hψ hc0 (fun σ' hσ' => hmeasn n ψ hψ σ' hσ')
        (fun σ' hσ' => (hK0 (Ln n) hn (εn n) (hεnI n) σ' hσ').trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        hτ hσ
      refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · push Not at hn
      have hnN : n < ⌈Lmin⌉₊ := by
        rw [Nat.lt_ceil]
        have : (n : ℝ) ≤ Ln n := by
          simp only [hLn]
          have h3 : (1 : ℝ) ≤ Lb := (le_max_left 1 L₀).trans ((le_max_left _ _).trans (le_max_left _ _))
          linarith
        linarith
      have h1 := hKn n τ hτ σ hσ
      have h2 : |Kn n| ≤ ∑ n ∈ Finset.range ⌈Lmin⌉₊, |Kn n| :=
        Finset.single_le_sum (f := fun n => |Kn n|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hnN)
      calc _ ≤ Kn n * |τ - σ| := h1
        _ ≤ |Kn n| * |τ - σ| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
        _ ≤ (∑ n ∈ Finset.range ⌈Lmin⌉₊, |Kn n|) * |τ - σ| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  · -- initial data
    intro ψ hψ
    refine Metric.tendsto_atTop.2 fun δ hδ => ?_
    obtain ⟨L1, ε0, hε0, h⟩ := hi.2 ψ hψ (δ / 2) (half_pos hδ)
    obtain ⟨N1, hN1⟩ := hLge L1
    obtain ⟨N2, hN2⟩ := hεge ε0 hε0
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have := h (Ln n) (max_le (hLnge1 n) (hN1 n ((le_max_left _ _).trans hn))) (εn n) (hεnI n).1
      (hN2 n ((le_max_right _ _).trans hn))
    rw [Real.dist_eq]
    exact lt_of_le_of_lt this (half_lt_self hδ)
  · -- measurability
    intro ψ hψ σ hσ
    exact ⟨(sa12y_weakOp_cont hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD t ht σ hσ ψ hψ).aestronglyMeasurable,
      fun n => hmeasn n ψ hψ σ hσ⟩
  · -- operator convergence
    intro ψ hψ δ hδ
    obtain ⟨-, -, -, hconv⟩ := hL8 ψ hψ
    obtain ⟨L1, ε0, hε0, h⟩ := hconv δ hδ
    obtain ⟨N1, hN1⟩ := hLge L1
    obtain ⟨N2, hN2⟩ := hεge ε0 hε0
    refine Filter.eventually_atTop.2 ⟨max N1 N2, fun n hn σ hσ => ?_⟩
    exact h (Ln n) (hN1 n ((le_max_left _ _).trans hn)) (εn n) (hεnI n).1 (hN2 n ((le_max_right _ _).trans hn)) σ hσ
  · intro ψ hψ
    exact sa12x3p_op_bound hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD t ht hψ

theorem sa12x4_weighted_sequence :
    HRS.MH.AdjointRd.Phase2SA12Companions.WeightedApproxSeqStatement :=
  fun {d} hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ =>
    sa12x4_weighted_sequence_aux d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ

end HRS.MH.AdjointRd.Phase2SA12X4Seq
