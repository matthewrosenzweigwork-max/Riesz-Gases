import HRS.MS.SA12X3P2

/-!
# S.A.12 X5 S1: the tail of `sequence_from_cell_producers` for a GIVEN family of periodic solutions

`sa12x5_one_seq` is the second half of `sequence_from_cell_producers` (SA12X3P2) with the periodic sequence `(L_n, ε_n)`,
the constants of C1/C2/C15 and the solutions `F_n` as hypotheses; the conclusion exposes `a.F = Fs`.  It lets the
paired construction use the same `(L_n, ε_n, datum)` for two coefficient sets.
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12x5_one_seq (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (ζ η : Euc d → ℝ) (γ : ℝ → Euc d → ℝ) (hγ : ∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L))
    (Λ' ΛV' Cb L₀ : ℝ) (C2 : ℝ) (hC2 : 0 < C2)
    (hinit : ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
      (∀ L ε : ℝ, 1 ≤ L → 0 < ε →
        BddJets m (periodicDatum ζ η L ε φ) ∧
        (∀ (x : Euc d) (k : Fin d → ℤ),
          periodicDatum ζ η L ε φ (x + L • latticePt k) = periodicDatum ζ η L ε φ x) ∧
        ulocNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C2 * ulocNormE m χ φ ∧
        varpiNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C2 * varpiNormE m χ φ) ∧
      ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0 < δ →
        ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, max 1 L₁ ≤ L →
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
            |(∫ x, periodicDatum ζ η L ε φ x * ψ x) - (∫ x, φ x * ψ x)| ≤ δ)
    (C15 L15 : ℝ) (hC15 : 0 < C15)
    (h15 : ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L15 ≤ L → PerData s m MB Λ' ΛV' νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          ulocNormE m χ (F τ) ≤
            ENNReal.ofReal (C15 * Real.exp (Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) * τ)) * ulocNormE m χ (F 0))
    (C : ℝ) (hCpos : 0 < C) (hCa : C15 * C2 ≤ C) (hCb : C15 ≤ C)
    (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (hφ : ulocNormE m χ φ < ⊤)
    (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hApp : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL)
    (hTime : ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε ∈ Ioc (0 : ℝ) 1, PeriodicTimeSmooth T (μL L ε))
    (Ln εn : ℕ → ℝ) (hLn1 : ∀ n, max 1 L₀ ≤ Ln n) (hLn15 : ∀ n, L15 ≤ Ln n) (hLnge1 : ∀ n, 1 ≤ Ln n)
    (hεnI : ∀ n, εn n ∈ Ioc (0 : ℝ) 1) (hLN : ∀ n : ℕ, (n : ℝ) ≤ Ln n)
    (hLge : ∀ a : ℝ, ∃ N : ℕ, ∀ n ≥ N, a ≤ Ln n) (hεge : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, εn n ≤ e)
    (Fs : ℕ → ℝ → Euc d → ℝ)
    (hFs : ∀ n, IsPerSol (max m 2) (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n))
      (fun τ => torusDriftL D.M (Ln n) (γ (Ln n)) (μL (Ln n) (εn n) τ) (VL (Ln n) (εn n)))
      (fun _ _ => 0) t (Fs n) ∧ Fs n 0 = periodicDatum ζ η (Ln n) (εn n) φ) :
    ∃ a : ApproximationSequence (d := d) χ m (D.coeff μ) t φ (rdProfile Rg C ν₀ s m χ φ), a.F = Fs := by
  classical
  have hT0 : 0 ≤ T := ht.1.le.trans ht.2
  have htT : t ≤ T := ht.2
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
  have hsol : ∀ n, IsPerSol m (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n) (fun _ _ => 0) t (Fs n) :=
    fun n => sa12x3p_isPerSol_mono (le_max_left m 2) (hFs n).1
  have hsol2 : ∀ n, IsPerSol 2 (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n) (fun _ _ => 0) t (Fs n) :=
    fun n => sa12x3p_isPerSol_mono (le_max_right m 2) (hFs n).1
  -- the profile
  have hlam : Rg.lambdaM C15 ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C ν₀ (PDE.thetaOrder d s) := by
    have hCC : C15 ≤ C := by
      exact hCb
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
            exact hCa
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
  refine ⟨⟨Fs, dat, (fun n => weakOpPer (Ln n) (γ (Ln n)) D.M D.invβ (μL (Ln n) (εn n)) (bn n)), Bd, hBd0,
    hprofB, hbound, hweak, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
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
        have : (n : ℝ) ≤ Ln n := hLN n
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


end HRS.MH.AdjointRd.Phase2SA12Assembly
