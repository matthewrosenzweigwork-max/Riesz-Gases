import HRS.MS.SA12X3N1L

/-!
# S.A.12 N2 (SA12X3): locally uniform convergence of the boxed periodic nonlocal test term to `nonlocalTestRd`
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriConv
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3n_N2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∀ (R δ : ℝ), 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
        |(centeredBox d L).indicator (nonlocalTestPer L (γ L) D.M (μL L ε σ) ψ) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x| ≤ δ := by
  intro R δ hδ
  obtain ⟨hDs, -, -⟩ := hD.hs
  obtain ⟨L₁, Kc, hL₁, hKc, -, hP2⟩ := sa12x3n_nl_bounds hd s hs0 hsd hψ.1 hψ.2 D.M
  obtain ⟨L₂, Kq, hL₂, hKq, hdiff⟩ := hP2 R
  set Λρ : ℝ := 2 * max Λ 0 with hΛρ
  have hΛρ0 : 0 ≤ Λρ := by positivity
  set δ' : ℝ := δ / (4 * (Kc + 1)) with hδ'
  have hδ'pos : 0 < δ' := by positivity
  obtain ⟨L₁a, ε₀a, hε₀a, ha⟩ := hA.2 (Metric.closedBall (0 : Euc d) R) (isCompact_closedBall _ _) 0
    (by omega) δ' hδ'pos
  obtain ⟨L₁b, ε₀b, hε₀b, hb⟩ := hA.2 (Metric.closedBall (0 : Euc d) R) (isCompact_closedBall _ _) 1
    (by omega) δ' hδ'pos
  refine ⟨max (max (max L₁a L₁b) (max L₂ (max 1 L₀))) (max (2 * R + 1) (2 * Kq * Λρ / δ + 1)),
    min (min ε₀a ε₀b) 1, lt_min (lt_min hε₀a hε₀b) one_pos, fun L hL ε hε hεle σ hσ x hx => ?_⟩
  have hLa : L₁a ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLb : L₁b ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLc : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hL1 : max 1 L₀ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLR : 2 * R + 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLK : 2 * Kq * Λρ / δ + 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL0 : 0 < L := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hL1)
  have hεa : ε ≤ ε₀a := hεle.trans (((min_le_left _ _).trans (min_le_left _ _)))
  have hεb : ε ≤ ε₀b := hεle.trans (((min_le_left _ _).trans (min_le_right _ _)))
  have hεI : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε, hεle.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans ht.2⟩
  have hrT : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hmax : max (t - σ) 0 = t - σ := max_eq_left (by linarith [hσ.2])
  have hxK : x ∈ Metric.closedBall (0 : Euc d) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx
  have hxbox : x ∈ centeredBox d L := by
    intro i
    have h1 : |x i| ≤ R := by
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      linarith
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  rw [indicator_of_mem hxbox]
  have hPD := hA.1 L hL1 ε hεI
  have hμ1 : ContDiff ℝ 1 (μL L ε σ) := (hPD.μ_smooth σ hσT).of_le (by simp)
  obtain ⟨hρsm, hρjet⟩ := sa12x3n_regMF_jets hD.hμ.regular hrT
  have hμ2 : ContDiff ℝ 1 (μ (t - σ)) := hρsm.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hRd : nonlocalTestRd (D.coeff μ) (t - σ) ψ x = ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      partialDeriv (fun _ : Fin 1 => j) (fun y => μ (t - σ) y *
        gradient (HRS.Whole.convFun (rieszKernel d s) ψ) y i) x := by
    show ∑ i : Fin d, ∑ j : Fin d, D.M j i * partialDeriv (fun _ : Fin 1 => j) (fun y => μ (t - σ) y *
      gradient (HRS.Whole.convFun (rieszKernel d D.s) ψ) y i) x = _
    rw [hDs]
  rw [hRd]
  have h2 := hdiff L hLc (γ L) hPD.hγ (μL L ε σ) (μ (t - σ)) hμ1 hμ2 x hx
  have e0 := (ha L hLa ε hε hεa σ hσT x hxK).2
  have e1 := (hb L hLb ε hε hεb σ hσT x hxK).2
  rw [hmax, tcv_iter_zero_sub_norm, Real.norm_eq_abs] at e0
  rw [hmax, sa12x3n_norm_one_sub] at e1
  have j0 : |μ (t - σ) x| ≤ max Λ 0 := by
    have := hρjet 0 (by omega) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have j1 : ‖fderiv ℝ (μ (t - σ)) x‖ ≤ max Λ 0 := by
    have := hρjet 1 (by omega) x
    rwa [norm_iteratedFDeriv_one] at this
  refine h2.trans ?_
  have hA1 : Kc * (‖fderiv ℝ (μL L ε σ) x - fderiv ℝ (μ (t - σ)) x‖ + |μL L ε σ x - μ (t - σ) x|) ≤ δ / 2 := by
    calc _ ≤ Kc * (δ' + δ') := mul_le_mul_of_nonneg_left (add_le_add e1 e0) hKc
      _ = δ / 2 * (2 * Kc / (2 * (Kc + 1))) := by rw [hδ']; field_simp; ring
      _ ≤ δ / 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = δ / 2 := mul_one _
  have hA2 : Kq / L * (‖fderiv ℝ (μ (t - σ)) x‖ + |μ (t - σ) x|) ≤ δ / 2 := by
    have h3 : ‖fderiv ℝ (μ (t - σ)) x‖ + |μ (t - σ) x| ≤ Λρ := by rw [hΛρ]; linarith
    have h4 : 2 * Kq * Λρ / δ ≤ L := by linarith
    rw [div_le_iff₀ hδ] at h4
    calc Kq / L * (‖fderiv ℝ (μ (t - σ)) x‖ + |μ (t - σ) x|) ≤ Kq / L * Λρ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Kq * Λρ / L := by ring
      _ ≤ δ / 2 := by
          rw [div_le_iff₀ hL0]; nlinarith
  linarith

end HRS.MH.AdjointRd.Phase2SA12Limit
