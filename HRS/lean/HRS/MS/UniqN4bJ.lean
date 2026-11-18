import HRS.MS.UniqN4bI
import HRS.MS.UniqN2bD

/-!
# N4b of `UniqPlan.md`: the R3 core estimate

`n4b_r3_core`: in the regime `R3` (`d - 2 < s < d`, `ν ≥ ν₀ > 0`; the viscosity is not used here) for the test function
`ψ' = ς_c^σ f` with `f ∈ C^∞` of uniform local `L²` mass `A`:
`|nMain D (ρ (t-σ)) f ψ'| ≤ δ ∫_{B̄(Ψ_σ c, 8 e^{Cb t})} |∇f|² + C A²`, for every `δ > 0`,
with `C` independent of `σ, c, f, A`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqC3 HRS.MS.UniqN2a HRS.MS.UniqN2b

variable {d : ℕ}

/-- The partial derivatives of a Lipschitz function are bounded by its Lipschitz constant. -/
theorem n4b_D1_le_lip {u : Euc d → ℝ} {Lχ : ℝ} (hL : 0 ≤ Lχ)
    (h : HRS.PDE.ToolboxRd.IsLipschitz Lχ u) (j : Fin d) (y : Euc d) : |D1 j u y| ≤ Lχ := by
  have hlip : LipschitzWith (Real.toNNReal Lχ) u := by
    refine LipschitzWith.of_dist_le_mul fun x z => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact h x z
  have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
  rw [Real.coe_toNNReal _ hL] at this
  exact (n2b_D1_le j u y).trans this

/-- The flow bundle gives the cutoff data `N4bCut`. -/
theorem n4b_cut {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hK : FlowBundle d m Cb t χ χh b Ψ K) (hχ : IsCutoffPair χ χh)
    {Lχ : ℝ} (hLχ0 : 0 ≤ Lχ)
    (hLχ : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ z : Euc d,
      HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χh Ψ τ z))
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t) (c : Euc d) :
    N4bCut d (Ψ σ c) (Real.exp (Cb * t)) K Lχ (4 * Real.exp (-(|K| * t)))
      (varsigma χ Ψ σ c) (advCutoff χh Ψ σ c) := by
  refine ⟨hK.contDiff σ hσ c, hK.range σ hσ c, hK.fderiv_le σ hσ c, hK.supp σ hσ c, ?_,
    fun y => ?_, hK.partner_supp σ hσ c, fun j y => n4b_D1_le_lip hLχ0 (hLχ σ hσ c) j y,
    fun x y hx hy => ?_⟩
  · have h1 : ContDiff ℝ 1 (fun x => Function.invFun (Ψ σ) x - c) :=
      ((hK.flow.contDiff_inv σ hσ).of_le (by exact_mod_cast (by omega : 1 ≤ _ + 1))).sub contDiff_const
    exact (hχ.2.1.of_le (by exact_mod_cast le_top)).comp h1
  · exact hK.partner_range σ hσ c y
  · refine le_trans ?_ (hK.sep σ hσ c x y hx hy)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have h1 : K * σ ≤ |K| * σ := mul_le_mul_of_nonneg_right (le_abs_self K) hσ.1
    have h2 : |K| * σ ≤ |K| * t := mul_le_mul_of_nonneg_left hσ.2 (abs_nonneg _)
    linarith

/-- **Packet N4b: the regime `R3` core estimate.**  Same hypotheses as `n2b_r2a_core`, with `RdRegimeHolds R3`
(`d - 2 < s`, `ν ≥ ν₀ > 0`; not used: the viscosity enters only in the later absorption).  For every `δ > 0` there is `C`
(depending on `δ, d, D.s, D.M, m, Cb, Λ, t, K, χ, χh, ρ`, not on `σ, c, A, f`) with
`|nMain D (ρ (t-σ)) f (ς_c^σ f)| ≤ δ ∫_{B̄(Ψ_σ c, 8 e^{Cb t})} |∇f|² + C A²`. -/
theorem n4b_r3_core (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ν₀ : ℝ)
    (hR : RdRegimeHolds PDE.Regime.R3 d D.s D.M D.invβ ν₀)
    (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ) (hcoef : CoeffHypRd D.s m Λ T ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ),
      0 ≤ A → ContDiff ℝ ∞ f → LocMass A f →
      |nMain D (ρ (t - σ)) f (fun x => varsigma χ Ψ σ c x * f x)| ≤
        δ * (∫ y in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), ‖fderiv ℝ f y‖ ^ 2) + C * A ^ 2 := by
  intro δ hδ
  have ht0 : 0 ≤ t := ht.1
  have hCb : 0 ≤ Cb := by
    have := hb.growth 0 ⟨le_rfl, ht0⟩ 0
    simp at this
    linarith [norm_nonneg (b 0 0)]
  have hL1 : 1 ≤ Real.exp (Cb * t) := Real.one_le_exp (mul_nonneg hCb ht0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK.fderiv_le 0 ⟨le_rfl, ht0⟩ 0 0)
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  obtain ⟨Lχ, hLχ0, hLχ⟩ := n2b_advCutoff_lip hK.flow hχ.2.1 hχ.2.2.1
  set δs : ℝ := 4 * Real.exp (-(|K| * t)) with hδs
  have hδs0 : 0 < δs := by positivity
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, |D.M j i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨C, hC0, hpair⟩ := n4b_pair hd hs0 hsd hL1 hK0 hLχ0 hCρ0 hδs0
    (ε := δ / (S + 1)) (by positivity)
  refine ⟨S * C, by positivity, ?_⟩
  intro σ hσ c A f hA hf hfm
  have hr : t - σ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef hr
  have hcut := n4b_cut hK hχ hLχ0 hLχ hσ c
  have hrho : N4bRho d Cρ (ρ (t - σ)) :=
    ⟨hρ1, hρ0, fun j y => (n2b_D1_le j _ y).trans (hρ1' y)⟩
  set G2 : ℝ := ∫ y in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), ‖fderiv ℝ f y‖ ^ 2 with hG2
  have hG20 : 0 ≤ G2 :=
    setIntegral_nonneg measurableSet_closedBall fun y _ => by positivity
  unfold nMain
  calc |∑ i : Fin d, ∑ j : Fin d, D.M j i *
        ∫ x, f x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i
          (fun x => varsigma χ Ψ σ c x * f x) y) x (EuclideanSpace.single j (1 : ℝ))|
      ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i| * ((δ / (S + 1)) * G2 + C * A ^ 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hpair i j (Ψ σ c) (varsigma χ Ψ σ c) (advCutoff χh Ψ σ c) (ρ (t - σ)) f A hA hcut hrho
            hf hfm) (abs_nonneg _)
    _ = S * ((δ / (S + 1)) * G2 + C * A ^ 2) := by
        rw [hS, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ ≤ δ * G2 + S * C * A ^ 2 := by
        have h1 : S * (δ / (S + 1)) ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h1 hG20]

end HRS.MS.UniqN4b
