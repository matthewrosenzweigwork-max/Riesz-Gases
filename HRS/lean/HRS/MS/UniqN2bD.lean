import HRS.MS.UniqN2bC
import HRS.MS.UniqN2aF
import HRS.MS.UniqC3e

/-!
# N2b of `UniqPlan.md`, part (d): the regime `R2a` core estimate

`n2b_r2a_core`: in the regime `R2a` (`d - 2 < s`, `symPart M = 0`), for the test function
`ψ' = ς_c^σ f` with `f ∈ C^∞` of uniform local `L²` mass `A`, `|nMain D (ρ (t-σ)) f ψ'| ≤ C A²`
with `C` independent of `σ, c, f, A`.

* by `n2b_nMain_eq` the term `ρ' ∂_j H_i` cancels (antisymmetry of `M`, symmetry of the Hessian of `ψ'`);
* `d - 1 < s < d`: `n2a_main_locmass` with `a = ∂_jρ'`;
* `d - 2 < s ≤ d - 1`: `n2b_case_low` (`kgOrder d s = 0`, `screened_local` plus far field).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqC3 HRS.MS.UniqN2a

variable {d : ℕ}

/-- The advected cutoff is Lipschitz, uniformly in `τ ∈ [0,t]` and the centre. -/
theorem n2b_advCutoff_lip {m : ℕ} {Cb t : ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hF : FlowFacts m Cb t Ψ) {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ Lχ : ℝ, 0 ≤ Lχ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ z : Euc d,
      HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χ Ψ τ z) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc (hχ.of_le (by exact_mod_cast le_top)) one_ne_zero
  refine ⟨(L : ℝ) * Real.exp (|Cb| * t), by positivity, fun τ hτ z x y => ?_⟩
  have h1 := hL.dist_le_mul (Function.invFun (Ψ τ) x - z) (Function.invFun (Ψ τ) y - z)
  rw [Real.dist_eq, dist_eq_norm] at h1
  have h2 := hF.lip_inv τ hτ x y
  have h3 : Real.exp (Cb * τ) ≤ Real.exp (|Cb| * t) := by
    refine Real.exp_le_exp.2 ?_
    calc Cb * τ ≤ |Cb| * τ := mul_le_mul_of_nonneg_right (le_abs_self Cb) hτ.1
      _ ≤ |Cb| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
  unfold advCutoff
  calc |χ (Function.invFun (Ψ τ) x - z) - χ (Function.invFun (Ψ τ) y - z)|
      ≤ (L : ℝ) * ‖Function.invFun (Ψ τ) x - z - (Function.invFun (Ψ τ) y - z)‖ := h1
    _ = (L : ℝ) * ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ := by
        congr 2; abel
    _ ≤ (L : ℝ) * (Real.exp (Cb * τ) * ‖x - y‖) := by gcongr
    _ ≤ (L : ℝ) * (Real.exp (|Cb| * t) * ‖x - y‖) := by gcongr
    _ = _ := by ring

/-- Test-function facts for `ψ' = ς f`. -/
theorem n2b_psi_facts {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hK : FlowBundle d m Cb t χ χh b Ψ K) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) t) (c : Euc d) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 2 (fun x => varsigma χ Ψ σ c x * f x) ∧
    HasCompactSupport (fun x => varsigma χ Ψ σ c x * f x) ∧
    Function.support (fun x => varsigma χ Ψ σ c x * f x) ⊆
      closedBall (Ψ σ c) (2 * Real.exp (Cb * t)) ∧
    (∀ y, |varsigma χ Ψ σ c y * f y| ≤ |f y|) := by
  refine ⟨(hK.contDiff σ hσ c).mul (hf.of_le (by simp)),
    (hK.compact_supp σ hσ c).mul_right, ?_, fun y => ?_⟩
  · exact (Function.support_mul_subset_left _ _).trans
      (subset_tsupport _ |>.trans (hK.supp σ hσ c))
  · rw [abs_mul]
    have h := hK.range σ hσ c y
    calc |varsigma χ Ψ σ c y| * |f y| ≤ 1 * |f y| := by
          gcongr; rw [abs_of_nonneg h.1]; exact h.2
      _ = |f y| := one_mul _

/-- **Packet N2b: the regime `R2a` core estimate.**  Hypotheses: `0 ≤ s < d` (`WholeMainData.hs0/hsd`),
`d ≥ 1`, `RdRegimeHolds R2a` (`d - 2 < s`, `symPart M = 0`), `CoeffHypRd D.s m Λ T ρ` on `[0,T] ∋ t`, a cutoff pair,
an advecting drift `b` on `[0,t]` with its flow `Ψ`, and the flow bundle of packet C3.  The constant `C` depends on
`(d, D.s, M, m, Cb, Λ, t, K, χ, χh, ρ)` but not on `σ, c, f, A`. -/
theorem n2b_r2a_core (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ν₀ : ℝ)
    (hR : RdRegimeHolds PDE.Regime.R2a d D.s D.M D.invβ ν₀)
    (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ) (hcoef : CoeffHypRd D.s m Λ T ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ), 0 ≤ A →
      ContDiff ℝ ∞ f → LocMass A f →
      |nMain D (ρ (t - σ)) f (fun x => varsigma χ Ψ σ c x * f x)| ≤ C * A ^ 2 := by
  have hR' : (d : ℝ) - 2 < D.s ∧ Torus.symPart D.M = 0 := hR
  have hM : ∀ i j, D.M j i + D.M i j = 0 := by
    intro i j
    have := congrFun (congrFun hR'.2 j) i
    simp only [Torus.symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul, Matrix.zero_apply] at this
    linarith
  set L : ℝ := Real.exp (Cb * t) with hL
  have hL0 : 0 < L := Real.exp_pos _
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  have hr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  -- the uniform bound on each term
  have key : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ)
      (i j : Fin d), 0 ≤ A → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, f y * (D1 j (ρ (t - σ)) y *
        kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤ C0 * A ^ 2 := by
    by_cases hs1 : (d : ℝ) - 1 < D.s
    · -- `d - 1 < s < d`: the truncation bridge of N2a
      obtain ⟨C, N, hC⟩ := n2a_main_locmass hd D.s hs1 hsd m Cb t χ χh hχ
      obtain ⟨Lχ0, hLχ0, hLχ⟩ := n2b_advCutoff_lip hK.flow hχ.1.1 hχ.1.2.1
      set Q : ℝ := C ^ 2 * Real.exp (|C| * d * t) * max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * N
        with hQ
      refine ⟨Q, by positivity, fun σ hσ c A f i j hA hf hfm => ?_⟩
      obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
      obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
      have hmeas : Measurable f := (hf.continuous).measurable
      obtain ⟨_, _, h3⟩ := hC b Ψ hb hΨ σ hσ c Lχ0 (hLχ σ hσ c) i Cρ Cρ (D1 j (ρ (t - σ))) f
        (hlip j) (hjb j) hmeas A hfm (hψ2.of_le (by norm_num)) hψc
      have h3' : |∫ y, f y * (D1 j (ρ (t - σ)) y *
          kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤
          C * max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * ((N : ℝ) * A ^ 2) *
            (C * Real.exp (C * d * σ)) := by
        simp only [mul_assoc] at h3 ⊢
        exact h3
      refine h3'.trans ?_
      have hexp : Real.exp (C * d * σ) ≤ Real.exp (|C| * d * t) := by
        refine Real.exp_le_exp.2 ?_
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        calc C * d * σ ≤ |C| * d * σ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hd0) hσ.1
          _ ≤ |C| * d * t := mul_le_mul_of_nonneg_left hσ.2 (by positivity)
      have hQ0 : 0 ≤ max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * (N : ℝ) * A ^ 2 := by positivity
      calc C * max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * ((N : ℝ) * A ^ 2) *
            (C * Real.exp (C * d * σ))
          = (C ^ 2 * Real.exp (C * d * σ)) *
              (max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * (N : ℝ) * A ^ 2) := by ring
        _ ≤ (C ^ 2 * Real.exp (|C| * d * t)) *
              (max 1 D.s * (Cρ + Cρ) * (1 + Lχ0) ^ 2 * (N : ℝ) * A ^ 2) := by gcongr
        _ = Q * A ^ 2 := by rw [hQ]; ring
    · -- `d - 2 < s ≤ d - 1`: `kgOrder = 0`
      have hs1' : D.s ≤ (d : ℝ) - 1 := not_lt.1 hs1
      obtain ⟨C0, hC0, hlow⟩ := n2b_case_low hd hs0 hsd hs1' (2 * L) Cρ (by positivity) hCρ0
      refine ⟨C0, hC0, fun σ hσ c A f i j hA hf hfm => ?_⟩
      obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
      obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
      exact hlow (Ψ σ c) A f (D1 j (ρ (t - σ))) _ i hA hfm (hjb j) (hψ2.of_le (by norm_num))
        hψc hψs hψf
  obtain ⟨C0, hC0, hkey⟩ := key
  refine ⟨(∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * C0, by positivity, ?_⟩
  intro σ hσ c A f hA hf hfm
  obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
  obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
  rw [n2b_nMain_eq hs0 hsd hM hρ1 hρ0 hρ1' hfm hψ2 hψc]
  calc |∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j (ρ (t - σ)) y *
          kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)|
      ≤ ∑ i, ∑ j, |D.M j i| * (C0 * A ^ 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hkey σ hσ c A f i j hA hf hfm) (abs_nonneg _)
    _ = (∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * C0 * A ^ 2 := by
        simp only [← Finset.sum_mul]
        ring

end HRS.MS.UniqN2b
