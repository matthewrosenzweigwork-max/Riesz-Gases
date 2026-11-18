import HRS.MS.UniqN3cE
import HRS.MS.UniqN2bD
import HRS.MS.UniqN2aF

/-!
# STAR-1: the first-order sum in the corner `d - 1 < s < d`

`star_key_high` is the analogue of `n3c_key` (which needs `s ≤ d - 1`) for `d - 1 < s < d`.  The bound is the same
`O(A²)` for the scalar integral `∫ f (∂_jρ' · ∂_i(g * (ς f)))` for ANY matrix `M` (it is per `(i,j)`), obtained from
`n2a_main_locmass` with the scalar coefficient `a = ∂_jρ'` exactly as in `n2b_r2a_core`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN3c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqC3 HRS.MS.UniqN2b HRS.MS.UniqN2a HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- The first-order sum, `d - 1 < s < d` (any matrix `M`; the statement is per `(i,j)`). -/
theorem star_key_high (hd : 1 ≤ d) (D : WholeDyn d) (hsd : D.s < d)
    (hs1 : (d : ℝ) - 1 < D.s) (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hcoef : CoeffHypRd D.s m Λ T ρ) (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ)
    (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ)
      (i j : Fin d), 0 ≤ A → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, f y * (D1 j (ρ (t - σ)) y *
        kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤ C0 * A ^ 2 := by
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  have hr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
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

end HRS.MS.UniqN3c
