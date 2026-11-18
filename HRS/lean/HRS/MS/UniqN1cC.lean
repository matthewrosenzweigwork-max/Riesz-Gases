import HRS.MS.UniqN1cB

/-!
# N1c of `UniqPlan.md`, part (c): the `R1` core estimate

`n1c_r1_core`: in the regime `R1` (`s ≤ d - 2`, any `ν ≥ 0`, any matrix `M`), for `ψ' = ς_c^σ f` with
`f ∈ C^∞` of uniform local `L²` mass `A`, `|nMain D (ρ (t-σ)) f ψ'| ≤ C A²` with `C` independent of
`σ, c, f, A`.  By `n1c_nMain_eq`, `nMain = ∑ M_{ji} (∫ f ∂_jρ' H_i + ∫ f ρ' ∂_jH_i)`; the first integral is
bounded by `n2b_case_low` (`s ≤ d - 1`), the second by `n1c_case_hess`.  No sign and no derivative of `f`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1
  HRS.MS.UniqNDefs HRS.MS.UniqC3 HRS.MS.UniqN2b

variable {d : ℕ}

/-- **Packet N1c: the regime `R1` core estimate.** -/
theorem n1c_r1_core (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ν₀ : ℝ)
    (hR : RdRegimeHolds PDE.Regime.R1 d D.s D.M D.invβ ν₀)
    (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ) (hcoef : CoeffHypRd D.s m Λ T ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ), 0 ≤ A →
      ContDiff ℝ ∞ f → LocMass A f →
      |nMain D (ρ (t - σ)) f (fun x => varsigma χ Ψ σ c x * f x)| ≤ C * A ^ 2 := by
  have hs2 : D.s ≤ (d : ℝ) - 2 := hR
  have hs1 : D.s ≤ (d : ℝ) - 1 := by linarith
  set L : ℝ := Real.exp (Cb * t) with hL
  have hL0 : 0 < L := Real.exp_pos _
  set Cρ : ℝ := HRS.MS.UniqC1.c1A d m Λ with hCρ
  have hCρ0 : 0 ≤ Cρ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  have hr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  -- the density satisfies the `jbracket` decay bound
  have hjbρ : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ y,
      jbracket y ^ ((d : ℝ) + 3) * |ρ (t - σ) y| ≤ Cρ := by
    intro σ hσ y
    obtain ⟨_, _, h0, _⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
    have hjb : 0 < jbracket y := by unfold jbracket; positivity
    have hpos : 0 < 1 + ‖y‖ := by positivity
    have e1 : jbracket y ^ ((d : ℝ) + 3) ≤ (1 + ‖y‖) ^ ((d : ℝ) + 3) :=
      Real.rpow_le_rpow hjb.le (n2b_jbracket_le y) (by positivity)
    calc jbracket y ^ ((d : ℝ) + 3) * |ρ (t - σ) y|
        ≤ (1 + ‖y‖) ^ ((d : ℝ) + 3) * (Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) :=
          mul_le_mul e1 (h0 y) (abs_nonneg _) (by positivity)
      _ = Cρ := by
          rw [mul_left_comm, ← Real.rpow_add hpos]; simp
  obtain ⟨C1, hC1, hlow⟩ := n2b_case_low hd hs0 hsd hs1 (2 * L) Cρ (by positivity) hCρ0
  obtain ⟨C2, hC2, hhess⟩ := n1c_case_hess hd hs0 hsd hs2 (2 * L) Cρ (by positivity) hCρ0
  refine ⟨(∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * (C1 + C2), by positivity, ?_⟩
  intro σ hσ c A f hA hf hfm
  obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
  obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
  rw [n1c_nMain_eq hs0 hsd hρ1 hρ0 hρ1' hfm hψ2 hψc]
  have hterm : ∀ i j : Fin d, |(∫ y, f y * (D1 j (ρ (t - σ)) y *
        kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)) +
      ∫ y, f y * (ρ (t - σ) y *
        D1 j (kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x)) y)| ≤
      (C1 + C2) * A ^ 2 := by
    intro i j
    refine (abs_add_le _ _).trans ?_
    have h1 := hlow (Ψ σ c) A f (D1 j (ρ (t - σ))) _ i hA hfm (hjb j) (hψ2.of_le (by norm_num))
      hψc hψs hψf
    have h2 := hhess (Ψ σ c) A f (ρ (t - σ)) _ i j hA hfm (hjbρ σ hσ) hψ2 hψc hψs hψf
    linarith
  calc |∑ i, ∑ j, D.M j i * ((∫ y, f y * (D1 j (ρ (t - σ)) y *
          kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)) +
        ∫ y, f y * (ρ (t - σ) y *
          D1 j (kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x)) y))|
      ≤ ∑ i, ∑ j, |D.M j i| * ((C1 + C2) * A ^ 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hterm i j) (abs_nonneg _)
    _ = (∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * (C1 + C2) * A ^ 2 := by
        simp only [← Finset.sum_mul]
        ring

end HRS.MS.UniqN1c
