import HRS.MS.UniqN3cC

/-!
# N3c, part D: helper lemmas for the R2c core

* `n3c_mq_homog`: the symbol `c (2π⟨ξ,q⟩)² ‖ξ‖^{s-d}` (`c > 0`) is an `IsHomogSymbol` of order `s + 2 - d`.
* `n3c_key`: the first-order sum `∫ f (∂_jρ' H_i)` is `O(A²)` for `s ≤ d - 1` (`n2b_case_low`).
* `n3c_memLp`: a measurable function with decay `(1+‖x‖)^{-(d+3)}` is in `L²`.
* `n3c_p_decay`: `√ρ' ≤ √C (1+‖x‖)^{-(d+3)/2}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN3c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqC3 HRS.MS.UniqN2b HRS.PDE.ToolboxRd

variable {d : ℕ}

theorem n3c_homog_scale {θ : ℝ} {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) {κ : ℝ} (hκ : 0 < κ) :
    IsHomogSymbol θ (fun ξ => κ * m ξ) where
  smooth := contDiffOn_const.mul hm.smooth
  even := fun ξ => by simp only [hm.even]
  nonneg := fun ξ => mul_nonneg hκ.le (hm.nonneg ξ)
  homog := fun c hc ξ => by simp only [hm.homog c hc]; ring
  zero := by simp [hm.zero]

theorem n3c_rieszConst_pos {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem n3c_mq_homog (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    {c : ℝ} (hc : 0 < c) (q : Euc d) :
    IsHomogSymbol (s + 2 - d) (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)) := by
  have h := symbolK_isHomogSymbol hd s hs0 hs1 hsd q
  have hR : 0 < rieszConst d s := n3c_rieszConst_pos hd hs0 hsd
  have hP : 0 < (2 * Real.pi) ^ (s - (d : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have h2 := n3c_homog_scale h (κ := c / (rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ))))
    (by positivity)
  have heq : (fun ξ : Euc d => c / (rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ))) *
        symbolKRd d s q ξ) = fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d) := by
    funext ξ
    unfold symbolKRd
    rw [Real.mul_rpow (by positivity) (norm_nonneg ξ), real_inner_comm]
    field_simp
  rw [heq] at h2
  exact h2

/-- The first-order sum, `s ≤ d - 1`. -/
theorem n3c_key (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hs1 : D.s ≤ (d : ℝ) - 1) (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hcoef : CoeffHypRd D.s m Λ T ρ) (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (K : ℝ)
    (hK : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A : ℝ) (f : Euc d → ℝ)
      (i j : Fin d), 0 ≤ A → ContDiff ℝ ∞ f → LocMass A f →
      |∫ y, f y * (D1 j (ρ (t - σ)) y *
        kernelConvDeriv d D.s i (fun x => varsigma χ Ψ σ c x * f x) y)| ≤ C0 * A ^ 2 := by
  have hL0 : 0 < Real.exp (Cb * t) := Real.exp_pos _
  have hCρ0 : 0 ≤ HRS.MS.UniqC1.c1A d m Λ := HRS.MS.UniqE1.e1_A_nonneg m Λ
  have hr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨C0, hC0, hlow⟩ := n2b_case_low hd hs0 hsd hs1 (2 * Real.exp (Cb * t))
    (HRS.MS.UniqC1.c1A d m Λ) (by positivity) hCρ0
  refine ⟨C0, hC0, fun σ hσ c A f i j hA hf hfm => ?_⟩
  obtain ⟨hρ1, hρ2, hρ0, hρ1', hlip, hjb⟩ := n2b_rho_coeff hd hcoef (hr σ hσ)
  obtain ⟨hψ2, hψc, hψs, hψf⟩ := n2b_psi_facts hK hσ c hf
  exact hlow (Ψ σ c) A f (D1 j (ρ (t - σ))) _ i hA hfm (hjb j) (hψ2.of_le (by norm_num))
    hψc hψs hψf

/-- Decay implies `L²`. -/
theorem n3c_memLp {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) {C : ℝ}
    (hb : ∀ x, |u x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) : MemLp u 2 volume := by
  rw [memLp_two_iff_integrable_sq hu]
  have hκ : (d : ℝ) < (d : ℝ) + 3 := by linarith
  have hdom : Integrable (fun x : Euc d => C ^ 2 * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) volume :=
    (integrable_one_add_norm (E := Euc d) (μ := volume) (r := (d : ℝ) + 3)
      (by simp [hκ])).const_mul _
  refine hdom.mono' (hu.pow 2) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hw0 : 0 ≤ (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by positivity
  have hw1 : (1 + ‖x‖) ^ (-((d : ℝ) + 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)
  have h1 : |u x| ^ 2 ≤ (C * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  rw [← sq_abs (u x)]
  calc |u x| ^ 2 ≤ (C * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ^ 2 := h1
    _ = C ^ 2 * ((1 + ‖x‖) ^ (-((d : ℝ) + 3)) * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) := by ring
    _ ≤ C ^ 2 * ((1 + ‖x‖) ^ (-((d : ℝ) + 3)) * 1) := by gcongr
    _ = C ^ 2 * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by rw [mul_one]

/-- Decay of the square root. -/
theorem n3c_p_decay {ρ' : Euc d → ℝ} (h0 : ∀ x, 0 ≤ ρ' x) {C : ℝ}
    (hb : ∀ x, |ρ' x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) (x : Euc d) :
    Real.sqrt (ρ' x) ≤ Real.sqrt C * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) := by
  have hw : 0 ≤ (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) := by positivity
  have h1 : (1 + ‖x‖) ^ (-((d : ℝ) + 3)) = ((1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h2 : ρ' x ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := (le_abs_self _).trans (hb x)
  have hC : 0 ≤ C := by
    have : 0 ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := (h0 x).trans h2
    have hp : 0 < (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by positivity
    exact (mul_nonneg_iff_of_pos_right hp).1 this
  calc Real.sqrt (ρ' x) ≤ Real.sqrt (C * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt C * (1 + ‖x‖) ^ (-(((d : ℝ) + 3) / 2)) := by
        rw [h1, Real.sqrt_mul hC, Real.sqrt_sq hw]

end HRS.MS.UniqN3c
