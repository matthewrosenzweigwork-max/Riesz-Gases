import HRS.MC.D3T1
import HRS.MC.D3T3
import HRS.MC.D3TW
import HRS.MC.D3TG

/-!
# Packet D3TAsm: Lemma D.3 on `𝕋^d` (`HRS.fdl_kernel_torus`) assembled from `D3T1` (i, iv), `D3TW`/`D3TG` (ii)
and `D3T3` (iii).  The statement is copied verbatim from `HRS/Appendix/FDL.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.D3TAsm

open HRS

variable {d : ℕ}

theorem fdl_kernel_torus_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    -- (i)
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ x : Torus d, x ≠ 0 → 0 ≤ fdlWT ψ s b lam x) ∧
      (∀ x : Torus d, lam ≤ KernelGrad.tdist x 0 →
        fdlWT ψ s b lam x = 0 ∧ fdlTruncT ψ s b lam x = periodicRiesz d s x) ∧
      (∀ x : Torus d, x ≠ 0 → fdlWT ψ s b lam x ≤ periodicRiesz d s x + C) ∧
      ∫⁻ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s))) ∧
    -- (ii), `j + s > 0`
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ y : Euc d, Torus.mk y ≠ 0 →
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlWT ψ s b lam)) y‖ ≤
          (if KernelGrad.tdist (Torus.mk y) 0 ≤ lam then
            C * KernelGrad.tdist (Torus.mk y) 0 ^ (-s - (j : ℝ)) else 0) ∧
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤
          C * (max lam (KernelGrad.tdist (Torus.mk y) 0)) ^ (-s - (j : ℝ)) + C) ∧
    -- (ii), `s = j = 0`
    (s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      |fdlWT ψ s b lam x| ≤
        (if KernelGrad.tdist x 0 ≤ lam then C * Real.log (lam / KernelGrad.tdist x 0) else 0)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      s = 0 → |fdlTruncT ψ s b lam x| ≤ C * (1 + |Real.log lam|)) ∧
    -- (ii), smoothness and sup bounds ("in particular")
    (∀ lam : ℝ, 0 < lam → lam < 1 → Torus.IsSmooth (fdlTruncT ψ s b lam)) ∧
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤ C * lam ^ (-s - (j : ℝ))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncT ψ s b lam 0| ≤
        C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0))) ∧
    -- (iii)
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d,
      Torus.fcoef (fdlWT ψ s b lam) k = ((fdlWhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlWhat ψ s b lam k) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d, k ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t)
        (Set.Ioi lam) ∧
      Torus.fcoef (fdlTruncT ψ s b lam) k = ((fdlGhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlGhat ψ s b lam k) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k) ∧
      |Torus.laplacian (fdlTruncT ψ s b lam) 0| ≤
        4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ∧
      4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ≤
        C * lam ^ (-s - 2)) ∧
    -- (iv)
    (0 < s → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 →
      c * KernelGrad.tdist x 0 ^ (-s) - C ≤ fdlTruncT ψ s b lam x) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 → KernelGrad.tdist x 0 ≤ 1 / 2 →
      c * Real.log (1 / KernelGrad.tdist x 0) - C ≤ fdlTruncT ψ s b lam x) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * lam →
      c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWT ψ s b (K * lam) x) := by
  obtain ⟨hiv1, hiv2, hiv3⟩ := D3T1.d3t_part_iv hd hs0 hsd hψ hb
  refine ⟨D3T1.d3t_part_i hd hs0 hsd hψ hb, ?_, D3TW.d3tw_log hd hs0 hsd hψ hb, D3TG.d3tg_log hd hs0 hsd hψ hb,
    D3TG.d3tg_smooth hd hs0 hsd hψ hb, D3TG.d3tg_sup hd hs0 hsd hψ hb, D3TG.d3tg_zero hd hs0 hsd hψ hb,
    D3T3.d3f_part_iii_a hd hs0 hsd hψ hb, D3T3.d3f_part_iii_b hd hs0 hsd hψ hb,
    D3T3.d3f_part_iii_c hd hs0 hsd hψ hb, hiv1, hiv2, hiv3⟩
  intro j hj
  obtain ⟨C1, hC1, h1⟩ := D3TW.d3tw_deriv hd hs0 hsd hψ hb j hj
  obtain ⟨C2, hC2, h2⟩ := D3TG.d3tg_deriv hd hs0 hsd hψ hb j hj
  refine ⟨max C1 C2, le_max_of_le_left hC1, fun lam hl hl1 y hy => ⟨?_, ?_⟩⟩
  · have := h1 lam hl hl1 y hy
    split_ifs at this ⊢
    · exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (KernelGrad.tdist_nonneg _ _) _))
    · exact this
  · have h := h2 lam hl hl1 y hy
    have hm : 0 ≤ (max lam (KernelGrad.tdist (Torus.mk y) 0)) ^ (-s - (j : ℝ)) :=
      Real.rpow_nonneg (le_trans hl.le (le_max_left _ _)) _
    calc _ ≤ _ := h
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right (le_max_right C1 C2) hm
        linarith [le_max_right C1 C2]

example := (@fdl_kernel_torus_proof : type_of% @HRS.fdl_kernel_torus)

end HRS.MC.D3TAsm
