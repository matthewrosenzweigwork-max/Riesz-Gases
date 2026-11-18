import HRS.Equilibrium.Parametrix.PX3aAuxZ

/-!
# Packet PX3a auxiliaries AA: the Newton map on symmetric kernels
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

lemma chartSource_even {F : Torus d → Torus d → ℝ} (hF : IsSymmPair F) (X w : Euc d) :
    (fun q : Euc d × Euc d => chi d q.2 * toChart F q) (X, -w) =
      (fun q : Euc d × Euc d => chi d q.2 * toChart F q) (X, w) := by
  simp only [px3a_chi_neg, px3a_toChart_neg hF]

theorem newton_ofChart_sym (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F →
      Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
        (ofChart (newtonChart d ν (toChart F))) := by
  by_cases hσ1 : σ = 1
  · subst hσ1
    have hb' : ∀ c : ℕ, (b + if (1 : ℝ) - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) = b := by
      intro c
      have : ¬ ((1 : ℝ) - 2 + (c : ℝ) = 0 ∧ c ≠ 1) := by
        rintro ⟨h0, hc⟩
        apply hc
        have : (c : ℝ) = 1 := by linarith
        exact_mod_cast this
      rw [if_neg this, add_zero]
    obtain ⟨Cq, hCq0, hCq⟩ := newton_conormal_of_pot hd hν hσ b m (fun _ => b) (fun _ => le_rfl)
      (fun _ => by omega)
    obtain ⟨K1, hK1, hsrc⟩ := srcCls_chart (d := d) (1 : ℝ) b m
    obtain ⟨Cu, hCu0, hCu⟩ := newtonPot_bound_uniform hd hσ b m
    obtain ⟨Cs, hCs0, hCs⟩ := base_pos_sym hd b m
    refine ⟨Cq * ((Cu + Cs) * K1), by positivity, fun B F hB hsym hF => ?_⟩
    have key := hCq ((Cu + Cs) * K1) B F (by positivity) hB hF ?_
    · have e : (fun c : ℕ => b + if (1 : ℝ) - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) = fun _ => b :=
        funext hb'
      simpa [e] using key
    · intro a c hac r hr hr1 X z hz u v
      have hg := hsrc B F hB hF
      have hA : 0 ≤ K1 * B := mul_nonneg hK1 hB
      have hP : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
      by_cases hc : c = 1
      · subst hc
        have := hCs hg hA (chartSource_even hsym) hac hr hr1 X z hz u v
        refine this.trans ?_
        have e : r ^ (-((1 : ℝ) - 2 + ((1 : ℕ) : ℝ))) = 1 := by
          have : -((1 : ℝ) - 2 + ((1 : ℕ) : ℝ)) = 0 := by push_cast; ring
          rw [this, Real.rpow_zero]
        rw [e, one_mul]
        have hL : 0 ≤ lw r ^ b := pow_nonneg (lw_pos _).le b
        have : (Cs * (K1 * B)) * (1 + lw r ^ b) ≤ ((Cu + Cs) * K1) * B * (1 + lw r ^ b) := by
          have : Cs * (K1 * B) ≤ ((Cu + Cs) * K1) * B := by nlinarith [mul_nonneg hCu0 (mul_nonneg hK1 hB)]
          exact mul_le_mul_of_nonneg_right this (by linarith)
        exact mul_le_mul_of_nonneg_right this hP
      · have := hCu hg hA hac hr hr1 X z hz u v
        refine this.trans ?_
        have hne : ¬ ((1 : ℝ) - 2 + (c : ℝ) = 0) := by
          intro h0; apply hc
          have : (c : ℝ) = 1 := by linarith
          exact_mod_cast this
        rw [if_neg hne, add_zero]
        have hT : 0 ≤ 1 + r ^ (-((1 : ℝ) - 2 + (c : ℝ))) * lw r ^ b :=
          by have : 0 ≤ r ^ (-((1 : ℝ) - 2 + (c : ℝ))) * lw r ^ b :=
                mul_nonneg (Real.rpow_nonneg hr.le _) (pow_nonneg (lw_pos _).le _)
             linarith
        have : Cu * (K1 * B) ≤ ((Cu + Cs) * K1) * B := by nlinarith [mul_nonneg hCs0 (mul_nonneg hK1 hB)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) hP
  · obtain ⟨C, hC0, hC⟩ := newton_ofChart_general hd hν hσ b m
    refine ⟨C, hC0, fun B F hB hsym hF => ?_⟩
    have e : (fun c : ℕ => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) =
        fun c : ℕ => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0 := by
      funext c
      have : (σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1) ↔ σ - 2 + (c : ℝ) = 0 := by
        refine ⟨fun h => h.1, fun h => ⟨h, fun hc => hσ1 ?_⟩⟩
        subst hc
        push_cast at h
        linarith
      simp only [this]
    rw [e]
    exact hC B F hB hF

theorem px3a_newton_map (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {β : ℝ}
    (hβ : 0 < β) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F →
      Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) := by
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_sym hd (ν := β⁻¹) (inv_pos.mpr hβ) hσ b m
  obtain ⟨Cc, hCc0, hCc⟩ := canonical_conormal hd hρ (σ := σ - 2) (by linarith) (b + 1) m
  refine ⟨Cc * Cn, mul_nonneg hCc0 hCn0, fun B F hB hsym hF => ?_⟩
  have hN := hCn B F hB hsym hF
  have hcc := hCc (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
    (fun c => by split_ifs <;> omega) (Cn * B) _ (mul_nonneg hCn0 hB) hN
  rw [← mul_assoc] at hcc
  refine conormalL_congr_offDiag (fun x y hxy => ?_) hcc
  unfold newtonOp
  rw [if_neg hxy]

end HRS.Parx

end
