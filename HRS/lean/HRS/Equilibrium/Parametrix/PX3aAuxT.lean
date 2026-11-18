import HRS.Equilibrium.Parametrix.PX3aAuxS

/-!
# Packet PX3a auxiliaries T: kernels `-r₁(x) - r₂(y) + c` are conormal (finite smoothness)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem norm_iteratedFDeriv_sub_prod_le_m {n : ℕ} {Φ₁ Φ₂ : Euc d → ℝ}
    (hΦ₁ : ContDiff ℝ (n : WithTop ℕ∞) Φ₁) (hΦ₂ : ContDiff ℝ (n : WithTop ℕ∞) Φ₂) {i : ℕ} (hi : i ≤ n)
    (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₁ q.1 - Φ₂ q.2) p‖ ≤
      ‖iteratedFDeriv ℝ i Φ₁ p.1‖ + ‖iteratedFDeriv ℝ i Φ₂ p.2‖ := by
  have hin : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Euc d × Euc d => Φ₁ q.1) := hΦ₁.comp contDiff_fst
  have h2 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Euc d × Euc d => Φ₂ q.2) := hΦ₂.comp contDiff_snd
  rw [show (fun q : Euc d × Euc d => Φ₁ q.1 - Φ₂ q.2) =
      (fun q : Euc d × Euc d => Φ₁ q.1) - (fun q : Euc d × Euc d => Φ₂ q.2) from rfl,
    iteratedFDeriv_sub_apply (h1.contDiffAt.of_le hin) (h2.contDiffAt.of_le hin)]
  have e1 : iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₁ q.1) p =
      (iteratedFDeriv ℝ i Φ₁ p.1).compContinuousLinearMap (fun _ => ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) hΦ₁ p hin
  have e2 : iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₂ q.2) p =
      (iteratedFDeriv ℝ i Φ₂ p.2).compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) hΦ₂ p hin
  have hfst : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)
  have hsnd : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [e1]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i Φ₁ p.1‖ * 1 := by gcongr
      _ = _ := mul_one _
  · rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i Φ₂ p.2‖ * 1 := by gcongr
      _ = _ := mul_one _

theorem norm_iteratedFDeriv_sigma2_le_m {n : ℕ} {Φ₁ Φ₂ : Euc d → ℝ}
    (hΦ₁ : ContDiff ℝ (n : WithTop ℕ∞) Φ₁) (hΦ₂ : ContDiff ℝ (n : WithTop ℕ∞) Φ₂) (c : ℝ) {k : ℕ}
    (hk : k ≤ n) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (fun q : Euc d × Euc d => -Φ₁ q.1 - Φ₂ q.2 + c) p‖ ≤
      ‖iteratedFDeriv ℝ k Φ₁ p.1‖ + ‖iteratedFDeriv ℝ k Φ₂ p.2‖ + |c| := by
  have hkn : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  have hneg : ContDiff ℝ (n : WithTop ℕ∞) (fun y => -Φ₁ y) := hΦ₁.neg
  have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Euc d × Euc d => -Φ₁ q.1 - Φ₂ q.2) :=
    (hneg.comp contDiff_fst).sub (hΦ₂.comp contDiff_snd)
  have e : (fun q : Euc d × Euc d => -Φ₁ q.1 - Φ₂ q.2 + c) =
      (fun q : Euc d × Euc d => -Φ₁ q.1 - Φ₂ q.2) + (fun _ : Euc d × Euc d => c) := rfl
  rw [e, iteratedFDeriv_add_apply (h1.contDiffAt.of_le hkn) (contDiffAt_const.of_le hkn)]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_iteratedFDeriv_const_le c k p))
  have := norm_iteratedFDeriv_sub_prod_le_m hneg hΦ₂ hk p
  have e2 : iteratedFDeriv ℝ k (fun y => -Φ₁ y) p.1 = -iteratedFDeriv ℝ k Φ₁ p.1 :=
    iteratedFDeriv_neg_apply
  simpa [e2] using this

theorem conormal_sigma2 (σ : ℝ) (m : ℕ) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (r₁ r₂ : Torus d → ℝ), Torus.IsCk (m : WithTop ℕ∞) r₁ →
      Torus.IsCk (m : WithTop ℕ∞) r₂ → ∀ c₀ : ℝ, |c₀| ≤ Torus.cbNorm m r₁ →
      ConormalL σ (fun _ => 0) m (Cs * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂))
        (fun x y => -r₁ x - r₂ y + c₀) := by
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth_aux (d := d) m σ (fun _ => 0)
  have hone : ConormalL σ (fun _ => 0) m (∑ k ∈ Finset.range (m + 1), (2 : ℝ) ^ k * 1)
      (fun _ _ : Torus d => (1 : ℝ)) :=
    conormal_of_smooth_kernel σ (fun _ => 0) m (a := fun _ _ : Torus d => (1 : ℝ))
      (by exact contDiff_const) (fun _ => 1) (fun k p => by
        have := norm_iteratedFDeriv_const_le (d := d) 1 k p
        have e : lift2 (fun _ _ : Torus d => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
        rw [e]
        simpa using this)
  set B1 : ℝ := ∑ k ∈ Finset.range (m + 1), (2 : ℝ) ^ k * 1 with hB1
  have hB10 : 0 ≤ B1 := Finset.sum_nonneg fun k _ => by positivity
  refine ⟨Cm * B1 * ((m : ℝ) + 2), by positivity, fun r₁ r₂ hr₁ hr₂ c₀ hc₀ => ?_⟩
  have hΦ₁ : ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift r₁) := hr₁
  have hΦ₂ : ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift r₂) := hr₂
  set S : Torus d → Torus d → ℝ := fun x y => -r₁ x - r₂ y + c₀ with hS
  have hSc : PDE.IsCk2 m S := by
    have : PDE.lift2 S = fun q : Euc d × Euc d => -Torus.lift r₁ q.1 - Torus.lift r₂ q.2 + c₀ := rfl
    unfold PDE.IsCk2
    rw [this]
    exact (((hΦ₁.comp contDiff_fst).neg).sub (hΦ₂.comp contDiff_snd)).add contDiff_const
  have hbdd : ∀ (r : Torus d → ℝ), ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift r) → ∀ i : ℕ, i ≤ m →
      BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ i (Torus.lift r) x‖) := by
    intro r hr i hi
    obtain ⟨M, _, hM⟩ := bdd_iteratedFDeriv_lift r i (hr.of_le (by exact_mod_cast hi))
    exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  set R₁ : ℕ → ℝ := fun k => ⨆ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift r₁) y‖ with hR₁
  set R₂ : ℕ → ℝ := fun k => ⨆ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift r₂) y‖ with hR₂
  have hR₁0 : ∀ k, 0 ≤ R₁ k := fun k => Real.iSup_nonneg fun _ => norm_nonneg _
  have hR₂0 : ∀ k, 0 ≤ R₂ k := fun k => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcb₁ : Torus.cbNorm m r₁ = ∑ k ∈ Finset.range (m + 1), R₁ k := rfl
  have hcb₂ : Torus.cbNorm m r₂ = ∑ k ∈ Finset.range (m + 1), R₂ k := rfl
  have hcb₁0 : 0 ≤ Torus.cbNorm m r₁ := by rw [hcb₁]; exact Finset.sum_nonneg fun k _ => hR₁0 k
  have hcb₂0 : 0 ≤ Torus.cbNorm m r₂ := by rw [hcb₂]; exact Finset.sum_nonneg fun k _ => hR₂0 k
  have hcb2 : PDE.cbNorm2 m S ≤ Torus.cbNorm m r₁ + Torus.cbNorm m r₂ + ((m : ℝ) + 1) * |c₀| := by
    unfold PDE.cbNorm2
    have : ∀ j ∈ Finset.range (m + 1), (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (PDE.lift2 S) p‖) ≤
        R₁ j + R₂ j + |c₀| := by
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      refine ciSup_le fun p => ?_
      have h1 := norm_iteratedFDeriv_sigma2_le_m hΦ₁ hΦ₂ c₀ hjm p
      have h2 : ‖iteratedFDeriv ℝ j (Torus.lift r₁) p.1‖ ≤ R₁ j := le_ciSup (hbdd r₁ hΦ₁ j hjm) p.1
      have h3 : ‖iteratedFDeriv ℝ j (Torus.lift r₂) p.2‖ ≤ R₂ j := le_ciSup (hbdd r₂ hΦ₂ j hjm) p.2
      have : PDE.lift2 S = fun q : Euc d × Euc d => -Torus.lift r₁ q.1 - Torus.lift r₂ q.2 + c₀ := rfl
      rw [this]
      linarith
    calc _ ≤ ∑ j ∈ Finset.range (m + 1), (R₁ j + R₂ j + |c₀|) := Finset.sum_le_sum this
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, hcb₁, hcb₂]
        push_cast; ring
  have hcb20 : 0 ≤ PDE.cbNorm2 m S := by
    unfold PDE.cbNorm2
    exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hmul := hCm B1 (fun _ _ => 1) S hone hSc
  have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => (0 : ℕ))) = fun _ => 0 := by
    funext c; simp
  rw [hsup] at hmul
  have hSfun : (fun x y => S x y * (fun _ _ : Torus d => (1 : ℝ)) x y) = S := by
    funext x y; simp
  rw [hSfun] at hmul
  refine conormalL_mono_B hmul (by positivity) ?_
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : ((m : ℝ) + 1) * |c₀| ≤ ((m : ℝ) + 1) * Torus.cbNorm m r₁ :=
    mul_le_mul_of_nonneg_left hc₀ (by linarith)
  have h2 : PDE.cbNorm2 m S ≤ ((m : ℝ) + 2) * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂) := by
    nlinarith [mul_nonneg hm0 hcb₂0]
  calc Cm * PDE.cbNorm2 m S * B1 = (Cm * B1) * PDE.cbNorm2 m S := by ring
    _ ≤ (Cm * B1) * (((m : ℝ) + 2) * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hCm0 hB10)
    _ = _ := by ring

end HRS.Parx

end
