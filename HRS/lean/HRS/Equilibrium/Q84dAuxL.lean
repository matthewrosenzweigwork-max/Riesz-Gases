/-
# HRS.Equilibrium.Q84dAuxL — packet Q84d: integrability of `E_N(ψ)` (D2, third conjunct)
-/
import HRS.Equilibrium.Q84dAuxK

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

section Main

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

/-- Integrability of `F_N(𝒥ψ)`. -/
theorem q84d_integrable_FstatJ {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    Integrable (Fstat (N := N) (Jpair d s ρ ψ)) (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hK := q84d_K_nonneg hd hcrit hψ
  obtain ⟨C₁, hC₁0, hC₁⟩ := q84d_q_mul_w_le hd hcrit hV hβ hN
  have hJm := q84d_jpair_aestronglyMeasurable (by omega) hsd hρs hf hψ
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN
    (C := (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N * (N * (K₁ * C₁)))) ?_ ?_
  · unfold Fstat
    exact (q84d_aesm_pairSum (N := N) hJm).const_mul _
  · intro X hX
    set q := Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hXne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
    have hps := q84d_pairSum_bound q hq0 (Jpair d s ρ ψ) X (M := K₁ * C₁) (by positivity)
      (fun i j hij => by
        have h1 := (hC₁ X i j hij).1
        have h2 := hψ.jpair_bound (X i) (X j) (hXne i j hij)
        calc q * |Jpair d s ρ ψ (X i) (X j)| ≤ q * (K₁ * wEnv s (X i) (X j)) :=
              mul_le_mul_of_nonneg_left h2 hq0
          _ = K₁ * (q * wEnv s (X i) (X j)) := by ring
          _ ≤ K₁ * C₁ := mul_le_mul_of_nonneg_left h1 hK)
    unfold Fstat
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_mul, abs_of_nonneg hN0]
    calc q * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * |pairSumOrdered (Jpair d s ρ ψ) X|)
        = (N : ℝ) ^ (-(3 / 2 : ℝ)) * (q * |pairSumOrdered (Jpair d s ρ ψ) X|) := by ring
      _ ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N * (N * (K₁ * C₁))) :=
          mul_le_mul_of_nonneg_left hps hN0

/-- Integrability of `N^{-5/2} ∑ B_ψ`. -/
theorem q84d_integrable_pairB {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) {CB : ℝ}
    (hB : ∀ x y, x ≠ y → |Bpsi d s ρ ψ x y| ≤ CB * K₁ * wEnv s x y ^ 2) :
    Integrable (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered (Bpsi d s ρ ψ) X)
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := q84d_q_mul_w_le hd hcrit hV hβ hN
  have hBm := q84d_aesm_Bpsi (ρ := ρ) hsd hψ.symm hψ.size.smooth (by omega)
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN
    (C := (N : ℝ) ^ (-(5 / 2 : ℝ)) * (N * (N * (|CB * K₁| * C₁)))) ?_ ?_
  · exact (q84d_aesm_pairSum (N := N) hBm).const_mul _
  · intro X hX
    set q := Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hXne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
    have hps := q84d_pairSum_bound q hq0 (Bpsi d s ρ ψ) X (M := |CB * K₁| * C₁) (by positivity)
      (fun i j hij => by
        have h1 := (hC₁ X i j hij).2
        have h2 := hB (X i) (X j) (hXne i j hij)
        have h3 : |Bpsi d s ρ ψ (X i) (X j)| ≤ |CB * K₁| * wEnv s (X i) (X j) ^ 2 :=
          h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc q * |Bpsi d s ρ ψ (X i) (X j)| ≤ q * (|CB * K₁| * wEnv s (X i) (X j) ^ 2) :=
              mul_le_mul_of_nonneg_left h3 hq0
          _ = |CB * K₁| * (q * wEnv s (X i) (X j) ^ 2) := by ring
          _ ≤ |CB * K₁| * C₁ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_mul, abs_of_nonneg hN0]
    calc q * ((N : ℝ) ^ (-(5 / 2 : ℝ)) * |pairSumOrdered (Bpsi d s ρ ψ) X|)
        = (N : ℝ) ^ (-(5 / 2 : ℝ)) * (q * |pairSumOrdered (Bpsi d s ρ ψ) X|) := by ring
      _ ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) * (N * (N * (|CB * K₁| * C₁))) :=
          mul_le_mul_of_nonneg_left hps hN0

/-- Integrability of `N^{-5/2} ∑ G_ψ`. -/
theorem q84d_integrable_tripleG {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) {CG : ℝ}
    (hG : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
      CG * K₁ * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) :
    Integrable (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum (Gpsi d s ρ ψ) X)
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨C₂, hC₂0, hC₂⟩ := q84d_q_mul_ww_le hd hcrit hV hβ hN
  have hJm := q84d_jpair_aestronglyMeasurable (by omega) hsd hρs hf hψ
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN
    (C := (N : ℝ) ^ (-(5 / 2 : ℝ)) * (N * (N * (N * (|CG * K₁| * (3 * C₂)))))) ?_ ?_
  · refine (?_ : AEStronglyMeasurable (fun X : Config d N => tripleSum (Gpsi d s ρ ψ) X) volume).const_mul _
    unfold tripleSum
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j hj =>
        Finset.aestronglyMeasurable_fun_sum _ fun k hk => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact q84d_aesm_Gpsi (by omega) hsd hψ.symm hψ.size.smooth hJm hji.symm hki.symm hkj.symm
  · intro X hX
    set q := Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hXne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
    have hps := q84d_tripleSum_bound q hq0 (Gpsi d s ρ ψ) X (M := |CG * K₁| * (3 * C₂))
      (by positivity) (fun i j k hij hik hjk => by
        have t1 := hC₂ X i j i k hij hik (by rintro (⟨_, h⟩ | ⟨h, _⟩) <;> simp_all)
        have t2 := hC₂ X i j j k hij hjk (by rintro (⟨h, _⟩ | ⟨_, h⟩) <;> simp_all)
        have t3 := hC₂ X i k j k hik hjk (by rintro (⟨h, _⟩ | ⟨_, h⟩) <;> simp_all)
        have h2 := hG (X i) (X j) (X k) (hXne i j hij) (hXne i k hik) (hXne j k hjk)
        set S := wEnv s (X i) (X j) * wEnv s (X i) (X k) + wEnv s (X i) (X j) * wEnv s (X j) (X k) +
          wEnv s (X i) (X k) * wEnv s (X j) (X k) with hS
        have hS0 : 0 ≤ S := by
          have w0 : ∀ a b : Torus d, 0 ≤ wEnv s a b :=
            fun a b => zero_le_one.trans (PairCorrAux.one_le_wEnv (d := d) s a b)
          exact add_nonneg (add_nonneg (mul_nonneg (w0 _ _) (w0 _ _)) (mul_nonneg (w0 _ _) (w0 _ _)))
            (mul_nonneg (w0 _ _) (w0 _ _))
        have h3 : |Gpsi d s ρ ψ (X i) (X j) (X k)| ≤ |CG * K₁| * S :=
          h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hS0)
        calc q * |Gpsi d s ρ ψ (X i) (X j) (X k)| ≤ q * (|CG * K₁| * S) :=
              mul_le_mul_of_nonneg_left h3 hq0
          _ = |CG * K₁| * (q * S) := by ring
          _ ≤ |CG * K₁| * (3 * C₂) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              have : q * S = q * (wEnv s (X i) (X j) * wEnv s (X i) (X k)) +
                  q * (wEnv s (X i) (X j) * wEnv s (X j) (X k)) +
                  q * (wEnv s (X i) (X k) * wEnv s (X j) (X k)) := by rw [hS]; ring
              rw [this]; linarith)
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_mul, abs_of_nonneg hN0]
    calc q * ((N : ℝ) ^ (-(5 / 2 : ℝ)) * |tripleSum (Gpsi d s ρ ψ) X|)
        = (N : ℝ) ^ (-(5 / 2 : ℝ)) * (q * |tripleSum (Gpsi d s ρ ψ) X|) := by ring
      _ ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) * (N * (N * (N * (|CG * K₁| * (3 * C₂))))) :=
          mul_le_mul_of_nonneg_left hps hN0

end Main

end HRS.Q84d

end
