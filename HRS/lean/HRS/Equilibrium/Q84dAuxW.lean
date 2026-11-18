/-
# HRS.Equilibrium.Q84dAuxW — packet Q84d: measurability, bounds and integrability of `v_{ik}`
-/
import HRS.Equilibrium.Q84dAuxV

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_measurable_vik (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) {β : ℝ} (ψ : Torus d → Torus d → ℝ) (i : Fin N) (k : Fin d) :
    Measurable (vik d s V β ψ i k : Config d N → ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hq : Measurable (qd d s V β : Config d N → ℝ) :=
    q84d_measurable_q (q84d_measurable_g hd hcrit) (q84d_measurable_V hV)
  have hpair : ∀ (F : Torus d × Torus d → ℝ), Measurable F → ∀ j : Fin N,
      Measurable (fun X : Config d N => F (X i, X j)) := fun F hF j =>
    hF.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hA : Measurable (Aik d ψ i k : Config d N → ℝ) := by
    unfold Aik
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact hpair (fun p => gK ψ k p.1 p.2) (q84d_measurable_gK ψ k) j
  have hC : Measurable (Cik d ψ i k : Config d N → ℝ) := by
    unfold Cik
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact hpair (fun p => hK ψ k p.1 p.2) (q84d_measurable_hK ψ k) j
  have hB : Measurable (Bik d s V i k : Config d N → ℝ) := by
    unfold Bik
    refine Measurable.add ?_ (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_))
    · exact ((EuclideanSpace.proj k).continuous.measurable.comp (q84d_measurable_grad V)).comp
        (measurable_pi_apply i)
    · exact (EuclideanSpace.proj k).continuous.measurable.comp
        ((KernelGrad.measurable_periodicRieszGrad hsd).comp
          ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  unfold vik
  exact hq.mul (hC.sub (measurable_const.mul (hB.mul hA)))

section Bound

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_vik_bound {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : Fin N) (k : Fin d) (X : Config d N), X ∉ collisionSet d N →
      |vik d s V β ψ i k X| ≤ M * ∑ l ∈ Finset.univ.erase i, wEnv s (X i) (X l) := by
  have hK₁ := q84d_K_nonneg hd hcrit hψ
  obtain ⟨Q₀, hQ0, hQ⟩ := q84d_q_le_const hd hcrit hV hβ hN (N := N)
  obtain ⟨Vg, hVg⟩ := q84d_exists_grad_bound hV
  have hVg0 : 0 ≤ Vg := (abs_nonneg _).trans (hVg (0 : Torus d) ⟨0, by omega⟩)
  obtain ⟨Mg, hMg0, hMg⟩ := q84d_q_mul_gradg_le hd hcrit hV hβ hN (N := N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨(Q₀ + β * (Q₀ * Vg + Mg)) * (2 * c * K₁), by positivity, fun i k X hX => ?_⟩
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  set W : ℝ := ∑ l ∈ Finset.univ.erase i, wEnv s (X i) (X l) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun l _ => zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _)
  have hA : |Aik d ψ i k X| ≤ 2 * c * K₁ * W := by
    unfold Aik
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)))]
    rw [← hc]
    calc 2 * c * |∑ j ∈ Finset.univ.erase i, gK ψ k (X i) (X j)|
        ≤ 2 * c * ∑ j ∈ Finset.univ.erase i, K₁ * wEnv s (X i) (X j) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          exact q84d_gK_bound hψ.size (hXne i j (Finset.ne_of_mem_erase hj).symm) k
      _ = 2 * c * K₁ * W := by rw [← Finset.mul_sum]; ring
  have hC : |Cik d ψ i k X| ≤ 2 * c * K₁ * W := by
    unfold Cik
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)))]
    rw [← hc]
    calc 2 * c * |∑ j ∈ Finset.univ.erase i, hK ψ k (X i) (X j)|
        ≤ 2 * c * ∑ j ∈ Finset.univ.erase i, K₁ * wEnv s (X i) (X j) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          exact q84d_hK_bound hψ.size (hXne i j (Finset.ne_of_mem_erase hj).symm) k
      _ = 2 * c * K₁ * W := by rw [← Finset.mul_sum]; ring
  have hq0 : 0 ≤ qd d s V β X := (Real.exp_pos _).le
  have hqB : qd d s V β X * |Bik d s V i k X| ≤ Q₀ * Vg + Mg := by
    unfold Bik
    have h1 : |(Torus.grad V (X i)) k +
        (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X j)) k| ≤
        Vg + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, ‖periodicRieszGrad d s (X i - X j)‖ := by
      refine (abs_add_le _ _).trans (add_le_add (hVg _ _) ?_)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => q84d_comp_le_norm _ k)
    have h2 : qd d s V β X * ∑ j ∈ Finset.univ.erase i, ‖periodicRieszGrad d s (X i - X j)‖ ≤ N * Mg := by
      rw [Finset.mul_sum]
      exact q84d_sum_le_card _ _ hMg0 fun j hj =>
        hMg X i j (Finset.ne_of_mem_erase hj).symm (hXne i j (Finset.ne_of_mem_erase hj).symm)
    calc qd d s V β X * |(Torus.grad V (X i)) k +
          (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X j)) k|
        ≤ qd d s V β X * (Vg + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
            ‖periodicRieszGrad d s (X i - X j)‖) := mul_le_mul_of_nonneg_left h1 hq0
      _ = qd d s V β X * Vg + (1 / (N : ℝ)) * (qd d s V β X * ∑ j ∈ Finset.univ.erase i,
            ‖periodicRieszGrad d s (X i - X j)‖) := by ring
      _ ≤ Q₀ * Vg + (1 / (N : ℝ)) * (N * Mg) := by
          gcongr
          exact hQ X
      _ = Q₀ * Vg + Mg := by field_simp
  have hqC : qd d s V β X * |Cik d ψ i k X| ≤ Q₀ * (2 * c * K₁ * W) :=
    mul_le_mul (hQ X) hC (abs_nonneg _) hQ0
  have hv : |vik d s V β ψ i k X| ≤ qd d s V β X * |Cik d ψ i k X| +
      β * ((qd d s V β X * |Bik d s V i k X|) * |Aik d ψ i k X|) := by
    unfold vik
    rw [abs_mul, abs_of_nonneg hq0]
    calc qd d s V β X * |Cik d ψ i k X - β * (Bik d s V i k X * Aik d ψ i k X)|
        ≤ qd d s V β X * (|Cik d ψ i k X| + |β * (Bik d s V i k X * Aik d ψ i k X)|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hq0
      _ = qd d s V β X * |Cik d ψ i k X| +
          β * ((qd d s V β X * |Bik d s V i k X|) * |Aik d ψ i k X|) := by
          rw [abs_mul, abs_mul, abs_of_pos hβ]; ring
  calc |vik d s V β ψ i k X|
      ≤ qd d s V β X * |Cik d ψ i k X| + β * ((qd d s V β X * |Bik d s V i k X|) * |Aik d ψ i k X|) := hv
    _ ≤ Q₀ * (2 * c * K₁ * W) + β * ((Q₀ * Vg + Mg) * (2 * c * K₁ * W)) := by
        gcongr
    _ = (Q₀ + β * (Q₀ * Vg + Mg)) * (2 * c * K₁) * W := by ring

theorem q84d_vik_integrable {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (i : Fin N) (k : Fin d) :
    Integrable (vik d s V β ψ i k : Config d N → ℝ) volume := by
  obtain ⟨M, hM0, hM⟩ := q84d_vik_bound hd hcrit hV hβ hN hψ
  have hint : Integrable (fun X : Config d N => M * ∑ l ∈ Finset.univ.erase i, wEnv s (X i) (X l)) volume :=
    (integrable_finsetSum _ fun l hl =>
      q84d_integrable_w_pair hd hcrit (Finset.ne_of_mem_erase hl).symm).const_mul M
  refine Integrable.mono' hint
    (q84d_measurable_vik hd hcrit hV ψ i k).aestronglyMeasurable ?_
  filter_upwards [q84d_ae_not_collision (N := N) (d := d) (by omega)] with X hX
  rw [Real.norm_eq_abs]
  exact hM i k X hX

end Bound

end HRS.Q84d

end
