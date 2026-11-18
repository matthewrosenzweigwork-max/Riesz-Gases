/-
# HRS.Equilibrium.TaylorAux8 — Lemma 4.7 `M:R:lem:Taylor` (packet TAYLOR)

`integrated_taylor_remainder_proof` restates `HRS.integrated_taylor_remainder` verbatim (the
statement lives in `PoleCavity.lean`, which cannot import this file: the proof uses Lemma 4.4 in its
proved form `product_moment_transfer_proof`, downstream of `PoleCavity.lean`).

Proof route (TeX lines 4307-4350), with `N = ν⁸`, `H = 2ν⁵`, `M = ν³`:
1. pointwise: `H(v) ≤ H(v_H) + (v - v_H)`, `H(v_H) ≤ e^K v_H²` (`taylor_pointwise`);
   hence the remainder is `≤ B₁(Y) + λ ∑_{j≠i} T_{H,x}(y_j)`;
2. `‖B₁‖_{L^{2q}(μ^n)} ≤ C Θ(N,H) ≤ C ν^{-5}`: Jensen in `y` and the bounded-summand Bernstein
   inequality for `v_{Y,H}(y)` (`taylor_B1_bound`, `taylor_field_moment`);
3. `‖λ ∑ T(y_j)‖_{L^{2q}(μ^n)} ≤ C ν^{-5}`: cap `T` at `M = ν³`, Bernstein for the capped part,
   Minkowski and the `6q`-th moment (Young's inequality) for the remainder (`taylor_sum_bound`);
4. transfer (Lemma 4.4 with loss `N^{1/16}`): `‖·‖_{L²(P)} ≤ C N^{1/16} ν^{-5} = C N^{-9/16}`.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.TaylorAux7

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

open HRS.TaylorAux

theorem taylor_rpow_ids (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 * (((taylorNu N) ^ 5)⁻¹) ^ 2 = (N : ℝ) ^ (-(9 / 8 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e1 : ((N : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have e2 : (((taylorNu N) ^ 5)⁻¹) ^ 2 = (N : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have : (taylorNu N) ^ 5 = (N : ℝ) ^ ((5 : ℝ) / 8) := by
      unfold taylorNu
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [this, ← Real.rpow_neg hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  rw [e1, e2, ← Real.rpow_add hN0]
  norm_num

theorem integrated_taylor_remainder_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ t' ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ f ∈ ({fun _ => 1,
          fun y => Real.exp (-(t * (β / N)) * gPlus d s c (x - y)),
          fun y => gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))} :
            Set (Torus d → ℝ)),
        ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂(critPole d s c β ρ N x t') ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨q, hq2, C0, hC0⟩ := product_moment_transfer_proof hd hcrit β hβ ρ hρ c hc (1 / 16) (by norm_num)
  obtain ⟨K, hK0, hKl⟩ := taylor_field_lower hd hcrit β hβ ρ hρ c hc
  obtain ⟨Cb, hCb0, hCb⟩ := taylor_Lp_total hd hcrit β hβ ρ hρ c hc q (by omega) hK0
  refine ⟨(max C0 0 * Cb) ^ 2, fun N hN x t ht t' ht' i f hf => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  set P : Measure (Config d (N - 1)) := critPole d s c β ρ N x t' with hP
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ with hPm
  -- general claim for a dominating test `φ`
  have key : ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
      ∀ g : Torus d → ℝ, (∀ y, g y ≤ φ y) →
      ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂P ≤
        ENNReal.ofReal ((max C0 0 * Cb) ^ 2 * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
    intro φ hφ g hgφ
    have hφm : Measurable φ := by
      rcases hφ with rfl | rfl
      · exact measurable_const
      · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
          (measurable_const.sub measurable_id)
    have hφ0 : ∀ y, 0 ≤ φ y := by
      rcases hφ with rfl | rfl
      · intro y; exact zero_le_one
      · intro y; exact hc _
    set B : (Config d (N - 1)) → ℝ≥0∞ := fun Y => (∫⁻ y, ENNReal.ofReal (φ y) *
        ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂(withDensityReal ρ)) +
        ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
          taylorT (withDensityReal ρ) φ (taylorG d s c H) (Y j) with hB
    have hBm : Measurable B := by
      refine Measurable.add ?_ ?_
      · refine Measurable.lintegral_prod_right' (f := fun p : Config d (N - 1) × Torus d =>
          ENNReal.ofReal (φ p.2) * ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H p.1 p.2 ^ 2)) ?_
        exact (hφm.comp measurable_snd).ennreal_ofReal.mul
          ((measurable_const.mul
            ((taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H).pow_const 2)).ennreal_ofReal)
      · exact (Finset.measurable_sum _ fun j _ =>
          (taylor_measurable_T hφm (measurable_taylorG hd hs0 hsd c H (s := s))).comp
            (measurable_pi_apply j)).const_mul _
    have hpt : ∀ Y, ∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
        ∂(withDensityReal ρ) ≤ B Y := fun Y =>
      taylor_pointwise hd hcrit β hβ ρ hρ c hc hK0 hKl N H hH i φ g hφm hφ0 hgφ Y
    have hLp := hCb N hN i x φ hφ
    -- the `L^{2q}(Pm)` bound on `B`
    have hb : ∫⁻ a, B a ^ (2 * q) ∂Pm ≤ (ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ (2 * q) := by
      have h1 := taylorLp_rpow hp0 B (P := Pm)
      have h2 : taylorLp Pm ((2 * q : ℕ) : ℝ) B ≤ ENNReal.ofReal (Cb * (ν ^ 5)⁻¹) := hLp
      have h3 := ENNReal.rpow_le_rpow h2 hp0.le
      rw [h1] at h3
      simp only [ENNReal.rpow_natCast] at h3
      exact h3
    have hwrap := taylor_transfer_wrap P Pm q (by omega) (ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)))
      (fun Y hY => (hC0 N hN).2 x t' ht' Y hY) B hBm _ hb
    calc ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (g y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂P ≤ ∫⁻ Y, B Y ^ 2 ∂P :=
          lintegral_mono fun Y => pow_le_pow_left' (hpt Y) 2
      _ ≤ (ENNReal.ofReal (C0 * (N : ℝ) ^ ((1 : ℝ) / 16)) * ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ 2 := hwrap
      _ ≤ (ENNReal.ofReal (max C0 0 * (N : ℝ) ^ ((1 : ℝ) / 16)) * ENNReal.ofReal (Cb * (ν ^ 5)⁻¹)) ^ 2 := by
          refine pow_le_pow_left' (mul_le_mul' ?_ le_rfl) 2
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _))
      _ = ENNReal.ofReal ((max C0 0 * (N : ℝ) ^ ((1 : ℝ) / 16) * (Cb * (ν ^ 5)⁻¹)) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
      _ = ENNReal.ofReal ((max C0 0 * Cb) ^ 2 * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
          congr 1
          rw [← taylor_rpow_ids N (by omega)]
          ring
  have hmem1 : (fun _ => (1 : ℝ)) ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)) := by
    simp
  have hmem2 : (fun y => gPlus d s c (x - y)) ∈
      ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)) := by simp
  have hE : ∀ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ≤ 1 := by
    intro y
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t * (β / N) := mul_nonneg ht.1 (by positivity)
    have := hc (x - y)
    have : 0 ≤ gPlus d s c (x - y) := this
    nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · exact key _ hmem1 _ fun y => le_rfl
  · exact key _ hmem1 _ fun y => hE y
  · refine key _ hmem2 _ fun y => ?_
    have h0 : 0 ≤ gPlus d s c (x - y) := hc _
    have := Real.exp_pos (-(t * (β / N)) * gPlus d s c (x - y))
    calc gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
        ≤ gPlus d s c (x - y) * 1 := mul_le_mul_of_nonneg_left (hE y) h0
      _ = _ := mul_one _

example := (@integrated_taylor_remainder_proof : type_of% @integrated_taylor_remainder)

end HRS
