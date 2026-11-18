import HRS.MS.SuppU8Aux7

/-!
# Worker U8 aux 8: pointwise bound of the singular integral
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

variable {d : ℕ}

theorem u8_pointwise (hd : 1 ≤ d) (α b : ℝ) (hα : 0 < α) (hb : 0 < b) (hbd : b < d)
    (m ℓ : ℕ) (hm : 1 ≤ m) (hαℓ : α < ℓ) (hℓm : ℓ ≤ 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (u : EuclideanSpace ℝ (Fin d) → E) (B : ℝ), 0 ≤ B → ContDiff ℝ ℓ u →
      (∀ z, ‖u z‖ ≤ B * (1 + ‖z‖) ^ (-b)) →
      (∀ z, ‖iteratedFDeriv ℝ ℓ u z‖ ≤ B * (1 + ‖z‖) ^ (-(b + ℓ))) →
      ∀ x, Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x) ∧
        ∫ y, ‖‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x‖ ≤
          C * B * (1 + ‖x‖) ^ (-(b + α)) ∧
        ‖∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x‖ ≤
          C * B * (1 + ‖x‖) ^ (-(b + α)) := by
  have : NeZero d := ⟨by omega⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨c4, hc4def⟩ : ∃ c4 : ℝ, c4 = 4 * m := ⟨_, rfl⟩
  have hc4 : 0 < c4 := by rw [hc4def]; positivity
  have hcd := u8_cd_pos hd
  have hℓα : 0 < (ℓ : ℝ) - α := by linarith
  have hdb : 0 < (d : ℝ) - b := by linarith
  obtain ⟨Afar, hAfar⟩ : ∃ Afar : ℝ, Afar = 2 ^ b * c4 ^ α / α +
      c4 ^ ((d : ℝ) + α) * 2 ^ (-((d : ℝ) - b)) / ((d : ℝ) - b) := ⟨_, rfl⟩
  have hAfar0 : 0 ≤ Afar := by rw [hAfar]; positivity
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℝ, Cn = 2 ^ (2 * m - ℓ) * (2 ^ (b + ℓ) * c4 ^ (-((ℓ : ℝ) - α))) *
      (u8_cd d / ((ℓ : ℝ) - α)) := ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = 2 ^ (2 * m) * ((4 * m + 1 : ℝ) * (u8_cd d * Afar)) :=
    ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  refine ⟨Cn + Cf, by positivity, ?_⟩
  intro E _ _ _ u B hB hu hu0 hu1 x
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = 1 + ‖x‖ := ⟨_, rfl⟩
  have hnpos : 0 < n := by rw [hn]; positivity
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = n / c4 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have h4ρ : 2 * m * ρ = n / 2 := by
    rw [hρdef, hc4def]; field_simp; ring
  obtain ⟨K, hK⟩ : ∃ K : EuclideanSpace ℝ (Fin d) → ℝ, K = fun y => ‖y‖ ^ (-((d : ℝ) + α)) :=
    ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : EuclideanSpace ℝ (Fin d) → E,
      f = fun y => K y • u8_fd (u8_L m y) u x := ⟨_, rfl⟩
  have hKnn : ∀ y, 0 ≤ K y := by intro y; rw [hK]; positivity
  have hfmeas : AEStronglyMeasurable f := by
    have h1 : Measurable K := by rw [hK]; exact measurable_norm.pow_const _
    have h2 : Continuous (fun y => u8_fd (u8_L m y) u x) := u8_L_cont m hu.continuous x
    rw [hf]
    exact h1.aestronglyMeasurable.smul h2.aestronglyMeasurable
  have hnormf : ∀ y, ‖f y‖ = K y * ‖u8_fd (u8_L m y) u x‖ := by
    intro y; rw [hf]; simp only [norm_smul, Real.norm_of_nonneg (hKnn y)]
  -- near bound
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = 2 ^ (2 * m - ℓ) * (B * (n / 2) ^ (-(b + ℓ))) := ⟨_, rfl⟩
  have hN0nn : 0 ≤ N0 := by rw [hN0]; positivity
  have hnear : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) ρ,
      ‖f y‖ ≤ N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d) := by
    intro y hy
    have hyn : ‖y‖ < ρ := by simpa using hy
    by_cases hy0 : y = 0
    · subst hy0
      have : f 0 = 0 := by
        rw [hf, hK]
        simp only [norm_zero]
        rw [Real.zero_rpow (by have : (0:ℝ) < d + α := by positivity
                               linarith), zero_smul]
      rw [this, norm_zero]
      positivity
    · have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hT := u8_fd_taylor ℓ (u8_L m y) ‖y‖ (B * (n / 2) ^ (-(b + ℓ))) u x hu
        (u8_L_norm m y) (by rw [u8_L_length]; exact hℓm) (by
          intro z hz
          rw [u8_L_length] at hz
          rw [mem_closedBall, dist_eq_norm] at hz
          have hzx : ‖z - x‖ ≤ 2 * m * ρ := by
            have : ((2 * m : ℕ) : ℝ) * ‖y‖ ≤ 2 * m * ρ := by
              push_cast; nlinarith
            linarith
          have h1 : n / 2 ≤ 1 + ‖z‖ := by
            have := norm_sub_norm_le x z
            rw [norm_sub_rev] at this
            rw [hn]; linarith
          have h2 : (1 + ‖z‖) ^ (-(b + ℓ)) ≤ (n / 2) ^ (-(b + ℓ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by
              have : (0 : ℝ) ≤ ℓ := by positivity
              linarith)
          calc ‖iteratedFDeriv ℝ ℓ u z‖ ≤ B * (1 + ‖z‖) ^ (-(b + ℓ)) := hu1 z
            _ ≤ B * (n / 2) ^ (-(b + ℓ)) := mul_le_mul_of_nonneg_left h2 hB)
      rw [u8_L_length] at hT
      rw [hnormf y]
      calc K y * ‖u8_fd (u8_L m y) u x‖
          ≤ K y * (2 ^ (2 * m - ℓ) * ‖y‖ ^ ℓ * (B * (n / 2) ^ (-(b + ℓ)))) :=
            mul_le_mul_of_nonneg_left hT (hKnn y)
        _ = N0 * (‖y‖ ^ ℓ * K y) := by rw [hN0]; ring
        _ = N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d) := by
            congr 1
            rw [hK]
            simp only
            rw [← Real.rpow_natCast, ← Real.rpow_add hyp]
            congr 1; ring
  -- far part
  obtain ⟨Fj, hFj⟩ : ∃ Fj : ℤ → EuclideanSpace ℝ (Fin d) → ℝ, Fj = fun j : ℤ =>
      (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b)) := ⟨_, rfl⟩
  have hFj' : ∀ j, Fj j = (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-((d : ℝ) + α)) * (1 + ‖x + (j : ℝ) • y‖) ^ (-b)) := fun j => by
    rw [hFj]
  have hFjnn : ∀ j y, 0 ≤ Fj j y := by
    intro j y; rw [hFj' j]; apply indicator_nonneg; intro y _; positivity
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = Finset.Icc (-((2 * m : ℕ) : ℤ)) ((2 * m : ℕ) : ℤ) :=
    ⟨_, rfl⟩
  have hfar : ∀ y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) ρ,
      ‖f y‖ ≤ 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y := by
    intro y hy
    have hcr := u8_fd_crude y (u8_L m y) u x (u8_L_mem m y)
    rw [u8_L_length] at hcr
    rw [hnormf y]
    have hyc : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ := hy
    have hFy : ∀ j, Fj j y = K y * (1 + ‖x + (j : ℝ) • y‖) ^ (-b) := by
      intro j; rw [hFj' j, hK]; exact indicator_of_mem hyc _
    calc K y * ‖u8_fd (u8_L m y) u x‖
        ≤ K y * (2 ^ (2 * m) * ∑ j ∈ S, ‖u (x + j • y)‖) := by
          rw [hS]; exact mul_le_mul_of_nonneg_left hcr (hKnn y)
      _ ≤ K y * (2 ^ (2 * m) * ∑ j ∈ S, B * (1 + ‖x + (j : ℝ) • y‖) ^ (-b)) := by
          apply mul_le_mul_of_nonneg_left _ (hKnn y)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro j _
          rw [← Int.cast_smul_eq_zsmul ℝ j y]
          exact hu0 _
      _ = 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y := by
          simp_rw [hFy, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, g = fun y =>
      (ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
        (fun y => N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d)) y + 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y :=
    ⟨_, rfl⟩
  have hdom : ∀ y, ‖f y‖ ≤ g y := by
    intro y
    rw [hg]
    have hfs : 0 ≤ 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y := by
      have : 0 ≤ ∑ j ∈ S, Fj j y := Finset.sum_nonneg (fun j _ => hFjnn j y)
      positivity
    by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) ρ
    · simp only [indicator_of_mem hy]
      linarith [hnear y hy]
    · have : (ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
          (fun y => N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d)) y = 0 := indicator_of_notMem hy _
      simp only [this, zero_add]
      exact hfar y hy
  obtain ⟨hnearI, hnearV⟩ := u8_near_int (d := d) hd ((ℓ : ℝ) - α) ρ hℓα hρ
  have hnearInt : Integrable ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
        (fun y => N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d))) :=
    (integrable_indicator_iff measurableSet_ball).2 (hnearI.const_mul N0)
  have hfarJ := fun j : ℤ => u8_far_term hd b α hb hbd hα x j n ρ hn hρ
  have hFjInt : ∀ j ∈ S, Integrable (Fj j) := by
    intro j _; rw [hFj' j]; exact (hfarJ j).1
  have hsumInt : Integrable (fun y => ∑ j ∈ S, Fj j y) := integrable_finset_sum S hFjInt
  have hfarSum : Integrable (fun y => 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y) :=
    hsumInt.const_mul _
  have hgInt : Integrable g := by
    rw [hg]; exact hnearInt.add hfarSum
  have hfInt : Integrable f := Integrable.mono' hgInt hfmeas (Filter.Eventually.of_forall hdom)
  have hnorm : ∫ y, ‖f y‖ ≤ ∫ y, g y :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hgInt
      (Filter.Eventually.of_forall hdom)
  have hgval : ∫ y, g y = N0 * (u8_cd d * (ρ ^ ((ℓ : ℝ) - α) / ((ℓ : ℝ) - α))) +
      2 ^ (2 * m) * B * ∑ j ∈ S, ∫ y, Fj j y := by
    rw [hg]
    show ∫ y, ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ).indicator
        (fun y => N0 * ‖y‖ ^ (((ℓ : ℝ) - α) - d)) y + 2 ^ (2 * m) * B * ∑ j ∈ S, Fj j y) = _
    rw [integral_add hnearInt hfarSum, integral_indicator measurableSet_ball,
      integral_const_mul, hnearV, integral_const_mul, integral_finsetSum S hFjInt]
  have hcard : (S.card : ℝ) = 4 * m + 1 := by
    rw [hS, Int.card_Icc]
    have : (((2 * m : ℕ) : ℤ) + 1 - -((2 * m : ℕ) : ℤ)).toNat = 4 * m + 1 := by omega
    rw [this]; push_cast; ring
  have hsum : ∑ j ∈ S, ∫ y, Fj j y ≤ (4 * m + 1) * (u8_cd d * (Afar * n ^ (-(b + α)))) := by
    calc ∑ j ∈ S, ∫ y, Fj j y ≤ ∑ j ∈ S, (u8_cd d * (Afar * n ^ (-(b + α)))) := by
          apply Finset.sum_le_sum; intro j _
          have := (hfarJ j).2
          rw [hFj' j]
          refine this.trans (le_of_eq ?_)
          rw [hρdef, hAfar, ← u8_alg_far d b α c4 n hc4 hnpos]
      _ = (4 * m + 1) * (u8_cd d * (Afar * n ^ (-(b + α)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have h1 : N0 * (u8_cd d * (ρ ^ ((ℓ : ℝ) - α) / ((ℓ : ℝ) - α))) = Cn * B * n ^ (-(b + α)) := by
    have key := u8_alg_near b α ℓ c4 n hc4 hnpos
    calc N0 * (u8_cd d * (ρ ^ ((ℓ : ℝ) - α) / ((ℓ : ℝ) - α)))
        = 2 ^ (2 * m - ℓ) * B * (u8_cd d / ((ℓ : ℝ) - α)) *
            ((n / 2) ^ (-(b + ℓ)) * (n / c4) ^ ((ℓ : ℝ) - α)) := by
          rw [hN0, hρdef]; ring
      _ = Cn * B * n ^ (-(b + α)) := by rw [key, hCn]; ring
  have h2 : 2 ^ (2 * m) * B * ∑ j ∈ S, ∫ y, Fj j y ≤ Cf * B * n ^ (-(b + α)) := by
    calc 2 ^ (2 * m) * B * ∑ j ∈ S, ∫ y, Fj j y
        ≤ 2 ^ (2 * m) * B * ((4 * m + 1) * (u8_cd d * (Afar * n ^ (-(b + α))))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Cf * B * n ^ (-(b + α)) := by rw [hCf]; ring
  have hfinal : ∫ y, ‖f y‖ ≤ (Cn + Cf) * B * (1 + ‖x‖) ^ (-(b + α)) := by
   calc ∫ y, ‖f y‖ ≤ ∫ y, g y := hnorm
    _ = _ := hgval
    _ ≤ Cn * B * n ^ (-(b + α)) + Cf * B * n ^ (-(b + α)) := by linarith
    _ = (Cn + Cf) * B * (1 + ‖x‖) ^ (-(b + α)) := by rw [hn]; ring
  have hres := (⟨hfInt, hfinal, (norm_integral_le_integral_norm _).trans hfinal⟩ :
    Integrable f ∧ ∫ y, ‖f y‖ ≤ (Cn + Cf) * B * (1 + ‖x‖) ^ (-(b + α)) ∧
      ‖∫ y, f y‖ ≤ (Cn + Cf) * B * (1 + ‖x‖) ^ (-(b + α)))
  subst hf
  subst hK
  exact hres

end HRS.U8
