import HRS.MS.SpecAux43

/-!
# S8P: Rayleigh bound `‖S‖²_{Σ^1} ≲ ∫ |D S|² + ∫ S²` (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_osc1_dir`: for the thermal data there is `K` such that for every Schwartz `S`
`oscNorm 1 S ^ 2 ≤ K (∑_j ∫ (D_j S)² + ∫ S²)`, `D_j S = ∂_j S - ½ ℓ_j S`.  Uses `s8p_osc1_bound`, the Hardy-type bound
`s8p_hardy_j` and `ℓ_j = -(βq) x_j + B_j` with `B` bounded (`x_j = (B_j - ℓ_j)/(βq)`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_osc1_dir (H : Mov2dTh d s β q ρ) (hE : Mov2eEll d ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : 𝓢R, oscNorm 1 S ^ 2 ≤
      K * ((∑ j : Fin d, ∫ x, s8p_Dj ρ S j x ^ 2) + ∫ x, S x ^ 2) := by
  obtain ⟨K0, hK0, hK0b⟩ := s8p_osc1_bound (d := d)
  obtain ⟨Df, hDf0, hDf⟩ := s8p_ell_bounds hE
  obtain ⟨B, hT, MB, hMB⟩ := s8p_therm_B H
  have hq' : 0 < β * q := mul_pos H.hβ H.hq
  have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
  set a1 : ℝ := 2 / (β * q) ^ 2 with ha1
  have ha10 : 0 < a1 := by positivity
  refine ⟨K0 * (1 + a1 * ((d : ℝ) * MB ^ 2 + 2 * d * Df) + a1 * 4 + 1 + (d : ℝ) * Df / 2 + 1), by positivity,
    fun S => ?_⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj := fun j => s8p_hardy_j hE hDf S j
  have IS2 : Integrable (fun x => S x ^ 2) := by
    have hSGD : Mov2eGD (S : Euc d → ℝ) := mov2e_schwartz_GD S
    exact (hSGD.mul hSGD).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  set I0 : ℝ := ∫ x, S x ^ 2 with hI0
  have hI0nn : 0 ≤ I0 := integral_nonneg fun x => sq_nonneg _
  set Dsum : ℝ := ∑ j : Fin d, ∫ x, s8p_Dj ρ S j x ^ 2 with hDsum
  set Psum : ℝ := ∑ j : Fin d, ∫ x, (fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2 with hPsum
  set Lsum : ℝ := ∑ j : Fin d, ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2 with hLsum
  have hDnn : 0 ≤ Dsum := Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
  have hPnn : 0 ≤ Psum := Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
  have hLnn : 0 ≤ Lsum := Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  -- Hardy summed
  have hH : Psum + (1 / 4) * Lsum ≤ Dsum + (d * Df / 2) * I0 := by
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => (hj j).2.2.2)
    have e1 : ∑ j : Fin d, ((∫ x, s8p_pd S j x ^ 2) + (1 / 4) * ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2) =
        Psum + (1 / 4) * Lsum := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e2 : ∑ j : Fin d, ((∫ x, s8p_Dj ρ S j x ^ 2) + (Df / 2) * ∫ x, S x ^ 2) =
        Dsum + (d * Df / 2) * I0 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e1, e2] at h1
    exact h1
  -- the coordinates
  have hx : ∀ j : Fin d, (∫ x, (x j * S x) ^ 2) ≤ a1 * (MB ^ 2 * I0 + ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2) := by
    intro j
    have Ib := (hj j).2.1
    have hpt : ∀ x : Euc d, (x j * S x) ^ 2 ≤ a1 * (MB ^ 2 * S x ^ 2 + s8p_ell ρ j x ^ 2 * S x ^ 2) := by
      intro x
      have hl : s8p_ell ρ j x = -(β * q) * x j + B x j := hT.ell_eq x j
      have hBj : |B x j| ≤ MB := by
        have := PiLp.norm_apply_le (B x) j
        rw [Real.norm_eq_abs] at this
        exact this.trans (hMB x)
      have hxj : x j = (B x j - s8p_ell ρ j x) / (β * q) := by
        have hβ0 := H.hβ.ne'
        have hq0 := H.hq.ne'
        rw [hl]; field_simp; ring
      have h2 : (B x j - s8p_ell ρ j x) ^ 2 ≤ 2 * (MB ^ 2 + s8p_ell ρ j x ^ 2) := by
        have : B x j ^ 2 ≤ MB ^ 2 := by
          calc B x j ^ 2 = |B x j| ^ 2 := (sq_abs _).symm
            _ ≤ MB ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hBj 2
        nlinarith [sq_nonneg (B x j + s8p_ell ρ j x)]
      calc (x j * S x) ^ 2 = (B x j - s8p_ell ρ j x) ^ 2 * S x ^ 2 / (β * q) ^ 2 := by
            have hβ0 := H.hβ.ne'
            have hq0 := H.hq.ne'
            rw [hxj]; field_simp
        _ ≤ 2 * (MB ^ 2 + s8p_ell ρ j x ^ 2) * S x ^ 2 / (β * q) ^ 2 := by
            gcongr
        _ = a1 * (MB ^ 2 * S x ^ 2 + s8p_ell ρ j x ^ 2 * S x ^ 2) := by
            rw [ha1]; ring
    have IR : Integrable (fun x => a1 * (MB ^ 2 * S x ^ 2 + s8p_ell ρ j x ^ 2 * S x ^ 2)) :=
      ((IS2.const_mul (MB ^ 2)).add Ib).const_mul a1
    have IL : Integrable (fun x => (x j * S x) ^ 2) := by
      refine Integrable.mono' IR ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.mul S.continuous).pow 2).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x
    calc ∫ x, (x j * S x) ^ 2 ≤ ∫ x, a1 * (MB ^ 2 * S x ^ 2 + s8p_ell ρ j x ^ 2 * S x ^ 2) :=
          integral_mono IL IR hpt
      _ = a1 * (MB ^ 2 * I0 + ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2) := by
          rw [integral_const_mul, integral_add (IS2.const_mul _) Ib, integral_const_mul]
  have hXsum : (∑ j : Fin d, ∫ x, (x j * S x) ^ 2) ≤ a1 * (d * MB ^ 2 * I0 + Lsum) := by
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hx j)
    have e1 : ∑ j : Fin d, a1 * (MB ^ 2 * I0 + ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2) =
        a1 * (d * MB ^ 2 * I0 + Lsum) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rwa [e1] at h1
  have hosc := hK0b S
  have hL4 : Lsum ≤ 4 * (Dsum + (d * Df / 2) * I0) := by nlinarith [hH, hPnn]
  have hP1 : Psum ≤ Dsum + (d * Df / 2) * I0 := by nlinarith [hH, hLnn]
  have hDf2 : 0 ≤ (d : ℝ) * Df / 2 := by positivity
  have hmb : 0 ≤ (d : ℝ) * MB ^ 2 := by positivity
  calc oscNorm 1 S ^ 2 ≤ K0 * (I0 + (∑ j : Fin d, ∫ x, (x j * S x) ^ 2) + Psum) := hosc
    _ ≤ K0 * (I0 + a1 * (d * MB ^ 2 * I0 + 4 * (Dsum + (d * Df / 2) * I0)) +
          (Dsum + (d * Df / 2) * I0)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        nlinarith [hXsum, hL4, hP1, mul_le_mul_of_nonneg_left hL4 ha10.le]
    _ ≤ K0 * ((1 + a1 * ((d : ℝ) * MB ^ 2 + 2 * d * Df) + a1 * 4 + 1 + (d : ℝ) * Df / 2 + 1) *
          (Dsum + I0)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        nlinarith [mul_nonneg ha10.le hmb, mul_nonneg ha10.le hDf2, mul_nonneg ha10.le hDnn,
          mul_nonneg ha10.le hI0nn, mul_nonneg hmb hI0nn, mul_nonneg hDf2 hI0nn, mul_nonneg hmb ha10.le,
          mul_nonneg (mul_nonneg ha10.le hmb) hI0nn, mul_nonneg (mul_nonneg ha10.le hDf2) hI0nn]
    _ = _ := by ring

end HRS.MS.Spec
