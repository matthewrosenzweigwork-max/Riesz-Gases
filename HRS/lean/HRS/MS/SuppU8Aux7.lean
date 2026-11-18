import HRS.MS.SuppU8Aux6

/-!
# Worker U8 aux 7: rpow algebra and the pointwise bound of the singular integral
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

theorem u8_rpow_div (n c e : ℝ) (hn : 0 ≤ n) (hc : 0 < c) : (n / c) ^ e = n ^ e * c ^ (-e) := by
  rw [Real.div_rpow hn hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]

theorem u8_alg_near (b α : ℝ) (ℓ : ℕ) (c4 n : ℝ) (hc4 : 0 < c4) (hn : 0 < n) :
    (n / 2) ^ (-(b + ℓ)) * (n / c4) ^ ((ℓ : ℝ) - α) =
      (2 ^ (b + ℓ) * c4 ^ (-((ℓ : ℝ) - α))) * n ^ (-(b + α)) := by
  rw [u8_rpow_div n 2 _ hn.le (by norm_num), u8_rpow_div n c4 _ hn.le hc4, neg_neg]
  have : n ^ (-(b + ℓ)) * n ^ ((ℓ : ℝ) - α) = n ^ (-(b + α)) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  calc n ^ (-(b + ℓ)) * 2 ^ (b + ℓ) * (n ^ ((ℓ : ℝ) - α) * c4 ^ (-((ℓ : ℝ) - α)))
      = (n ^ (-(b + ℓ)) * n ^ ((ℓ : ℝ) - α)) * (2 ^ (b + ℓ) * c4 ^ (-((ℓ : ℝ) - α))) := by ring
    _ = _ := by rw [this]; ring

theorem u8_alg_far (d : ℕ) (b α : ℝ) (c4 n : ℝ) (hc4 : 0 < c4) (hn : 0 < n) :
    2 ^ b * n ^ (-b) * ((n / c4) ^ (-α) / α) +
      (n / c4) ^ (-((d : ℝ) + α)) * ((n / 2) ^ ((d : ℝ) - b) / ((d : ℝ) - b)) =
    (2 ^ b * c4 ^ α / α + c4 ^ ((d : ℝ) + α) * 2 ^ (-((d : ℝ) - b)) / ((d : ℝ) - b)) *
      n ^ (-(b + α)) := by
  rw [u8_rpow_div n c4 _ hn.le hc4, u8_rpow_div n c4 _ hn.le hc4, u8_rpow_div n 2 _ hn.le (by norm_num)]
  simp only [neg_neg]
  have h1 : n ^ (-b) * n ^ (-α) = n ^ (-(b + α)) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  have h2 : n ^ (-((d : ℝ) + α)) * n ^ ((d : ℝ) - b) = n ^ (-(b + α)) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  calc 2 ^ b * n ^ (-b) * (n ^ (-α) * c4 ^ α / α) +
        n ^ (-((d : ℝ) + α)) * c4 ^ ((d : ℝ) + α) *
          (n ^ ((d : ℝ) - b) * 2 ^ (-((d : ℝ) - b)) / ((d : ℝ) - b))
      = (2 ^ b * c4 ^ α / α) * (n ^ (-b) * n ^ (-α)) +
        (c4 ^ ((d : ℝ) + α) * 2 ^ (-((d : ℝ) - b)) / ((d : ℝ) - b)) *
          (n ^ (-((d : ℝ) + α)) * n ^ ((d : ℝ) - b)) := by ring
    _ = _ := by rw [h1, h2]; ring

end HRS.U8
