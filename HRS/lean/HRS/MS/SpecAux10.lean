import HRS.MS.SpecAux9

/-!
# S8P: PSD-root relative bound, `ℝ≥0∞` form (S8.7, packet C1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

`s8p_psd_root_relative`: `S` symmetric, `⟨S x, x⟩ ≥ 0`, `∑ ‖S b_j‖² < ∞`, `e_j > 0`, `∑ e_j² < ∞`:
`∑_j ‖S b_j - e_j b_j‖² ≤ 4 ∑_{i,j} (⟨S b_i, S b_j⟩ - e_i² δ_{ij})²/(e_i² + e_j²)` in `ℝ≥0∞`.
With `Σ = S²` (so `Σ_{ij} = ⟨S b_i, S b_j⟩`) and `D = E²` this is `‖Σ^{1/2} - D^{1/2}‖²_HS ≤ 4 ∑ Δ_{ij}²/(d_i+d_j)`.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*}

theorem s8p_psd_root_relative [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hS : ∀ x, 0 ≤ ⟪S x, x⟫) (e : ι → ℝ) (he : ∀ i, 0 < e i) (b : HilbertBasis ι ℝ H)
    (hSHS : Summable fun j => ‖S (b j)‖ ^ 2) (heHS : Summable fun j => e j ^ 2) :
    ∑' j, ENNReal.ofReal (‖S (b j) - e j • b j‖ ^ 2) ≤
      4 * ∑' p : ι × ι, ENNReal.ofReal
        ((⟪S (b p.1), S (b p.2)⟫ - (if p.1 = p.2 then e p.1 ^ 2 else 0)) ^ 2 /
          (e p.1 ^ 2 + e p.2 ^ 2)) := by
  set Z : ι × ι → ℝ := fun p =>
    (⟪s8p_xi S e b p.1, s8p_xi S e b p.2⟫ + (e p.1 + e p.2) * s8p_x S e b p.1 p.2) /
      (e p.1 + e p.2) with hZ
  have hpos : ∀ p : ι × ι, 0 < e p.1 + e p.2 := fun p => by linarith [he p.1, he p.2]
  have hZeq : ∀ p : ι × ι, Z p = (⟪S (b p.1), S (b p.2)⟫ - (if p.1 = p.2 then e p.1 ^ 2 else 0)) /
      (e p.1 + e p.2) := by
    intro p
    simp only [hZ]
    rw [s8p_delta_eq S hSs e b p.1 p.2]
  have hle : ∀ p : ι × ι, Z p ^ 2 ≤
      (⟪S (b p.1), S (b p.2)⟫ - (if p.1 = p.2 then e p.1 ^ 2 else 0)) ^ 2 /
        (e p.1 ^ 2 + e p.2 ^ 2) := by
    intro p
    rw [hZeq, div_pow]
    refine div_le_div_of_nonneg_left (sq_nonneg _)
      (add_pos (pow_pos (he p.1) 2) (pow_pos (he p.2) 2)) ?_
    nlinarith [he p.1, he p.2]
  have hmono : ∑' p : ι × ι, ENNReal.ofReal (Z p ^ 2) ≤ ∑' p : ι × ι, ENNReal.ofReal
      ((⟪S (b p.1), S (b p.2)⟫ - (if p.1 = p.2 then e p.1 ^ 2 else 0)) ^ 2 /
        (e p.1 ^ 2 + e p.2 ^ 2)) :=
    ENNReal.tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal (hle p)
  by_cases htop : ∑' p : ι × ι, ENNReal.ofReal (Z p ^ 2) = ⊤
  · have : ∑' p : ι × ι, ENNReal.ofReal
        ((⟪S (b p.1), S (b p.2)⟫ - (if p.1 = p.2 then e p.1 ^ 2 else 0)) ^ 2 /
          (e p.1 ^ 2 + e p.2 ^ 2)) = ⊤ := top_le_iff.1 (htop ▸ hmono)
    rw [this]; simp
  · have hZs : Summable fun p : ι × ι => Z p ^ 2 := by
      have := ENNReal.summable_toReal htop
      refine this.congr fun p => ?_
      exact ENNReal.toReal_ofReal (sq_nonneg _)
    have hA : Summable fun j => ‖s8p_xi S e b j‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
        ((hSHS.mul_left 2).add (heHS.mul_left 2))
      have h1 : ‖s8p_xi S e b j‖ ≤ ‖S (b j)‖ + e j := by
        unfold s8p_xi
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, b.orthonormal.1 j, Real.norm_eq_abs, abs_of_pos (he j)]
        simp
      calc ‖s8p_xi S e b j‖ ^ 2 ≤ (‖S (b j)‖ + e j) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * ‖S (b j)‖ ^ 2 + 2 * e j ^ 2 := by nlinarith [sq_nonneg (‖S (b j)‖ - e j)]
    have hcore := s8p_psd_root_core S hSs hS e he b hA hZs
    have hL : ∑' j, ENNReal.ofReal (‖S (b j) - e j • b j‖ ^ 2) =
        ENNReal.ofReal (∑' j, ‖s8p_xi S e b j‖ ^ 2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hA]; rfl
    have hR : ∑' p : ι × ι, ENNReal.ofReal (Z p ^ 2) = ENNReal.ofReal (∑' p, Z p ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hZs).symm
    rw [hL]
    calc ENNReal.ofReal (∑' j, ‖s8p_xi S e b j‖ ^ 2)
        ≤ ENNReal.ofReal (4 * ∑' p, Z p ^ 2) := ENNReal.ofReal_le_ofReal hcore
      _ = 4 * ∑' p : ι × ι, ENNReal.ofReal (Z p ^ 2) := by
        rw [hR, ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ _ := by gcongr

end HRS.MS.Spec
