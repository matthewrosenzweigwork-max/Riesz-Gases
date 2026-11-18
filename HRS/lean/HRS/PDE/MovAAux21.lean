import HRS.PDE.MovAAux20

/-!
# MOVA Aux21: the decomposition `movT_srcReg_decomp` for `0 < T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

set_option maxHeartbeats 1600000 in
theorem mova_srcReg_decomp_gen (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt₀ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt₀) (hT : 0 ≤ T)
    (hρtc' : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ρt r))
    (hPDE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, ρt r x = mova_pdeRHS D (ρ r) x) :
    ∃ Cι : ℝ, 0 ≤ Cι ∧ ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      (∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|) ∧
      ∀ L : ℝ, IsLipschitzVF L (mfeTransport D (ρ r)) →
        IsLipschitzVF (L + Cι * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
          (movT_uReg D M (ρ r)) := by
  obtain ⟨c₀, hc₀, hc₀low⟩ := mova_traj_c0 hT hρt (fun r hr x => h.pos r hr x)
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  have hΛ : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm 2 (ρ r) ≤ max Λ₂ 0 := fun r hr =>
    (hΛ₂ r hr).trans (le_max_left _ _)
  set Λ : ℝ := max Λ₂ 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  have hL1g := mova_L1_nonneg (periodicRiesz d D.s)
  have hε0 := mova_L1_nonneg (mova_kM D 0)
  set Kh : ℝ := (1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) *
    (2 * d * (Λ * Λ)) with hKh
  have hKh0 : 0 ≤ Kh := by rw [hKh]; positivity
  refine ⟨2 * Kh + d * Λ, by positivity, fun M hM r hr => ?_⟩
  have hεM := mova_L1_nonneg (mova_kM D M)
  have hεeq := mova_L1_kM_eq D M
  rw [← hεeq]
  have hρ := h.ck r hr
  have hdens := h.mf.density r hr
  have hpos := h.pos r hr
  have hV := h.V_reg
  have hκ := h.pos_temp
  have hρtc := hρtc' r hr
  haveI hQ := movT_QReg_isProb (N := N) D h M hr
  have hPDE := hPDE r hr
  constructor
  · intro X
    rw [mova_srcReg_centered (by omega) D h.gradient M hρ hdens hpos hV hκ hρtc X]
    have hk : ∀ x, |mova_k D M ρ ρt r x| ≤ Kh * mova_L1 (mova_kM D M) := fun x => by
      have := mova_abs_k_le D hM hρ hdens hpos hV hκ hρtc hPDE (hΛ r hr) hc₀ (hc₀low r hr) x
      rw [hKh]
      calc _ ≤ _ := this
        _ = _ := by ring
    have h1 : |∑ i, mova_k D M ρ ρt r (X i)| ≤ N * (Kh * mova_L1 (mova_kM D M)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hk (X i)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : |∫ Y, ∑ i, mova_k D M ρ ρt r (Y i) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)| ≤
        N * (Kh * mova_L1 (mova_kM D M)) := by
      have := norm_integral_le_of_norm_le_const (μ := movT_Q (b15c_gReg d D.s M) D N ρ r)
        (f := fun Y : Config d N => ∑ i, mova_k D M ρ ρt r (Y i))
        (C := N * (Kh * mova_L1 (mova_kM D M)))
        (Filter.Eventually.of_forall fun Y => by
          rw [Real.norm_eq_abs]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hk (Y i)).trans ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
      simpa using this
    calc _ ≤ |∑ i, mova_k D M ρ ρt r (X i)| + |∫ Y, ∑ i, mova_k D M ρ ρt r (Y i)
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)| := abs_sub _ _
      _ ≤ 2 * (N * (Kh * mova_L1 (mova_kM D M))) := by linarith
      _ ≤ (2 * Kh + d * Λ) * N * mova_L1 (mova_kM D M) := by
          have : 0 ≤ (d : ℝ) * Λ * N * mova_L1 (mova_kM D M) := by positivity
          nlinarith
  · intro L hL
    have := mova_lip_uReg D M hρ (hΛ r hr) hL
    refine mova_isLipschitzVF_mono ?_ this
    have : 0 ≤ (2 * Kh) * mova_L1 (mova_kM D M) := by positivity
    nlinarith

theorem mova_srcReg_decomp_pos (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) :
    ∃ Cι : ℝ, 0 ≤ Cι ∧ ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      (∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|) ∧
      ∀ L : ℝ, IsLipschitzVF L (mfeTransport D (ρ r)) →
        IsLipschitzVF (L + Cι * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
          (movT_uReg D M (ρ r)) :=
  mova_srcReg_decomp_gen hN h hρt hT.le (fun r hr => mova_cont_ρt_slice hρt hr)
    (mova_pde_pointwise D h.gradient h.V_reg hT h.mf hρt)

end HRS
