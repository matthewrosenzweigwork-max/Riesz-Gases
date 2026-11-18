import HRS.MS.SpecAux24
import HRS.MS.MovLinAux13

/-!
# S8P: compactness of the time-one map of the S6.2 semigroup (S8.7, packet E2)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  If a family `T` on `L²_0 = MovL2Zero ρ` has the short-time smoothing bound
`MovSmoothingBounds d s ρ (movA d s) c C T` (as the semigroup of `mov_linear` does), then `T 1` maps the unit ball into a ball of `Σ^a`
(`a = movA ≥ 1 > 0`), hence into a relatively compact set of `L² = Σ^0` (compact embedding, `SpecAux24`): `T 1` is compact.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovLin

variable {d : ℕ} {ρ : Euc d → ℝ}

theorem s8p_movA_pos (d : ℕ) (s : ℝ) : 0 < movA d s := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem s8p_T1_compact {s : ℝ} (T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) {c C : ℝ}
    (hb : MovSmoothingBounds d s ρ (movA d s) c C T) : IsCompactOperator (T 1) := by
  set a := movA d s with ha
  have ha0 : 0 < a := s8p_movA_pos d s
  set R : ℝ := |C| * (1 + 1 ^ (-a / 2)) * Real.exp (-c * 1) with hR
  have hj := s8p_osc_embed_compact (d := d) (show (0 : ℝ) < a from ha0)
  have hKc := hj.isCompact_closure_image_closedBall R
  set K' : Set (Lp ℝ 2 (volume : Measure (Euc d))) :=
    (mov2d_Phi d) '' closure (mov2d_j (d := d) ha0.le '' closedBall 0 R) with hK'
  have hK'c : IsCompact K' := hKc.image (mov2d_Phi d).continuous
  have hmem : ∀ v : MovL2Zero ρ, v ∈ closedBall (0 : MovL2Zero ρ) 1 →
      ((T 1 v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) ∈ K' := by
    intro v hv
    have hv1 : ‖v‖ ≤ 1 := by simpa using hv
    obtain ⟨hv0, hvn⟩ := movlin_norm_osc0 v
    have hv0' : MemOsc (a - a) (movFun v) := by rwa [sub_self]
    obtain ⟨hm, hn⟩ := hb.2 1 one_pos v hv0'
    rw [sub_self] at hn
    rw [hvn] at hn
    set w := T 1 v with hw
    have hwn : oscNorm a (movFun w) ≤ R := by
      refine hn.trans ?_
      calc C * (1 + 1 ^ (-a / 2)) * Real.exp (-c * 1) * ‖v‖
          ≤ |C| * (1 + 1 ^ (-a / 2)) * Real.exp (-c * 1) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (Real.exp_pos _).le)
              hv1 (norm_nonneg _) (by positivity)
        _ = R := by rw [hR, mul_one]
    set z : OscSpace d a := OscSpace.ofFun a (movFun w) with hz
    have hzn : ‖z‖ ≤ R := by rw [hz, OscSpace.norm_ofFun _ hm]; exact hwn
    have hjz : mov2d_j (d := d) ha0.le z = (mov2d_Phi d).symm (w : Lp ℝ 2 (volume : Measure (Euc d))) := by
      rw [hz, mov2d_j_ofFun ha0.le hm]
      exact (movlin_L2_osc (w : Lp ℝ 2 (volume : Measure (Euc d)))).2.2
    refine ⟨(mov2d_Phi d).symm (w : Lp ℝ 2 (volume : Measure (Euc d))), subset_closure ⟨z, ?_, hjz⟩, ?_⟩
    · simpa using hzn
    · simp
  have hcomp : IsCompact (((↑) : MovL2Zero ρ → Lp ℝ 2 (volume : Measure (Euc d))) ⁻¹' K') :=
    ((MovL2Zero ρ).subtypeₗᵢ.isometry.isClosedEmbedding).isCompact_preimage hK'c
  exact (isCompactOperator_iff_image_closedBall_subset_compact (T 1 : MovL2Zero ρ →ₗ[ℝ] MovL2Zero ρ)
    one_pos).2 ⟨_, hcomp, by rintro _ ⟨v, hv, rfl⟩; exact hmem v hv⟩

end HRS.MS.Spec
