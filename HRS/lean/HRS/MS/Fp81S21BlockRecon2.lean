import HRS.MS.Fp81S21BlockRecon

/-!
# S2.1(iii), packet 15d-1: block reconstruction coordinates

This coordinate formula uses the feature-space horizon `H` in `s101P` and
`s101Q`; only the second path evaluation uses the clipped unit clock.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9 HRS.MS.CovMeas

variable {d : ℕ} {m H : ℝ}

/- Exact exported type:
theorem fp81s21_blockRecon_coord (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex d) :
  OscDual.coord (r2PathAt (fp81s21_blockRecon hH a k y) t) α =
    inner ℝ (pcm y fp81s21_unitClockEndpoint) (s101P m H t α) +
      inner ℝ (pcm y (fp81s21_blockClock a k ⟨t, ht⟩)) (s101Q m H α)
-/

/-- Observation coordinates split into the terminal `P` feature and clipped-clock `Q` feature. -/
theorem fp81s21_blockRecon_coord (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex d) :
    OscDual.coord (r2PathAt (fp81s21_blockRecon hH a k y) t) α =
      inner ℝ (pcm y fp81s21_unitClockEndpoint) (s101P m H t α) +
        inner ℝ (pcm y (fp81s21_blockClock a k ⟨t, ht⟩)) (s101Q m H α) := by
  let x : KSpace d m H := pcm y fp81s21_unitClockEndpoint
  let z : KSpace d m H := pcm y (fp81s21_blockClock a k ⟨t, ht⟩)
  have hxmk : x = KSpace.mk x.A₀ x.A' x.B := rfl
  have hzmk : z = KSpace.mk z.A₀ z.A' z.B := rfl
  have hpath : r2PathAt (fp81s21_blockRecon hH a k y) t =
      x.evalA t - x.B + z.B := by
    unfold r2PathAt
    rw [dif_pos ht]
    change (show C(Icc (0 : ℝ) H, OscDual d m) from
      fp81s21_blockRecon hH a k y) ⟨t, ht⟩ = x.evalA t - x.B + z.B
    rw [fp81s21_blockRecon_apply]
  have hP : inner ℝ x (s101P m H t α) =
      OscDual.coord x.A₀ α +
        inner ℝ (s101e m α)
          (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s
            ∂(volume.restrict (Icc (0 : ℝ) H))) - OscDual.coord x.B α := by
    have hinner : inner ℝ x (s101P m H t α) =
        inner ℝ x.A₀ (s101e m α) +
          inner ℝ x.A' (s101Ind m H t (s101e m α)) +
          inner ℝ x.B (-(s101e m α)) := by
      rw [hxmk]
      unfold s101P
      exact s101_inner_mk x.A₀ x.B x.A' _ (s101e m α) (-(s101e m α))
    rw [hinner, real_inner_comm (s101e m α) x.A₀, s101_inner_e x.A₀ α,
      real_inner_comm (s101Ind m H t (s101e m α)) x.A', s101_inner_Ind,
      inner_neg_right, real_inner_comm (s101e m α) x.B, s101_inner_e x.B α]
    ring
  have hQ : inner ℝ z (s101Q m H α) = OscDual.coord z.B α := by
    rw [hzmk]
    unfold s101Q
    rw [s101_inner_mk, inner_zero_right, inner_zero_right, zero_add, zero_add]
    rw [real_inner_comm, s101_inner_e]
    rfl
  have heval : OscDual.coord (x.evalA t) α =
      OscDual.coord x.A₀ α +
        inner ℝ (s101e m α)
          (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s) := by
    unfold KSpace.evalA
    rw [min_eq_left ht.2, ← s101_inner_e]
    show inner ℝ (s101e m α)
        (x.A₀ + ∫ τ in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) τ) = _
    rw [inner_add_right, s101_inner_e]
  have hrestrict :
      (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s
        ∂(volume.restrict (Icc (0 : ℝ) H))) =
        ∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s := by
    rw [Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Icc_subset_Icc_right ht.2)]
  have hadd : ∀ u v : OscDual d m,
      OscDual.coord (u + v) α = OscDual.coord u α + OscDual.coord v α :=
    fun _ _ => rfl
  rw [hpath, hadd, s101_coord_sub, heval, ← hrestrict, hP, hQ]

#print axioms fp81s21_blockRecon_coord

end HRS.Fp81.S21

end
