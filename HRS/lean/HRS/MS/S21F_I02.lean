import HRS.MS.S21F_I02b

/-!
# S21F, packet R26-T3.I02: cosine synthesis into the complete window space

`S z (u) = ∑_n cos_n(u) (1+n²)^{-3/8} · slice_n z` converges in `B_m` uniformly in `u` (Weierstrass M-test, with
`‖slice_n z‖` square-summable and `∑ w_n² < ∞` through the Hölder estimate), so `S z ∈ C([0,T]; B_m)`; `S` is linear with
`‖S‖ ≤ A (∑ w²)^{1/2}`.  The pointwise reconstruction alone would not give the `C([0,T])` norm.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

/-- the `n`-th term of the synthesis -/
def s21f_term (T : ℝ) (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z : SeqL2) (u : ℝ) : OscDual d m :=
  (r26t3_cosine T n u * s21f_w n) • s21f_slice e n z

theorem s21f_term_norm (hT : 0 < T) (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z : SeqL2) (u : ℝ) :
    ‖s21f_term (m := m) T e n z u‖ ≤
      ((Real.sqrt T)⁻¹ + Real.sqrt (2 / T)) * (s21f_w n * ‖s21f_slice (m := m) e n z‖) := by
  unfold s21f_term
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (s21f_w_pos n)]
  have := s21f_cos_bound hT n u
  have hw := s21f_w_pos n
  have h3 := mul_nonneg (sub_nonneg.2 this) (mul_nonneg hw.le (norm_nonneg (s21f_slice (m := m) e n z)))
  nlinarith [h3]

theorem s21f_term_summable (hT : 0 < T) (e : ℕ ≃ ℕ × MultiIndex d) (z : SeqL2) (u : ℝ) :
    Summable fun n => ‖s21f_term (m := m) T e n z u‖ :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => s21f_term_norm hT e n z u)
    ((s21f_holder (m := m) e z).1.mul_left _)

theorem s21f_synth_exists (hT : 0 < T) (e : ℕ ≃ ℕ × MultiIndex d) :
    ∃ S : SeqL2 →L[ℝ] OscPath d m T, ∃ C : ℝ, 0 < C ∧ ‖S‖ ≤ C ∧
      ∀ (z : SeqL2) (u : Set.Icc (0 : ℝ) T) (α : MultiIndex d),
        OscDual.coord (OscPath.at' (S z) u) α =
          ∑' n : ℕ, r26t3_cosine T n u * s21f_w n * SeqL2.coord z (e.symm (n, α)) := by
  set A : ℝ := (Real.sqrt T)⁻¹ + Real.sqrt (2 / T) with hA
  have hA0 : 0 ≤ A := by positivity
  have hcont : ∀ z : SeqL2, Continuous fun u : Set.Icc (0 : ℝ) T => ∑' n, s21f_term (m := m) T e n z u := by
    intro z
    refine continuous_tsum (u := fun n => A * (s21f_w n * ‖s21f_slice (m := m) e n z‖)) (fun n => ?_)
      ((s21f_holder (m := m) e z).1.mul_left A) (fun n u => s21f_term_norm hT e n z u)
    unfold s21f_term
    exact ((s21f_cos_cont T n).comp continuous_subtype_val |>.mul continuous_const).smul continuous_const
  let P : SeqL2 → C(Set.Icc (0 : ℝ) T, OscDual d m) := fun z =>
    ⟨fun u => ∑' n, s21f_term (m := m) T e n z u, hcont z⟩
  have hsum : ∀ z u, Summable fun n => s21f_term (m := m) T e n z u := fun z u =>
    (s21f_term_summable hT e z u).of_norm
  have hadd : ∀ z w, P (z + w) = P z + P w := fun z w => by
    ext u
    show ∑' n, s21f_term (m := m) T e n (z + w) u = ∑' n, s21f_term (m := m) T e n z u +
      ∑' n, s21f_term (m := m) T e n w u
    rw [← (hsum z u).tsum_add (hsum w u)]
    refine tsum_congr fun n => ?_
    unfold s21f_term
    rw [s21f_slice_add, smul_add]
  have hsmul : ∀ (c : ℝ) z, P (c • z) = c • P z := fun c z => by
    ext u
    show ∑' n, s21f_term (m := m) T e n (c • z) u = c • ∑' n, s21f_term (m := m) T e n z u
    rw [← tsum_const_smul'' c]
    refine tsum_congr fun n => ?_
    unfold s21f_term
    rw [s21f_slice_smul, smul_comm]
  have hbound : ∀ z, ‖(P z : C(Set.Icc (0 : ℝ) T, OscDual d m))‖ ≤
      (A * Real.sqrt (∑' n : ℕ, s21f_w n ^ 2)) * ‖z‖ := by
    intro z
    refine ContinuousMap.norm_le _ (by positivity) |>.2 fun u => ?_
    show ‖∑' n, s21f_term (m := m) T e n z u‖ ≤ _
    obtain ⟨hs, hh⟩ := s21f_holder (m := m) e z
    calc ‖∑' n, s21f_term (m := m) T e n z u‖ ≤ ∑' n, ‖s21f_term (m := m) T e n z u‖ :=
          norm_tsum_le_tsum_norm (s21f_term_summable hT e z u)
      _ ≤ ∑' n, A * (s21f_w n * ‖s21f_slice (m := m) e n z‖) :=
          (s21f_term_summable hT e z u).tsum_le_tsum (fun n => s21f_term_norm hT e n z u) (hs.mul_left A)
      _ = A * ∑' n, s21f_w n * ‖s21f_slice (m := m) e n z‖ := tsum_mul_left
      _ ≤ A * (Real.sqrt (∑' n : ℕ, s21f_w n ^ 2) * ‖z‖) := mul_le_mul_of_nonneg_left hh hA0
      _ = _ := by ring
  let L : SeqL2 →ₗ[ℝ] OscPath d m T :=
    { toFun := fun z => (P z : OscPath d m T)
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨L.mkContinuous (A * Real.sqrt (∑' n : ℕ, s21f_w n ^ 2)) hbound,
    A * Real.sqrt (∑' n : ℕ, s21f_w n ^ 2) + 1, by positivity, ?_, fun z u α => ?_⟩
  · exact (LinearMap.mkContinuous_norm_le _ (by positivity) _).trans (by linarith)
  · show OscDual.coord (∑' n, s21f_term (m := m) T e n z u) α = _
    have := (HRS.MS.R2Interp.s102_coordCLM (d := d) (m := m) α).map_tsum (hsum z u)
    refine this.trans (tsum_congr fun n => ?_)
    show OscDual.coord ((r26t3_cosine T n u * s21f_w n) • s21f_slice (m := m) e n z) α = _
    rw [OscDual.coord_smul, s21f_slice_coord]

theorem r26t3_cosine_synthesis (p : Parameters) :
    ∃ S : SeqL2 →L[ℝ] Window p, ∃ C : ℝ, 0 < C ∧ ‖S‖ ≤ C ∧
      ∀ z u α, OscDual.coord (OscPath.at' (S z) u) α =
        ∑' n : ℕ, r26t3_cosine p.T n u * (1 + (n : ℝ) ^ 2) ^ (-(3 / 8 : ℝ)) *
          SeqL2.coord z ((r26t3_feature_enum p.d).symm (n, α)) :=
  s21f_synth_exists p.hT (r26t3_feature_enum p.d)

end HRS.MS.R26T3
