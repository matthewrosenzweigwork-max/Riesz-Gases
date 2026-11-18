import HRS.Commutator.Torus.TEXTAux1
import HRS.Commutator.Whole.ExternalAuxHLS12
import HRS.Commutator.Whole.ExternalAuxMult4

/-!
# T-EXT-A helpers, part 3: pointwise bounds for periodisations

For `f : ℝ^d → ℝ` with `|f z| ≤ T |z|^{-M}` (`M > d`), the periodisation at a point `x = mk c`,
`c ∈ [-1/2,1/2]^d`, is bounded by `|f c|` plus a tail `≲ T`.  Also: integrability of the periodisation
of a signed integrable function with summable translates.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_toEuc_norm_le (m : Lattice d) : ‖Lattice.toEuc m‖ ≤ ∑ i, |(m i : ℝ)| := by
  have := Whole.cmxHLS_norm_toLp_le (d := d) (fun i => (m i : ℝ))
  exact this

lemma text_lattice_lower (c : Euc d) (hc : ∀ i, |c i| ≤ 1 / 2) (m : Lattice d) :
    ‖Lattice.toEuc m‖ ≤ 2 * d * ‖c + Lattice.toEuc m‖ := by
  refine (text_toEuc_norm_le m).trans ?_
  have hi : ∀ i, |(m i : ℝ)| ≤ 2 * ‖c + Lattice.toEuc m‖ := by
    intro i
    have h1 : |(c + Lattice.toEuc m) i| ≤ ‖c + Lattice.toEuc m‖ := by
      simpa using PiLp.norm_apply_le (c + Lattice.toEuc m) i
    by_cases hmi : m i = 0
    · rw [hmi]; simp only [Int.cast_zero, abs_zero]
      exact mul_nonneg (by norm_num) (norm_nonneg _)
    · have h2 : (1 : ℝ) ≤ |(m i : ℝ)| := by
        have : (1 : ℤ) ≤ |m i| := Int.one_le_abs hmi
        have h3 : ((1 : ℤ) : ℝ) ≤ ((|m i| : ℤ) : ℝ) := by exact_mod_cast this
        simpa using h3
      have h4 : (m i : ℝ) = (c + Lattice.toEuc m) i - c i := by
        simp [Lattice.toEuc]
      have h5 : |(m i : ℝ)| ≤ |(c + Lattice.toEuc m) i| + |c i| := by
        rw [h4]; exact abs_sub _ _
      have := hc i
      linarith
  calc ∑ i, |(m i : ℝ)| ≤ ∑ _i : Fin d, 2 * ‖c + Lattice.toEuc m‖ :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 2 * d * ‖c + Lattice.toEuc m‖ := by simp; ring

/-- Pointwise bound for the periodisation of a function with `|f z| ≤ T |z|^{-M}`. -/
lemma text_perio_bound (hd : 1 ≤ d) {f : Euc d → ℝ} {T : ℝ} {M : ℕ} (hT : 0 ≤ T)
    (hM : d < M) (hf : ∀ z, z ≠ 0 → |f z| ≤ T * ‖z‖ ^ (-(M : ℝ)))
    (c : Euc d) (hc : ∀ i, |c i| ≤ 1 / 2) :
    |perio f (Torus.mk c)| ≤ |f c| +
      T * ((2 * d) ^ M * ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-(M : ℝ))) := by
  have hMr : (d : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hS := tpos_summable_rpow (d := d) hMr
  set S := ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-(M : ℝ)) with hSdef
  set L : ℝ := T * (2 * d) ^ M with hL
  have hL0 : 0 ≤ L := by positivity
  let B : Lattice d → ℝ := fun m =>
    (if m = 0 then |f c| else 0) + L * ‖Lattice.toEuc m‖ ^ (-(M : ℝ))
  have hB : HasSum B (|f c| + L * S) :=
    (hasSum_ite_eq (0 : Lattice d) (|f c|)).add (hS.hasSum.mul_left L)
  rw [tpos_perio_mk]
  have hbound : ∀ m : Lattice d, ‖f (c + Lattice.toEuc m)‖ ≤ B m := by
    intro m
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp only [B, h0, add_zero, if_true]
      have : 0 ≤ L * ‖(0 : Euc d)‖ ^ (-(M : ℝ)) := by positivity
      linarith
    · simp only [B, hm, if_false, zero_add]
      have hmpos : 0 < ‖Lattice.toEuc m‖ := by
        rw [norm_pos_iff]
        intro h0
        apply hm
        funext i
        have := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
        simp [Lattice.toEuc] at this
        simpa using this
      have hd2 : (0 : ℝ) < 2 * d := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hlow := text_lattice_lower c hc m
      have hcm : 0 < ‖c + Lattice.toEuc m‖ := by
        by_contra hneg
        push Not at hneg
        have : ‖c + Lattice.toEuc m‖ = 0 := le_antisymm hneg (norm_nonneg _)
        rw [this] at hlow
        linarith
      have hne : c + Lattice.toEuc m ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hcm; exact lt_irrefl _ hcm
      have h1 := hf _ hne
      have h2 : ‖c + Lattice.toEuc m‖ ^ (-(M : ℝ)) ≤
          (‖Lattice.toEuc m‖ / (2 * d)) ^ (-(M : ℝ)) := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by
          have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
          linarith)
        rw [div_le_iff₀ hd2]; linarith
      have h3 : (‖Lattice.toEuc m‖ / (2 * d)) ^ (-(M : ℝ)) =
          (2 * d) ^ M * ‖Lattice.toEuc m‖ ^ (-(M : ℝ)) := by
        rw [Real.div_rpow hmpos.le hd2.le, Real.rpow_neg hd2.le, Real.rpow_natCast, div_inv_eq_mul,
          mul_comm]
      calc |f (c + Lattice.toEuc m)| ≤ T * ‖c + Lattice.toEuc m‖ ^ (-(M : ℝ)) := h1
        _ ≤ T * ((2 * d) ^ M * ‖Lattice.toEuc m‖ ^ (-(M : ℝ))) := by
            rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hT
        _ = L * ‖Lattice.toEuc m‖ ^ (-(M : ℝ)) := by simp only [hL]; ring
  have := tsum_of_norm_bounded hB hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  simp only [hL]; ring

/-- The periodisation of a signed integrable function with summable translates is integrable. -/
lemma text_integrable_perio_signed {f : Euc d → ℝ} (hf : Measurable f) (hint : Integrable f)
    (hsum : ∀ y, Summable fun m : Lattice d => f (y + Lattice.toEuc m)) :
    Integrable (perio f : Torus d → ℝ) := by
  have hsum' : ∀ y, Summable fun m : Lattice d => |f| (y + Lattice.toEuc m) := fun y =>
    (hsum y).abs
  have h1 : Integrable (perio (fun z => |f z|) : Torus d → ℝ) :=
    tpos_integrable_perio hf.abs hint.abs (fun z => abs_nonneg _) hsum'
  refine h1.mono' (tpos_perio_measurable hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold perio
  rw [Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm (hsum _).norm).trans (le_of_eq (by simp))

end HRS.Commutator.TorusNote
