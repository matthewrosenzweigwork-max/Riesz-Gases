import HRS.MS.R2ChaosAux47

/-!
# HRS.MS.R2ChaosAux48 -- (e) part 3: the Hilbert space `H = (L²(dt))^{k+1}` and the embedding `ι : C([0,T]) → L²(dt)`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

instance s94_inst_ips (T : ℝ) : InnerProductSpace ℝ (R2L2 T) :=
  inferInstanceAs (InnerProductSpace ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))))

instance s94_inst_cs (T : ℝ) : CompleteSpace (R2L2 T) :=
  inferInstanceAs (CompleteSpace (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))))

section Embed

variable {T : ℝ}

/-- The `L²(dt)` class of a continuous path. -/
def s94_iota (T : ℝ) (v : C(Set.Icc (0 : ℝ) T, ℝ)) : R2L2 T := r2L2Path T (r2PathEval T v)

theorem s94_pathEval_memLp (hT : 0 ≤ T) (v : C(Set.Icc (0 : ℝ) T, ℝ)) :
    MemLp (r2PathEval T v) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
  s94_memLp_of_bdd (s94_pathEval_measurable v) (K := ‖v‖) fun t _ => s94_pathEval_abs_le v t

theorem s94_iota_dist (hT : 0 ≤ T) (v v' : C(Set.Icc (0 : ℝ) T, ℝ)) :
    dist (s94_iota T v) (s94_iota T v') ≤ Real.sqrt T * dist v v' := by
  refine s94_dist_r2L2Path_le hT (s94_pathEval_memLp hT v) (s94_pathEval_memLp hT v') dist_nonneg fun t ht => ?_
  have := s94_pathEval_abs_le (v - v') t
  rw [s94_pathEval_sub] at this
  simpa [dist_eq_norm] using this

theorem s94_iota_continuous (hT : 0 ≤ T) : Continuous (s94_iota T) := by
  have : LipschitzWith ⟨Real.sqrt T, Real.sqrt_nonneg _⟩ (s94_iota T) :=
    LipschitzWith.of_dist_le_mul fun v v' => by
      show dist (s94_iota T v) (s94_iota T v') ≤ Real.sqrt T * dist v v'
      exact s94_iota_dist hT v v'
  exact this.continuous

end Embed

section HSpace

variable {T : ℝ} {k : ℕ}

/-- Assemble `(f_1, …, f_k, b)` into the Hilbert space `H = (L²(dt))^{k+1}`. -/
def s94_mkH (T : ℝ) {k : ℕ} (f : Fin k → R2L2 T) (b : R2L2 T) : PiLp 2 (fun _ : Fin (k + 1) => R2L2 T) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => R2L2 T) f b)

theorem s94_mkH_castSucc (f : Fin k → R2L2 T) (b : R2L2 T) (i : Fin k) :
    (s94_mkH T f b) (Fin.castSucc i) = f i := by
  simp [s94_mkH]

theorem s94_mkH_last (f : Fin k → R2L2 T) (b : R2L2 T) : (s94_mkH T f b) (Fin.last k) = b := by
  simp [s94_mkH]

theorem s94_mkH_continuous : Continuous fun p : (Fin k → R2L2 T) × R2L2 T => s94_mkH T p.1 p.2 := by
  unfold s94_mkH
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [Fin.snoc_last] using continuous_snd
  · have : Continuous fun p : (Fin k → R2L2 T) × R2L2 T => p.1 i := (continuous_apply i).comp continuous_fst
    simpa [Fin.snoc_castSucc] using this

theorem s94_normH_le (x : PiLp 2 (fun _ : Fin (k + 1) => R2L2 T)) : ‖x‖ ≤ ∑ j, ‖x j‖ := by
  have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (k + 1) => R2L2 T) x
  have h2 : ‖x‖ ^ 2 ≤ (∑ j, ‖x j‖) ^ 2 := by
    rw [h1]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 h2

theorem s94_normH_pow_le (x : PiLp 2 (fun _ : Fin (k + 1) => R2L2 T)) {p : ℝ} (hp : 1 ≤ p) :
    ‖x‖ ^ p ≤ ((k : ℝ) + 1) ^ (p - 1) * ∑ j, ‖x j‖ ^ p := by
  have h1 := s94_normH_le x
  have h2 : (∑ j, ‖x j‖) ^ p ≤ (Fintype.card (Fin (k + 1)) : ℝ) ^ (p - 1) * ∑ j, ‖x j‖ ^ p := by
    have := Real.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (Fin (k + 1))) (fun j => ‖x j‖) hp
    simpa using this
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h2
  exact (Real.rpow_le_rpow (norm_nonneg _) h1 (by linarith)).trans h2

/-- The linear map `H → B3 = (L²)^k × L² × C([0,T])`, `y ↦ (y_1..y_k, y_{k+1}, J y_{k+1})`. -/
def s94_Lmap (hT : 0 ≤ T) : PiLp 2 (fun _ : Fin (k + 1) => R2L2 T) →L[ℝ]
    (Fin k → R2L2 T) × R2L2 T × C(Set.Icc (0 : ℝ) T, ℝ) :=
  (ContinuousLinearMap.pi (fun i : Fin k => PiLp.proj 2 (fun _ : Fin (k + 1) => R2L2 T) (Fin.castSucc i))).prod
    ((PiLp.proj 2 (fun _ : Fin (k + 1) => R2L2 T) (Fin.last k)).prod
      ((s94_J hT).comp (PiLp.proj 2 (fun _ : Fin (k + 1) => R2L2 T) (Fin.last k))))

theorem s94_Lmap_mkH (hT : 0 ≤ T) (f : Fin k → R2L2 T) (b : R2L2 T) :
    s94_Lmap hT (s94_mkH T f b) = (f, b, s94_J hT b) := by
  have e1 : ∀ i, (s94_Lmap hT (s94_mkH T f b)).1 i = f i := fun i => s94_mkH_castSucc f b i
  have e2 : (s94_Lmap hT (s94_mkH T f b)).2.1 = b := s94_mkH_last f b
  have e3 : (s94_Lmap hT (s94_mkH T f b)).2.2 = s94_J hT b := by
    show s94_J hT ((s94_mkH T f b) (Fin.last k)) = _
    rw [s94_mkH_last]
  exact Prod.ext (funext e1) (Prod.ext e2 e3)

end HSpace

end HRS.MS.R2Chaos
