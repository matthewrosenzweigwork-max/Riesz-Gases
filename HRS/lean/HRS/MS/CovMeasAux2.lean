import HRS.MS.CovMeasAux1

/-!
# S10.1 (worker S101B), part 2: the orbit data of `R2OrbitSummable` as `ℓ²`-summable sup bounds; linearity of the propagator on
finite combinations

`S101Data C m T r c`: the unpacked content of `R2OrbitSummable C m T r` (regularity in `x`, differentiability in `t`) together with
`ℓ²`-summable sup bounds `c_α` (`s101_data_of_horb`): for `0 ≤ u ≤ t ≤ T`, `‖D^j U^{u,t}φ_α‖_∞ ≤ c_α` and
`‖D^j ∂_tU^{u,t}φ_α‖_∞ ≤ c_α` for `j ≤ r+1`.  `s101_prop_comb`: `hlin` for finite sums.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

/-- The time derivative `∂_tU^{τ,t}φ_α(x)` (one-sided within `[τ,T]`), as in `R2OrbitSummable`. -/
def s101Dt (C : WholeCoeff d) (m T : ℝ) (τ t : ℝ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  derivWithin (fun t' => propagatorW C τ t' (oscTestFun m α) x) (Set.Icc τ T) t

/-- The unpacked orbit data with `ℓ²`-summable sup bounds. -/
structure S101Data (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (c : MultiIndex d → ℝ) : Prop where
  nonneg : ∀ α, 0 ≤ c α
  summable : Summable fun α => c α ^ 2
  smoothU : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T,
    ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C u t (oscTestFun m α))
  smoothD : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T,
    ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun x => s101Dt C m T u t α x)
  diffT : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ x, ∀ t ∈ Set.Icc u T,
    DifferentiableWithinAt ℝ (fun t' => propagatorW C u t' (oscTestFun m α) x) (Set.Icc u T) t
  bddU : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T, ∀ j ≤ r + 1, ∀ x,
    ‖iteratedFDeriv ℝ j (propagatorW C u t (oscTestFun m α)) x‖ ≤ c α
  bddD : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T, ∀ j ≤ r + 1, ∀ x,
    ‖iteratedFDeriv ℝ j (fun x => s101Dt C m T u t α x) x‖ ≤ c α

lemma s101_norm_of_wsup {r : ℕ} {f : Euc d → ℝ} {Λ : ℝ} (hd : 1 ≤ d) (hΛ : 0 ≤ Λ)
    (h : weightedSupE (r + 1) 0 f ≤ ENNReal.ofReal Λ) :
    ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ (r + 1) * Λ := by
  intro j hj x
  have hp : ∀ idx : Fin j → Fin d, |partialDeriv idx f x| ≤ Λ := by
    intro idx
    have h1 := s55_dse_bound (k := r + 1) (w := fun _ => (0 : ℝ)) (by unfold weightedSupE at h; exact h)
      hj idx x
    simp only [Real.rpow_zero, one_mul] at h1
    exact h1.trans (max_eq_left hΛ).le
  have hs : ∑ idx : Fin j → Fin d, |partialDeriv idx f x| ≤ (d : ℝ) ^ j * Λ :=
    s55_card_sum_le j _ hp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc ‖iteratedFDeriv ℝ j f x‖ ≤ ∑ idx : Fin j → Fin d, |partialDeriv idx f x| :=
        HRS.MP.RdInit.mri_norm_iter_le j f x
    _ ≤ (d : ℝ) ^ j * Λ := hs
    _ ≤ (d : ℝ) ^ (r + 1) * Λ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hj) hΛ

theorem s101_data_of_horb {C : WholeCoeff d} {m T : ℝ} {r : ℕ} (hd : 1 ≤ d) (horb : R2OrbitSummable C m T r) :
    ∃ c : MultiIndex d → ℝ, S101Data C m T r c := by
  obtain ⟨hreg, hsum⟩ := horb
  set S : MultiIndex d → ℝ≥0∞ := fun α => ⨆ u ∈ Set.Icc (0 : ℝ) T, ⨆ t ∈ Set.Icc u T,
    (weightedSupE (r + 1) 0 (propagatorW C u t (oscTestFun m α)) ^ 2 +
      weightedSupE (r + 1) 0 (fun x => derivWithin (fun t' => propagatorW C u t' (oscTestFun m α) x)
        (Set.Icc u T) t) ^ 2) with hS
  have hSfin : ∀ α, S α ≠ ⊤ := fun α => ne_top_of_le_ne_top hsum.ne (ENNReal.le_tsum α)
  have hsq : Summable fun α => (S α).toReal := ENNReal.summable_toReal hsum.ne
  set c0 : MultiIndex d → ℝ := fun α => Real.sqrt (S α).toReal with hc0
  have hc0sq : ∀ α, c0 α ^ 2 = (S α).toReal := fun α => Real.sq_sqrt ENNReal.toReal_nonneg
  have hc0nn : ∀ α, 0 ≤ c0 α := fun α => Real.sqrt_nonneg _
  -- a single weighted sup is bounded by `c0`
  have hbound : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T, ∀ f : Euc d → ℝ,
      (weightedSupE (r + 1) 0 f ^ 2 ≤ S α) → weightedSupE (r + 1) 0 f ≤ ENNReal.ofReal (c0 α) := by
    intro α u hu t ht f hf
    have hfin : weightedSupE (r + 1) 0 f ≠ ⊤ := by
      intro htop
      rw [htop] at hf
      exact hSfin α (top_le_iff.1 (by simpa using hf))
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ((weightedSupE (r + 1) 0 f) ^ 2).toReal ≤ (S α).toReal := ENNReal.toReal_mono (hSfin α) hf
    rw [ENNReal.toReal_pow] at h1
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  have hU : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T,
      weightedSupE (r + 1) 0 (propagatorW C u t (oscTestFun m α)) ≤ ENNReal.ofReal (c0 α) := by
    intro α u hu t ht
    refine hbound α u hu t ht _ ?_
    exact le_trans (le_self_add) (le_iSup₂_of_le u hu (le_iSup₂_of_le t ht le_rfl))
  have hD : ∀ α, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc u T,
      weightedSupE (r + 1) 0 (fun x => derivWithin (fun t' => propagatorW C u t' (oscTestFun m α) x)
        (Set.Icc u T) t) ≤ ENNReal.ofReal (c0 α) := by
    intro α u hu t ht
    refine hbound α u hu t ht _ ?_
    exact le_trans (le_add_self) (le_iSup₂_of_le u hu (le_iSup₂_of_le t ht le_rfl))
  have hdpow : (0 : ℝ) ≤ (d : ℝ) ^ (r + 1) := by positivity
  refine ⟨fun α => (d : ℝ) ^ (r + 1) * c0 α, ?_⟩
  refine ⟨fun α => mul_nonneg hdpow (hc0nn α), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mul_pow, hc0sq] using hsq.mul_left (((d : ℝ) ^ (r + 1)) ^ 2)
  · intro α u hu t ht
    have := (hreg α u hu t ht).1
    simpa using this
  · intro α u hu t ht
    have := (hreg α u hu t ht).2.2
    simpa [s101Dt] using this
  · intro α u hu x t ht
    exact (hreg α u hu t ht).2.1 x
  · intro α u hu t ht j hj x
    exact s101_norm_of_wsup hd (hc0nn α) (hU α u hu t ht) j hj x
  · intro α u hu t ht j hj x
    exact s101_norm_of_wsup hd (hc0nn α) (hD α u hu t ht) j hj x

/-! ### Linearity of the propagator on finite combinations -/

lemma s101_isCombo_single (m : ℝ) (β : MultiIndex d) : IsR2DualCombo m (oscTestFun m β) :=
  ⟨{β}, fun _ => 1, by funext x; simp⟩

lemma s101_isCombo_zero (m : ℝ) : IsR2DualCombo (d := d) m (0 : Euc d → ℝ) :=
  ⟨∅, fun _ => 0, by funext x; simp⟩

lemma s101_isCombo_sum (m : ℝ) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    IsR2DualCombo m (fun x => ∑ α ∈ S, a α * oscTestFun m α x) := ⟨S, a, rfl⟩

theorem s101_prop_comb {C : WholeCoeff d} {m T : ℝ}
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ →
      IsR2DualCombo m ψ → propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    propagatorW C u t (fun x => ∑ α ∈ S, a α * oscTestFun m α x) =
      fun x => ∑ α ∈ S, a α * propagatorW C u t (oscTestFun m α) x := by
  classical
  have h0 : propagatorW C u t (0 : Euc d → ℝ) = 0 := by
    have := hlin u t hu hut htT 0 0 (-1) (s101_isCombo_zero m) (s101_isCombo_zero m)
    simpa using this
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact h0
  | insert β S hβ ih =>
    have e : (fun x => ∑ α ∈ insert β S, a α * oscTestFun m α x) =
        (fun x => ∑ α ∈ S, a α * oscTestFun m α x) + a β • oscTestFun m β := by
      funext x
      rw [Finset.sum_insert hβ]
      simp [add_comm]
    rw [e, hlin u t hu hut htT _ _ (a β) (s101_isCombo_sum m S a) (s101_isCombo_single m β), ih]
    funext x
    rw [Finset.sum_insert hβ]
    simp [add_comm]

end HRS.MS.CovMeas
