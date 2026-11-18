import HRS.MS.WsStatAux8
import HRS.MS.OrbFeatTie

/-!
# S21 packet E2: the `feature` clause of `OscAdjointInput` for the stationary coefficient

* `s21_isOrbitFeatureK`: if the base coordinates `d_a phi_alpha(x)` and the orbit coordinates
  `d_a U^{r,t} L phi_alpha (x)` are bounded by a summable majorant `c_alpha` (uniformly in `x`, `r <= t <= T`) and
  `t |-> d_a U^{r,t} L phi_alpha (x)` is a.e. measurable on `(r,T]`, then `IsOrbitFeatureK C m T (gradComp a) r x`
  (`l^2` membership of the coordinates and `L^2(0,T; l^2)` membership of the orbit path: nothing is junk).
* `s21_feature_bounds`: for the stationary coefficient `Cf` and `m >= 24 d + 240` such a majorant exists
  (`s52b_orbit_data`, `s52b_base_data`: `c_alpha = C lambda_alpha^{(J-m)/2}`, `J = s52bIdx d s (s52bK d (d+6) + 2) <= 4.5 d + 24`,
  summable since `m - J > 2d`), with measurability from the continuity in `t` of `s52b_orbit_data`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S21

open HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S85 HRS.MS.UlW HRS.MS.Go
open HRS (Euc)

variable {d : ℕ}

theorem s21_isOrbitFeatureK {C : WholeCoeff d} {m T : ℝ} (a : Fin d) (c : MultiIndex d → ℝ)
    (hc0 : ∀ α, 0 ≤ c α) (hcs : Summable c)
    (hbase : ∀ (α : MultiIndex d) (x : Euc d), |gradComp a (oscTestFun m α) x| ≤ c α)
    (horb : ∀ (α : MultiIndex d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
      |gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x| ≤ c α)
    (hmeas : ∀ r ∈ Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (x : Euc d),
      AEStronglyMeasurable (fun t => gradComp a (propagatorW C r t
        (generatorW C t (oscTestFun m α))) x) (volume.restrict (Ioc r T)))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (x : Euc d) :
    IsOrbitFeatureK C m T (gradComp a) r x := by
  have hsumabs : ∀ f : MultiIndex d → ℝ, (∀ α, |f α| ≤ c α) → Summable fun α => |f α| :=
    fun f hf => Summable.of_nonneg_of_le (fun α => abs_nonneg _) hf hcs
  refine ⟨s55f_memℓp_of_summable (hsumabs _ fun α => hbase α x), fun t ht =>
    s55f_memℓp_of_summable (hsumabs _ fun α => horb α r t hr.1 ht.1.le ht.2 x), ?_⟩
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set v' : MultiIndex d → ℝ → ℝ := fun α t =>
    if r < t ∧ t ≤ T then gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x else 0 with hv'
  have hv'bd : ∀ α t, |v' α t| ≤ c α := by
    intro α t
    by_cases ht : r < t ∧ t ≤ T
    · simp only [hv', ht, and_self, if_true]
      exact horb α r t hr.1 ht.1.le ht.2 x
    · simp only [hv', ht, if_false, abs_zero]; exact hc0 α
  have hv'meas : ∀ α, AEStronglyMeasurable (v' α) μ := by
    intro α
    have e : v' α = (Ioc r T).indicator (fun t => gradComp a
        (propagatorW C r t (generatorW C t (oscTestFun m α))) x) := by
      funext t
      by_cases ht : r < t ∧ t ≤ T
      · simp [hv', ht, Set.indicator_of_mem (show t ∈ Ioc r T from ht)]
      · simp [hv', ht, Set.indicator_of_notMem (show t ∉ Ioc r T from ht)]
    rw [e, aestronglyMeasurable_indicator_iff measurableSet_Ioc]
    have hsub : Ioc r T ⊆ Icc (0 : ℝ) T := fun t ht => ⟨hr.1.trans ht.1.le, ht.2⟩
    have : μ.restrict (Ioc r T) = volume.restrict (Ioc r T) := by
      rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rw [this]
    exact hmeas r hr α x
  set Fv : ℝ → OscDual d m := fun t => ellVec (d := d) m (fun α => v' α t) with hFv
  have hmeasF : AEStronglyMeasurable Fv μ :=
    s55f_aesm_ellVec (m := m) (fun α t => v' α t) hv'meas (fun t =>
      Summable.of_norm_bounded hcs fun α => by simpa [Real.norm_eq_abs] using hv'bd α t)
  have hFb : ∀ t, ‖Fv t‖ ≤ ∑' α, c α := by
    intro t
    have h := (s55f_ell_contDiff (E := ℝ) (m := m) (k := 0) (fun α _ => v' α t)
      (fun α => contDiff_const) c hcs (fun α j hj y => by
        have : j = 0 := by omega
        subst this
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact hv'bd α t)).2 0 le_rfl 0
    rwa [norm_iteratedFDeriv_zero] at h
  have hmem : MemLp Fv 2 μ := s55f_memLp_of_bound μ hmeasF hFb
  have hfF : (fun t => if r < t then ellVec (d := d) m (fun α => gradComp a
      (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) =ᵐ[μ] Fv := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
    by_cases hrt : r < t
    · have hc : r < t ∧ t ≤ T := ⟨hrt, ht.2⟩
      simp only [hrt, if_true, hFv, hv', hc, and_self]
    · simp only [hrt, if_false, hFv, hv', false_and, if_false]
      exact (s55f_ellVec_zero m).symm
  exact hmem.ae_eq hfF.symm

theorem s21_feature_bounds (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (hm : (24 : ℝ) * d + 240 ≤ m) :
    ∃ c : MultiIndex d → ℝ, (∀ α, 0 ≤ c α) ∧ Summable c ∧
      (∀ (a : Fin d) (α : MultiIndex d) (x : Euc d), |gradComp a (oscTestFun m α) x| ≤ c α) ∧
      (∀ (a : Fin d) (α : MultiIndex d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
        |gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r t
          (generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) t (oscTestFun m α))) x| ≤ c α) ∧
      (∀ (a : Fin d), ∀ r ∈ Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (x : Euc d),
        AEStronglyMeasurable (fun t => gradComp a (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r t
          (generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) t (oscTestFun m α))) x)
          (volume.restrict (Ioc r T))) := by
  have hd1 : 1 ≤ d := by omega
  set n : ℕ := d + 6 with hn
  have hn' : (d : ℝ) / 2 + 6 < ((n + 1 : ℕ) : ℝ) := by
    simp only [hn]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨Co, hCo0, hall⟩ := s52b_orbit_data hd hs0 hsd n hn' m hT hν Q ρ hρ.2 (fun _ => 0) (s85_sigma d)
    (s85c s ρ) rfl (s85_uniq hd hs0 hsd hν Q hQ hρ T)
  set K : ℕ := s52bK d n with hK
  set J : ℕ := s52bIdx d s (K + 2) with hJ
  have hKJ : K ≤ J := by
    show s52bK d n ≤ s52bIdx d s (s52bK d n + 2)
    unfold s52bIdx; omega
  obtain ⟨Cb, hCb0, hCb⟩ := s52b_base_data (d := d) n m hKJ
  have hJm : (d : ℝ) < (m - J) / 2 := by
    have h1 : (J : ℝ) = 2 * (n : ℝ) + 3 * (⌊(d : ℝ) / 2⌋₊ : ℝ) + 9 + (⌈s + 1⌉₊ : ℝ) := by
      simp only [hJ, hK, s52bIdx, s52bK]; push_cast; ring
    have h2 : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have h3 : (⌈s + 1⌉₊ : ℝ) < s + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
    have : (n : ℝ) = d + 6 := by simp [hn]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    have h := (summable_oscEigenvalue_rpow_iff hd1 ((m - J) / 2)).2 hJm
    have e : -((m - (J : ℝ)) / 2) = ((J : ℝ) - m) / 2 := by ring
    rwa [e] at h
  set Cc : ℝ := max Cb Co with hCc
  set c : MultiIndex d → ℝ := fun α => Cc * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) with hc
  have hpos : ∀ α, 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun α =>
    Real.rpow_nonneg (oscEv_pos α).le _
  have hCc0 : 0 ≤ Cc := (le_max_of_le_left hCb0)
  refine ⟨c, fun α => mul_nonneg hCc0 (hpos α), hsum.mul_left Cc, fun a α x => ?_, fun a α r t hr hrt htT x => ?_,
    fun a r hr α x => ?_⟩
  · obtain ⟨-, hb⟩ := hCb a α
    have := hb 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos α)
  · obtain ⟨hh, -⟩ := hall α a
    obtain ⟨-, hb⟩ := hh r t hr hrt htT
    have := hb 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hpos α)
  · obtain ⟨-, hmc⟩ := hall α a
    exact ((hmc r hr x).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc

end HRS.MS.S21
