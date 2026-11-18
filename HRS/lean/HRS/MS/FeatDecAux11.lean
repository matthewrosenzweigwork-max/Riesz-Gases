import HRS.MS.FeatDecAux10

/-!
# S8.5 `feature_decay`, part 11 (S85 packet): the weighted feature lemma

`s85_features_weighted`: coordinatewise weighted bounds
`‖D^j ∂_aφ_α(x)‖, ‖D^j ∂_aU(r,t)Lφ_α(x)‖ ≤ c_α ⟨x⟩^{-(p+j)}` (`j ≤ n`, `c` summable) imply, for every `a` and `r ∈ [0,T]`:
`IsKFeature` of the feature at every `x` (no junk), `x ↦ Γ_{r,a}(x)` is `C^n`, and `⟨x⟩^p ‖D^jΓ_{r,a}(x)‖ ≤ C_f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

theorem s85_jbneg_le_one {p : ℝ} (hp : 0 ≤ p) (j : ℕ) (x : Euc d) :
    jbracket x ^ (-(p + (j : ℝ))) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (s85_jb_one_le x)
    (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)

theorem s85_features_weighted {n : ℕ} {m T p : ℝ} (hd1 : 1 ≤ d) (hp : 0 ≤ p) (C : WholeCoeff d)
    (c : MultiIndex d → ℝ) (hc0 : ∀ α, 0 ≤ c α) (hcs : Summable c)
    (hbase : ∀ (a : Fin d) (α : MultiIndex d),
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (oscTestFun m α) x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤
        c α * jbracket x ^ (-(p + (j : ℝ))))
    (horb : ∀ (a : Fin d) (α : MultiIndex d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x) x‖ ≤
          c α * jbracket x ^ (-(p + (j : ℝ))))
    (hmeas : ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (x : Euc d),
      AEStronglyMeasurable (fun t => gradComp a (propagatorW C r t
        (generatorW C t (oscTestFun m α))) x) (volume.restrict (Set.Ioc r T))) :
    ∃ Cf : ℝ, ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) T,
      (∀ x, IsKFeature C m T (gradComp a) r x) ∧
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradFeature C m T a r x) ∧
      ∀ j ≤ n, ∀ x, jbracket x ^ p * ‖iteratedFDeriv ℝ j (fun y => gradFeature C m T a r y) x‖ ≤ Cf := by
  obtain ⟨Kw, hKw0, hKw⟩ := s85_mulw (d := d) n p
  obtain ⟨K', hK'0, hK'⟩ := s85_unweight (d := d) (E := KSpace d m T) n p
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set c' : MultiIndex d → ℝ := fun α => Kw * c α with hc'
  have hc'0 : ∀ α, 0 ≤ c' α := fun α => mul_nonneg hKw0 (hc0 α)
  have hc's : Summable c' := hcs.mul_left Kw
  refine ⟨K' * (2 * (∑' α, c' α) + (d : ℝ) ^ n * ((∑' α, c' α) * (μ Set.univ).toReal ^ (1 / 2 : ℝ))),
    fun a r hr => ?_⟩
  -- coordinate families
  set b : MultiIndex d → Euc d → ℝ := fun α y => gradComp a (oscTestFun m α) y with hb
  set o : MultiIndex d → ℝ → Euc d → ℝ := fun α t y =>
    if r < t ∧ t ≤ T then gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) y else 0
    with ho
  have hcsabs : Summable fun α => |c α| := hcs.abs
  -- raw bounds
  have hbR : ∀ α, ContDiff ℝ (n : WithTop ℕ∞) (b α) ∧ ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (b α) x‖ ≤ c α :=
    fun α => ⟨(hbase a α).1, fun j hj x => ((hbase a α).2 j hj x).trans (by
      calc c α * jbracket x ^ (-(p + (j : ℝ))) ≤ c α * 1 :=
            mul_le_mul_of_nonneg_left (s85_jbneg_le_one hp j x) (hc0 α)
        _ = c α := mul_one _)⟩
  have hoZ : ∀ α t, ¬ (r < t ∧ t ≤ T) → o α t = fun _ => 0 := fun α t h => by
    funext y; simp [ho, h]
  have hoE : ∀ α t, (r < t ∧ t ≤ T) → o α t = fun y => gradComp a
      (propagatorW C r t (generatorW C t (oscTestFun m α))) y := fun α t h => by
    funext y; simp [ho, h]
  have hoR : ∀ α t, ContDiff ℝ (n : WithTop ℕ∞) (o α t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (o α t) x‖ ≤ c α * jbracket x ^ (-(p + (j : ℝ))) := by
    intro α t
    by_cases h : r < t ∧ t ≤ T
    · rw [hoE α t h]
      exact horb a α r t hr.1 h.1.le h.2
    · rw [hoZ α t h]
      exact ⟨contDiff_const, fun j hj x => by
        rw [s55f_iter_zero]
        exact mul_nonneg (hc0 α) (Real.rpow_nonneg (s85_jb_pos x).le _)⟩
  have hoR' : ∀ α t, ContDiff ℝ (n : WithTop ℕ∞) (o α t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (o α t) x‖ ≤ c α := fun α t =>
    ⟨(hoR α t).1, fun j hj x => ((hoR α t).2 j hj x).trans (by
      calc c α * jbracket x ^ (-(p + (j : ℝ))) ≤ c α * 1 :=
            mul_le_mul_of_nonneg_left (s85_jbneg_le_one hp j x) (hc0 α)
        _ = c α := mul_one _)⟩
  have hmR : ∀ x α, AEStronglyMeasurable (fun t => o α t x) μ := by
    intro x α
    have e : (fun t => o α t x) = (Set.Ioc r T).indicator (fun t => gradComp a
        (propagatorW C r t (generatorW C t (oscTestFun m α))) x) := by
      funext t
      by_cases ht : r < t ∧ t ≤ T
      · simp [ho, ht, Set.indicator_of_mem (show t ∈ Set.Ioc r T from ht)]
      · simp [ho, ht, Set.indicator_of_notMem (show t ∉ Set.Ioc r T from ht)]
    rw [e, aestronglyMeasurable_indicator_iff measurableSet_Ioc]
    have hsub : Set.Ioc r T ⊆ Set.Icc (0 : ℝ) T := fun t ht => ⟨hr.1.trans ht.1.le, ht.2⟩
    have : μ.restrict (Set.Ioc r T) = volume.restrict (Set.Ioc r T) := by
      rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rw [this]
    exact hmeas a r hr α x
  obtain ⟨hmem, hCdR, -⟩ := s85_Th_props (n := n) (m := m) (T := T) hd1 b o c hc0 hcs hbR hoR' hmR
  -- weighted families
  set w : Euc d → ℝ := fun y => jbracket y ^ p with hw
  have hbW : ∀ α, ContDiff ℝ (n : WithTop ℕ∞) (fun y => w y * b α y) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => w y * b α y) x‖ ≤ c' α := fun α =>
    hKw (b α) (c α) (hc0 α) (hbase a α).1 (hbase a α).2
  have hoW : ∀ α t, ContDiff ℝ (n : WithTop ℕ∞) (fun y => w y * o α t y) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => w y * o α t y) x‖ ≤ c' α := fun α t =>
    hKw (o α t) (c α) (hc0 α) (hoR α t).1 (hoR α t).2
  have hmW : ∀ x α, AEStronglyMeasurable (fun t => w x * o α t x) μ := fun x α =>
    (hmR x α).const_mul (w x)
  obtain ⟨-, hCdW, hbdW⟩ := s85_Th_props (n := n) (m := m) (T := T) hd1 (fun α y => w y * b α y)
    (fun α t y => w y * o α t y) c' hc'0 hc's hbW hoW hmW
  -- identification of the feature
  have hbmem : ∀ x, Memℓp (fun α => b α x) 2 := fun x => by
    refine s55f_memℓp_of_summable (Summable.of_norm_bounded hcs fun α => ?_)
    have := (hbR α).2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    rwa [Real.norm_eq_abs, abs_abs]
  have hobd : ∀ x α t, |o α t x| ≤ c α := fun x α t => by
    have := (hoR' α t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have homem : ∀ x t, Memℓp (fun α => o α t x) 2 := fun x t =>
    s55f_memℓp_of_summable (Summable.of_norm_bounded hcs fun α => by
      simpa [Real.norm_eq_abs] using hobd x α t)
  have hid : ∀ x, gradFeature C m T a r x = s85Th m T b o x := by
    intro x
    have hfF : (fun t => if r < t then ellVec (d := d) m (fun α => gradComp a
        (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) =ᵐ[μ]
        fun t => ellVec (d := d) m (fun α => o α t x) := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
      by_cases hrt : r < t
      · have hc : r < t ∧ t ≤ T := ⟨hrt, ht.2⟩
        simp only [hrt, if_true, ho, hc, and_self]
      · simp only [hrt, if_false, ho, false_and, if_false]
        exact (s55f_ellVec_zero m).symm
    have hmf := (hmem x).ae_eq hfF.symm
    unfold s85Th
    rw [dif_pos (hmem x), ← s55f_mk_eq]
    unfold gradFeature orbitFeature
    dsimp only
    congr 1
    exact (dif_pos hmf).trans (MemLp.toLp_congr hmf (hmem x) hfF)
  have hsmul : ∀ x, s85Th m T (fun α y => w y * b α y) (fun α t y => w y * o α t y) x =
      w x • gradFeature C m T a r x := fun x => by
    rw [hid x]
    exact s85_Th_smul b o w x (hbmem x) (homem x) (hmem x)
  have hfunW : (fun x => w x • gradFeature C m T a r x) =
      s85Th m T (fun α y => w y * b α y) (fun α t y => w y * o α t y) :=
    funext fun x => (hsmul x).symm
  have hfunR : (fun x => gradFeature C m T a r x) = s85Th m T b o := funext hid
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨hbmem x, fun t ht => ?_, ?_⟩
    · have hc : r < t ∧ t ≤ T := ⟨ht.1, ht.2⟩
      have := homem x t
      simpa [ho, hc] using this
    · have hfF : (fun t => if r < t then ellVec (d := d) m (fun α => gradComp a
          (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) =ᵐ[μ]
          fun t => ellVec (d := d) m (fun α => o α t x) := by
        refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
        by_cases hrt : r < t
        · have hc : r < t ∧ t ≤ T := ⟨hrt, ht.2⟩
          simp only [hrt, if_true, ho, hc, and_self]
        · simp only [hrt, if_false, ho, false_and, if_false]
          exact (s55f_ellVec_zero m).symm
      exact (hmem x).ae_eq hfF.symm
  · rw [hfunR]; exact hCdR
  · intro j hj x
    refine hK' (fun y => gradFeature C m T a r y) _ ?_ ?_ j hj x
    · rw [hfunR]; exact hCdR
    · intro j' hj' y
      rw [hfunW]
      exact hbdW j' hj' y

end HRS.MS.S85
