import HRS.MS.R2GenInitAux22
import HRS.MS.OrbIdTie

/-!
# S10.5 window comparison, packet B9: pairings of the window feature with the reconstruction test vectors

For `u ∈ [0,T]`, `r ∈ [0,b+T]` and the vectors `y1(u,α) = (e_α, 1_{[0,u]}e_α, 0)`, `y2(α) = (0,0,e_α)` of `𝒦_T`:
`⟨Γ_{b,r,a}(x), y2(α)⟩ = 1_{b ≤ r} ∂_aφ_α(x)` and
`⟨Γ_{b,r,a}(x), y1(u,α)⟩ = ∂_aU(r,b+u)φ_α(x)` if `r ≤ b+u` and `∂_aφ_α(x)` otherwise (Duhamel at horizon `b+T`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MS.S52

variable {d : ℕ}

theorem s105_pair_y2 (C : WholeCoeff d) (m T b r : ℝ) (a : Fin d) (x : Euc d)
    (hA : Memℓp (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) 2)
    (hB : Memℓp (fun α => if b ≤ r then gradComp a (oscTestFun m α) x else 0) 2)
    (hmem : MemLp (fun u : ℝ => if r < b + u then ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (α : MultiIndex d) :
    inner ℝ (r2WindowFeature C m T (gradComp a) b r x) (s52y2 m T α) =
      if b ≤ r then gradComp a (oscTestFun m α) x else 0 := by
  rw [← s52_coord_B, s105_win_eq C m T b r a x hA hmem, s52_mk_B, s52_coord_ellVec hB]

theorem s105_F_integrable (C : WholeCoeff d) {m τ₀ : ℝ} (hC : OscAdjointInput C m τ₀) {r : ℝ} (hr : 0 ≤ r)
    (a : Fin d) (α : MultiIndex d) (x : Euc d) {t : ℝ} (ht : t ≤ τ₀) :
    IntegrableOn (fun τ' : ℝ => if r < τ' then gradComp a (propagatorW C r τ'
      (generatorW C τ' (oscTestFun m α))) x else 0) (Set.Icc (0 : ℝ) t) := by
  classical
  have e : (fun τ' : ℝ => if r < τ' then gradComp a (propagatorW C r τ'
      (generatorW C τ' (oscTestFun m α))) x else 0) =
      (Set.Ioi r).indicator (fun τ => gradComp a (propagatorW C r τ
        (generatorW C τ (oscTestFun m α))) x) := by
    funext τ; by_cases h : r < τ <;> simp [Set.indicator_apply, h]
  rw [e, integrableOn_indicator_iff measurableSet_Ioi]
  by_cases hrt : r ≤ t
  · refine (hC.duhamel r t hr hrt ht α a x).1.mono_set ?_
    intro τ hτ
    exact ⟨hτ.1.le, hτ.2.2⟩
  · have : Set.Ioi r ∩ Set.Icc (0 : ℝ) t = ∅ := by
      ext τ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h1 _; linarith [not_le.1 hrt]
    rw [this]
    exact integrableOn_empty

theorem s105_pair_y1 (C : WholeCoeff d) {m T b r : ℝ} (hC : OscAdjointInput C m (b + T)) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hrT : r ≤ b + T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (a : Fin d) (x : Euc d)
    (hA : Memℓp (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) 2)
    (hmemℓ : ∀ u' ∈ Set.Icc (0 : ℝ) T, r < b + u' → Memℓp (fun α => gradComp a (propagatorW C r (b + u')
      (generatorW C (b + u') (oscTestFun m α))) x) 2)
    (hmem : MemLp (fun u : ℝ => if r < b + u then ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (α : MultiIndex d) :
    inner ℝ (r2WindowFeature C m T (gradComp a) b r x) (s52y1 m T u α) =
      if r ≤ b + u then gradComp a (propagatorW C r (b + u) (oscTestFun m α)) x
      else gradComp a (oscTestFun m α) x := by
  classical
  rw [s52_inner_y1 hu.2, s105_win_eq C m T b r a x hA hmem, s52_mk_A₀, s52_mk_A', s52_coord_ellVec hA]
  have hae : ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ((hmem.toLp _ : L2Path d m T) τ) = (fun τ : ℝ => if r < b + τ then ellVec (d := d) m (fun α => gradComp a
        (propagatorW C r (b + τ) (generatorW C (b + τ) (oscTestFun m α))) x) else 0) τ := hmem.coeFn_toLp
  have hae' : ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) u)), ((hmem.toLp _ : L2Path d m T) τ) =
      (fun τ : ℝ => if r < b + τ then ellVec (d := d) m (fun α => gradComp a
        (propagatorW C r (b + τ) (generatorW C (b + τ) (oscTestFun m α))) x) else 0) τ :=
    ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc_right hu.2) hae
  have hint : ∫ τ in Set.Icc (0 : ℝ) u, OscDual.coord ((hmem.toLp _ : L2Path d m T) τ) α =
      ∫ τ in Set.Icc (0 : ℝ) u, (if r < b + τ then gradComp a (propagatorW C r (b + τ)
        (generatorW C (b + τ) (oscTestFun m α))) x else 0) := by
    refine integral_congr_ae ?_
    filter_upwards [hae', ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := u))] with τ h1 h2
    rw [h1]
    by_cases hrτ : r < b + τ
    · simp only [hrτ, if_true]
      exact s52_coord_ellVec (hmemℓ τ ⟨h2.1, h2.2.trans hu.2⟩ hrτ) α
    · simp only [hrτ, if_false]
      exact s52_coord_zero α
  rw [hint]
  set F : ℝ → ℝ := fun τ' => if r < τ' then gradComp a (propagatorW C r τ'
    (generatorW C τ' (oscTestFun m α))) x else 0 with hF
  have hbu : b ≤ b + u := by linarith [hu.1]
  have hbuT : b + u ≤ b + T := by linarith [hu.2]
  have hshift : ∫ τ in Set.Icc (0 : ℝ) u, F (b + τ) = ∫ τ' in Set.Icc b (b + u), F τ' := by
    have h1 := intervalIntegral.integral_comp_add_left (a := 0) (b := u) F b
    rw [intervalIntegral.integral_of_le hu.1, intervalIntegral.integral_of_le (by linarith [hu.1]),
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at h1
    simpa using h1
  have hFu := s52_duhamel_int hC hr (t := b + u) hbuT a α x
  have hFb := s52_duhamel_int hC hr (t := b) (by linarith) a α x
  have hI1 : IntervalIntegrable F volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2 (s105_F_integrable C hC hr a α x (by linarith))
  have hI2 : IntervalIntegrable F volume b (b + u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbu).2
      ((s105_F_integrable C hC hr a α x hbuT).mono_set (Set.Icc_subset_Icc_left hb))
  have hsplit : ∫ τ' in Set.Icc (0 : ℝ) (b + u), F τ' =
      (∫ τ' in Set.Icc (0 : ℝ) b, F τ') + ∫ τ' in Set.Icc b (b + u), F τ' := by
    have := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hbu,
      intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at this
    exact this.symm
  have hA0 : gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x =
      if r ≤ b then gradComp a (propagatorW C r b (oscTestFun m α)) x else gradComp a (oscTestFun m α) x := by
    by_cases hrb : r ≤ b
    · rw [max_eq_left hrb, if_pos hrb]
    · rw [max_eq_right (not_le.1 hrb).le, if_neg hrb]
      have := (hC.duhamel r r hr le_rfl hrT α a x).2
      rw [Set.Icc_self, setIntegral_measure_zero _ (by simp)] at this
      linarith
  show gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x + ∫ τ in Set.Icc (0 : ℝ) u, F (b + τ) = _
  rw [hshift, hA0]
  have hsub : ∫ τ' in Set.Icc b (b + u), F τ' =
      (∫ τ' in Set.Icc (0 : ℝ) (b + u), F τ') - ∫ τ' in Set.Icc (0 : ℝ) b, F τ' := by linarith
  rw [hsub, hFu, hFb]
  by_cases hrb : r ≤ b
  · have hrbu : r ≤ b + u := hrb.trans hbu
    simp only [hrb, hrbu, if_true]
    ring
  · have hrb' : ¬ r ≤ b := hrb
    simp only [hrb', if_false]
    by_cases hrbu : r ≤ b + u
    · simp only [hrbu, if_true]; ring
    · simp only [hrbu, if_false]; ring

end HRS.MS.R2GenInit
