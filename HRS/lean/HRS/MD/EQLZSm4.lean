import HRS.MD.EQLZSm3
import HRS.MD.EQLZMarg

/-!
# EQ-LZ packet SM, part 4: the grid maximal inequality for the true flow

From `LevelMaximal` (levels `n = 0, 1, 2, ...`, the regularised flows `Y^n` of `b15e_exists_regularised`, which equal
the true flow `X` eventually, pathwise: `b15c_regularised_eq_strong_proof`), Fatou in `n` (`sm_fatou_core`) and the
energy limit (`sm_energy_tendsto`) give, for every `m ≥ 1` and every smooth `F`,
`E max_{j ≤ m} (F(X_{a+jT/m}) - F(X_a))² ≤ 40 T β⁻¹ ∫ configGradSq F dℙ_{N,β}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS.MD.EQLZ

namespace HRS

namespace MD

namespace EQLZSm

variable {d N : ℕ}

/-- The level process `levelProc Y t` is measurable when `Y t` is. -/
theorem sm_measurable_levelProc {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ → Ω → Fin N → Euc d) (t : ℝ)
    (h : Measurable (Y t)) : Measurable (levelProc Y t) := by
  unfold levelProc
  refine (d1_configEquiv d N).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  exact (Torus.continuous_mk (d := d)).measurable.comp ((measurable_pi_apply i).comp h)

theorem sm_grid_true (hlevel : LevelMaximal) (hd : 2 ≤ d) (hN : 2 ≤ N) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (T a : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (h : LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X)
    (F : Config d N → ℝ) (hF : IsSmoothCfg F) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ ω, ⨆ j : Fin (m + 1),
        ENNReal.ofReal ((F (X (a + (j : ℕ) * (T / m)).toNNReal ω) - F (X a.toNNReal ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (40 * T * β⁻¹ *
        ∫ Y, LZ.configGradSq F Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) := by
  have hNeZ : NeZero N := ⟨by omega⟩
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hDV : D.V = V := rfl
  have hDs : D.s = s := rfl
  have hDinv : D.invβ = β⁻¹ := rfl
  have hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ) := rfl
  have hinvpos : 0 < D.invβ := by rw [hDinv]; exact inv_pos.mpr hβ
  have hV2 : Torus.IsCk 2 D.V := by rw [hDV]; exact sm_isCk_of_smooth hV 2
  have hbeta : D.invβ⁻¹ = β := by rw [hDinv, inv_inv]
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d D.s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  have hGR : gibbsRef D N = canonicalGibbs (periodicRiesz d s) V N β := by
    have := b15_gibbsRef_eq_canonicalGibbs_of_lower (N := N) D hB' hV2 hinvpos
    rwa [hbeta] at this
  have hfl := h.flow
  have hS : IsStrongSolution P D (a + T) X₀ W X ∧ PathwiseUnique P D (a + T) X₀ W := by
    rcases hfl.flow with hh | ⟨hd1, -⟩
    · exact hh
    · omega
  obtain ⟨ℱ, W', hF'⟩ := h.filtered
  have hX0 : P.map (X 0) = canonicalGibbs (periodicRiesz d s) V N β := by
    rw [← h.init]
    exact Measure.map_congr (by filter_upwards [hS.1.init] with ω hω using hω)
  have hprobG : IsProbabilityMeasure (gibbsRef D N) := by
    rw [hGR, ← hX0]; infer_instance
  -- the level flows
  have hW'' : IsBrownianFiltration P (b15e_shiftFil ℱ) W' := b15e_shiftFil_brownian hF'.brownian
  have hY₀ : ∀ t : ℝ, Measurable[b15e_shiftFil ℱ t] (b15e_initLift X) :=
    b15e_initLift_measurable (hF'.adapted 0)
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (b15e_initLift X ω i)) = X₀ ω := by
    filter_upwards [hS.1.init] with ω hω
    rw [b15e_mk_initLift, hω]
  choose Y hY using fun n : ℕ =>
    b15e_exists_regularised hW'' D hV2 (n : ℝ) (b15e_initLift X) hY₀
  have hev := b15c_regularised_eq_strong_proof (M := fun n : ℕ => (n : ℝ)) D hV2 hfl.brownian hS.1
    hF'.coords hY₀ae tendsto_natCast_atTop_atTop hY
  have hNd : 1 ≤ N * d := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by omega))
  set e := d1_configEquiv d N with he
  set Φ : Torus (N * d) → ℝ := fun x => F (e.symm x) with hΦ
  have hΦc : Continuous Φ := b15_continuous_of_isCk (sm_isCk_of_smooth hF 2)
  -- the squared gradient
  set g : Torus (N * d) → ℝ := fun x => ‖Torus.grad Φ x‖ ^ 2 with hg
  have hgc : Continuous g := sm_gradSq_continuous hF
  obtain ⟨Cg, hCg⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
  have hCg' : ∀ x, |g x| ≤ Cg := fun x => by simpa using hCg x (Set.mem_univ x)
  have hlim := sm_energy_tendsto (N := N) D hinvpos hV2 g hgc.measurable Cg hCg'
  have hE : ∫ X', g (e X') ∂(gibbsRef D N) =
      ∫ Y', LZ.configGradSq F Y' ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hGR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X' => ?_)
    simp only [hg]
    rw [sm_configGradSq_eq]
  -- the per-level bounds
  have hbound : ∀ n : ℕ, ∫⁻ ω, ⨆ j : Fin (m + 1),
      ENNReal.ofReal ((Φ (levelProc (Y n) (a + (j : ℕ) * (T / m)) ω) - Φ (levelProc (Y n) a ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (40 * T * D.invβ *
        ((b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) *
            (gibbsPartition D N)⁻¹).toReal *
          ∫ x, g x ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ))))) := by
    intro n
    obtain ⟨ρ, hρm, hρb, hρlaw⟩ := sm_level_density (N := N) D hinvpos hV2 (Nat.cast_nonneg n)
    have hflow : IsLevelFlow D (n : ℝ) P (b15e_shiftFil ℱ) W' (b15e_initLift X) (Y n) :=
      ⟨hW'', hY₀, hY n⟩
    have hlaw0 : P.map (levelProc (Y n) 0) = (gibbsRef D N).map e := by
      have h0 : levelProc (Y n) 0 = e ∘ X 0 := by
        funext ω
        unfold levelProc
        rw [(hY n).init ω, b15e_mk_initLift]
        rfl
      rw [h0, ← Measure.map_map e.measurable (hS.1.adapted 0), hX0, hGR]
    have := hlevel d N hNd D hDM (by rw [hDV]; exact hV) hinvpos (n : ℝ) P (b15e_shiftFil ℱ) W'
      (b15e_initLift X) (Y n) hflow _ ρ hρm hρb (by rw [hlaw0]; exact hρlaw) Φ hF a T ha hT m hm
    refine this.trans (le_of_eq ?_)
    congr 1
    ring
  -- Fatou in the level
  have hmeasY : ∀ n t, Measurable (levelProc (Y n) t) := by
    intro n t
    refine sm_measurable_levelProc _ t ?_
    exact ((hY n).adapted t).mono ((b15e_shiftFil ℱ).le t) le_rfl
  have hev' : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ a + T →
      levelProc (Y n) t ω = e (X t.toNNReal ω) := by
    filter_upwards [hev] with ω hω
    filter_upwards [hω] with n hn t ht0 htT
    have := hn t.toNNReal (by rw [Real.coe_toNNReal t ht0]; exact htT)
    have h1 : (fun i => Torus.mk (Y n t ω i)) = X t.toNNReal ω := by
      rw [← this]; funext i; simp [b15c_regProcess, projectPath, Real.coe_toNNReal t ht0]
    unfold levelProc
    rw [h1]
  have hfat := sm_fatou_core P (fun n => levelProc (Y n)) (fun t ω => e (X t.toNNReal ω)) Φ
    hΦc.measurable hmeasY a T ha hT m hev'
    (fun n => 40 * T * D.invβ *
      ((b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) *
        (gibbsPartition D N)⁻¹).toReal *
        ∫ x, g x ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ)))))
    (40 * T * D.invβ * ∫ X', g (e X') ∂(gibbsRef D N)) (hlim.const_mul _) hbound
  rw [hE, hDinv] at hfat
  simpa [hΦ] using hfat

end EQLZSm

end MD

end HRS

end
