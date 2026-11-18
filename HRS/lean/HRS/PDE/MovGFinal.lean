import HRS.PDE.MovGAux9
import HRS.PDE.MovSpec3

/-!
# MOVG Final: `movT_logK_integral` (normaliser identity)

`movT_logK_integral_proof` is the statement of `HRS.movT_logK_integral` (MovSpec3.lean), proved from the chain
MovGAux1-9 (see the plan in the header of MovGAux1).  Proof summary: `log K_N(ρ^r) = Φ(r) = -(βN/2) c₃(r) + log J(r)` on `[0,T]`,
`Φ` is continuous there and `Φ' = βN E_{Q_r}[C_N]` on `(0,T)` with a uniform bound; fundamental theorem of calculus.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_logK_integral_proof (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) :
    IntegrableOn (fun r => ∫ X, movT_comm D N ρ r X ∂(movT_Q (periodicRiesz d D.s) D N ρ r))
      (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) =
      D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t,
        ∫ X, movT_comm D N ρ r X ∂(movT_Q (periodicRiesz d D.s) D N ρ r) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hβ := h.pos_temp
  have hβpos : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rcases lt_trichotomy T 0 with hT | hT | hT
  · rw [Set.Icc_eq_empty (not_le.2 hT)]
    exact ⟨integrableOn_empty, fun t ht => absurd ht (by simp)⟩
  · subst hT
    have h0 : (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 0) = 0 :=
      Measure.restrict_eq_zero.2 (by simp)
    refine ⟨?_, fun t ht => ?_⟩
    · unfold IntegrableOn
      rw [h0]
      exact integrable_zero_measure
    · have : t = 0 := le_antisymm ht.2 ht.1
      subst this
      rw [h0]
      simp
  · obtain ⟨ρt, hρt⟩ := h.classical
    set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
    set β : ℝ := D.invβ⁻¹ with hβdef
    set Φ := movg_Phi D n ρ with hΦ
    -- continuity
    have hcont : ContinuousOn Φ (Set.Icc (0 : ℝ) T) := by
      refine (continuousOn_const.mul (movg_continuousOn_c3 D hρt)).add
        (ContinuousOn.log (movg_continuousOn_J D hβ hρt h.pos n) fun r hr => ?_)
      exact (movg_J_pos (b15_one_le_d D) D hβ (mova_continuous_of_isCk (h.ck r hr)) (h.pos r hr) n).ne'
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt Φ (β * Nr * movg_E D n ρ t) t :=
      fun t ht => movg_hasDerivAt_Phi D hβ h hT hρt n ht
    obtain ⟨B, hB⟩ := movg_Phi_deriv_bound D hβ h hT hρt n
    have hβN : 0 < β * Nr := mul_pos hβpos hNpos
    -- integrability of `E`
    have hEm : AEStronglyMeasurable (movg_E D n ρ) (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
      refine (((measurable_deriv Φ).div_const (β * Nr)).aestronglyMeasurable).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      show deriv Φ t / (β * Nr) = _
      rw [(hderiv t ht).deriv]
      field_simp
    have hEIoo : IntegrableOn (movg_E D n ρ) (Set.Ioo (0 : ℝ) T) := by
      refine Integrable.mono' (g := fun _ => B / (β * Nr)) (integrable_const _) hEm ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have := hB t ht
      rw [abs_mul, abs_of_pos hβN] at this
      simpa [Real.norm_eq_abs] using (le_div_iff₀' hβN).2 this
    have hEIcc : IntegrableOn (movg_E D n ρ) (Set.Icc (0 : ℝ) T) :=
      (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2 hEIoo
    refine ⟨hEIcc, fun t ht => ?_⟩
    have hΦeq : ∀ r ∈ Set.Icc (0 : ℝ) T, Real.log (gibbsNormalizer (periodicRiesz d D.s) (n + 1) β
        (withDensityReal (ρ r))) = Φ r := fun r hr => movg_Phi_eq D hβ h n hr
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    rw [hΦeq t ht, hΦeq 0 h0]
    rcases eq_or_lt_of_le ht.1 with h0t | h0t
    · subst h0t
      have : (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 0) = 0 := Measure.restrict_eq_zero.2 (by simp)
      simp [this]
    · have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := Φ)
        (f' := fun r => β * Nr * movg_E D n ρ r) h0t.le (hcont.mono (Set.Icc_subset_Icc_right ht.2))
        (fun r hr => hderiv r ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩)
        (by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0t.le]
          exact (hEIcc.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right ht.2))).const_mul _)
      rw [← hFTC, intervalIntegral.integral_of_le h0t.le, integral_Icc_eq_integral_Ioc, integral_const_mul]
      rfl

example := (@movT_logK_integral_proof : type_of% @HRS.movT_logK_integral)

end HRS
