import HRS.MS.Fp81S21WickApprox15

/-! Particle finite-rank coordinate families in time L². -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The actual finite-rank particle coefficient sum has a jointly measurable
version and random time-L² sections, uniformly over shifts and horizons. -/
theorem fp81s21_particle_rankKernel_time_fields (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ m : ℕ,
      ∀ D : Fin m → fp81s21_RankKernel p.d,
      ∃ M : ℝ, ∃ q : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
          q u ω = ∑ j : Fin m,
            fp81s21_particleQuad A u (D j).kernel ω • fp81s21_coeffBasis j) ∧
        (∀ u, 0 ≤ u → MemLp (q u) 2 A.P ∧
          (∫ ω, ‖q u ω‖ ^ 2 ∂A.P) ≤ M) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
          ∃ U : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            fp81s21_TimeL2Rep A.P q M a H U := by
  obtain ⟨δ₀, hδ₀, hhalf, hfield⟩ := fp81s21_particle_rankKernel_time_field p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R N hN A m D
  choose M q hqm hqe hqsec hqtime using
    fun j : Fin m => hfield δ hδ hδle R N hN A (D j) j
  let Q : ℝ → A.Ω → r26t6_Coeff := fun u ω => ∑ j : Fin m, q j u ω
  let MQ : ℝ := (m : ℝ) * ∑ j : Fin m, M j
  have hQm : Measurable (Function.uncurry Q) :=
    Finset.measurable_sum _ fun j _ => hqm j
  have hQe : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      Q u ω = ∑ j : Fin m,
        fp81s21_particleQuad A u (D j).kernel ω • fp81s21_coeffBasis j := by
    have hall : ∀ᵐ ω ∂A.P, ∀ j : Fin m, ∀ u : ℝ, 0 ≤ u →
        q j u ω = fp81s21_particleQuad A u (D j).kernel ω • fp81s21_coeffBasis j :=
      ae_all_iff.mpr hqe
    filter_upwards [hall] with ω hω u hu
    exact Finset.sum_congr rfl (fun j _ => hω j u hu)
  have hQsec : ∀ u, 0 ≤ u → MemLp (Q u) 2 A.P ∧
      (∫ ω, ‖Q u ω‖ ^ 2 ∂A.P) ≤ MQ := by
    intro u hu
    have hmem : MemLp (Q u) 2 A.P := by
      have hm := memLp_finsetSum' Finset.univ (fun j _ => (hqsec j u hu).1)
      convert hm using 1
      funext ω
      simp [Q, Finset.sum_apply]
    have hint : ∀ j : Fin m, Integrable (fun ω => ‖q j u ω‖ ^ 2) A.P :=
      fun j => (hqsec j u hu).1.integrable_norm_pow (by norm_num)
    have hpoint : ∀ ω, ‖Q u ω‖ ^ 2 ≤ (m : ℝ) * ∑ j : Fin m, ‖q j u ω‖ ^ 2 := by
      intro ω
      have ht : ‖Q u ω‖ ≤ ∑ j : Fin m, ‖q j u ω‖ := norm_sum_le _ _
      have hs : (∑ j : Fin m, ‖q j u ω‖) ^ 2 ≤
          (m : ℝ) * ∑ j : Fin m, ‖q j u ω‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin m => ‖q j u ω‖))
      exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs
    have hsumint : Integrable (fun ω => (m : ℝ) * ∑ j : Fin m, ‖q j u ω‖ ^ 2) A.P :=
      (integrable_finset_sum _ (fun j _ => hint j)).const_mul _
    refine ⟨hmem, ?_⟩
    calc
      _ ≤ ∫ ω, (m : ℝ) * ∑ j : Fin m, ‖q j u ω‖ ^ 2 ∂A.P :=
        integral_mono (hmem.integrable_norm_pow (by norm_num)) hsumint hpoint
      _ = (m : ℝ) * ∑ j : Fin m, ∫ ω, ‖q j u ω‖ ^ 2 ∂A.P := by
        rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint j)]
      _ ≤ MQ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
        exact Finset.sum_le_sum fun j _ => (hqsec j u hu).2
  refine ⟨MQ, Q, hQm, hQe, hQsec, ?_⟩
  intro a ha H hH
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × A.Ω → r26t6_Coeff := fun z => Q (a + z.1) z.2
  have hgm : Measurable g := hQm.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hsec : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 A.P ∧
      (∫ ω, ‖g (t, ω)‖ ^ 2 ∂A.P) ≤ MQ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hQsec (a + t) (add_nonneg ha ht.1)
  obtain ⟨hg, hbnd⟩ := fp81s21_memLp_prod_of_section_bound dt A.P g hgm MQ hsec
  have hi : Integrable (fun z => ‖g z‖ ^ 2) (dt.prod A.P) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hs : ∀ᵐ ω ∂A.P, MemLp (fun t => g (t, ω)) 2 dt := by
    filter_upwards [hi.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
  obtain ⟨U, hUm, hUL, hUeq, hUin⟩ := fp81s21_time_section_exists A.P H g hgm hg
  refine ⟨U, hUm, hUL, ?_, ?_⟩
  · rw [hUin]
    simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hH] using hbnd
  · filter_upwards [hs, hUeq] with ω hω heq
    exact ⟨hω, heq⟩

#print axioms fp81s21_particle_rankKernel_time_fields
end HRS.Fp81.S21
end
