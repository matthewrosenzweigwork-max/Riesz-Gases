/-
# HRS.Equilibrium.Q84dAuxN — packet Q84d: the integration-by-parts lemma along coordinate lines
-/
import HRS.Equilibrium.Q84dAuxM

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {N : ℕ}

theorem lineCfg_integral_comp (i : Fin N) (k : Fin d) (t : ℝ) (g : Config d N → ℝ) :
    ∫ Y, g (lineCfg i k Y t) = ∫ Y, g Y := by
  have h := q84d_translate_mp (d := d) (N := N) (Pi.single i (Torus.mk (t • ek k)))
  set z : Config d N := Pi.single i (Torus.mk (t • ek k)) with hz
  have h' : MeasurePreserving (MeasurableEquiv.addRight z) volume volume := h
  have := h'.integral_comp' (f := MeasurableEquiv.addRight z) g
  simpa [lineCfg_eq_add] using this

/-- **Integration by parts along a closed coordinate line.** -/
theorem q84d_ibp (i : Fin N) (k : Fin d) {v w : Config d N → ℝ} (hvm : Measurable v)
    (hvi : Integrable v volume)
    (hline : ∀ᵐ Y ∂(volume : Measure (Config d N)), ∀ t : ℝ,
      HasDerivAt (fun τ => w (lineCfg i k Y τ)) (v (lineCfg i k Y t)) t) :
    ∫ Y, v Y = 0 := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hν
  have : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  set Φ : Config d N × ℝ → ℝ := fun p => v (lineCfg i k p.1 p.2) with hΦ
  have hΦm : Measurable Φ := hvm.comp (q84d_measurable_lineCfg i k)
  have hint_t : ∀ t, Integrable (fun Y : Config d N => Φ (Y, t)) volume := fun t =>
    (lineCfg_mp i k t).integrable_comp_of_integrable hvi
  have hΦi : Integrable Φ ((volume : Measure (Config d N)).prod ν) := by
    refine (integrable_prod_iff' hΦm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hint_t, ?_⟩
    have : (fun t : ℝ => ∫ Y, ‖Φ (Y, t)‖) = fun _ => ∫ Y, ‖v Y‖ := by
      funext t
      exact lineCfg_integral_comp i k t (fun Y => ‖v Y‖)
    rw [this]
    exact integrable_const _
  have h1 := integral_prod Φ hΦi
  have h2 := integral_prod_symm Φ hΦi
  have hR : ∫ t, ∫ Y, Φ (Y, t) ∂volume ∂ν = ∫ Y, v Y := by
    have : (fun t : ℝ => ∫ Y, Φ (Y, t)) = fun _ => ∫ Y, v Y := by
      funext t; exact lineCfg_integral_comp i k t v
    rw [this, integral_const]
    simp [hν, Measure.real, Real.volume_Ioc]
  have hL : ∫ Y, ∫ t, Φ (Y, t) ∂ν = 0 := by
    have : ∀ᵐ Y ∂(volume : Measure (Config d N)), ∫ t, Φ (Y, t) ∂ν = 0 := by
      filter_upwards [hline, hΦi.prod_right_ae] with Y hY hYi
      have hii : IntervalIntegrable (fun t => v (lineCfg i k Y t)) volume 0 1 :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hYi
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun τ => w (lineCfg i k Y τ)) (f' := fun t => v (lineCfg i k Y t)) (a := 0) (b := 1)
        (fun t _ => hY t) hii
      rw [lineCfg_zero, lineCfg_one, sub_self] at this
      rw [intervalIntegral.integral_of_le zero_le_one] at this
      exact this
    rw [integral_congr_ae this, integral_zero]
  rw [← hR, ← h2, h1, hL]

/-! ### Almost every coordinate line avoids all collisions (`d ≥ 2`) -/

theorem q84d_ae_coord_ne (m : Fin d) :
    ∀ᵐ p ∂(volume : Measure (Torus d × Torus d)), p.1 m ≠ p.2 m := by
  have hm : MeasurableSet {p : Torus d × Torus d | p.1 m = p.2 m} :=
    measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_fst)
      ((measurable_pi_apply m).comp measurable_snd)
  rw [ae_iff]
  have : {p : Torus d × Torus d | ¬p.1 m ≠ p.2 m} = {p : Torus d × Torus d | p.1 m = p.2 m} := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_apply hm]
  have h0 : ∀ x : Torus d, (volume : Measure (Torus d))
      (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 m = p.2 m}) = 0 := by
    intro x
    have e : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 m = p.2 m} =
        (fun y : Torus d => y m) ⁻¹' {x m} := by
      ext y; simp [eq_comm]
    rw [e]
    have hmp : MeasurePreserving (fun y : Torus d => y m) volume (volume : Measure UnitAddCircle) :=
      measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) m
    rw [hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
    exact volume_singleton_circle _
  simp_rw [h0]
  simp

theorem q84d_ae_line_free (hd : 2 ≤ d) (i : Fin N) (k : Fin d) :
    ∀ᵐ Y ∂(volume : Measure (Config d N)), ∀ t : ℝ, lineCfg i k Y t ∉ collisionSet d N := by
  -- a coordinate `m ≠ k`
  obtain ⟨m, hmk⟩ : ∃ m : Fin d, m ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
  have h1 : ∀ j : Fin N, ∀ᵐ Y ∂(volume : Measure (Config d N)), j ≠ i → Y i m ≠ Y j m := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun Y h => absurd hji h
    · have := (q84d_pair_mp (d := d) (N := N) (Ne.symm hji)).quasiMeasurePreserving.ae
        (q84d_ae_coord_ne (d := d) m)
      filter_upwards [this] with Y hY _ using hY
  have h2 : ∀ᵐ Y ∂(volume : Measure (Config d N)), ∀ j : Fin N, j ≠ i → Y i m ≠ Y j m := by
    rw [ae_all_iff]; intro j; exact h1 j
  filter_upwards [h2, q84d_ae_not_collision (N := N) (d := d) (by omega)] with Y hY hYc t
  rintro ⟨a, b, hab, hX⟩
  have hdiff : ∀ a b : Fin N, a ≠ b → (lineCfg i k Y t) a ≠ (lineCfg i k Y t) b := by
    intro a b hab hX
    by_cases ha : a = i
    · subst ha
      have hb : b ≠ a := hab.symm
      simp only [lineCfg, Function.update_self, Function.update_of_ne hb] at hX
      have := congrFun hX m
      simp [Torus.mk, ek, hmk] at this
      exact hY b hb this
    · by_cases hb : b = i
      · subst hb
        simp only [lineCfg, Function.update_self, Function.update_of_ne ha] at hX
        have := congrFun hX m
        simp [Torus.mk, ek, hmk] at this
        exact hY a ha this.symm
      · simp only [lineCfg, Function.update_of_ne ha, Function.update_of_ne hb] at hX
        exact hYc ⟨a, b, hab, hX⟩
  exact hdiff a b hab hX

end HRS.Q84d

end
