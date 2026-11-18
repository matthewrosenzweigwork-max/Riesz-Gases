import HRS.Dynamics.Setup

/-!
# EQ-LAW (packet `eq_path_stationary`), part 2: transfer lemmas for `IsStrongSolution`

* `eqlaw_shift_integral`: `∫_{[0,a+b]} F - ∫_{[0,a]} F = ∫_{[0,b]} F(a + ·)`.
* `eqlaw_isStrongSolution_shift`: a strong solution on the horizon `u + T` started at time `u` is a strong solution on `T`
  with initial datum `X u` and driver `s ↦ W(u+s) - W u`.
* `eqlaw_isStrongSolution_congr`: modifications of the initial datum / the driver (a.s.).
* `eqlaw_isStrongSolution_comp`: composition with a measure-preserving map `J : Ω → Σ`.
* `eqlaw_isStrongSolution_mono`: the horizon can be decreased.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQLawPath

theorem eqlaw_shift_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hF : IntegrableOn F (Set.Icc 0 (a + b))) :
    IntegrableOn (fun r => F (a + r)) (Set.Icc 0 b) ∧
      (∫ r in Set.Icc (0 : ℝ) (a + b), F r) - (∫ r in Set.Icc (0 : ℝ) a, F r) =
        ∫ r in Set.Icc (0 : ℝ) b, F (a + r) := by
  have hab : (0 : ℝ) ≤ a + b := by linarith
  have hI : IntervalIntegrable F volume 0 (a + b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hF
  have hI1 : IntervalIntegrable F volume 0 a :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le ha]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hI2 : IntervalIntegrable F volume a (a + b) :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc ha le_rfl)
  have hI3 : IntervalIntegrable (fun r => F (a + r)) volume 0 b := by
    have := hI2.comp_add_left a
    simpa using this
  have hc : ∀ c : ℝ, 0 ≤ c → (∫ r in Set.Icc (0 : ℝ) c, F r) = ∫ r in (0 : ℝ)..c, F r := by
    intro c hc
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hc]
  have hc' : (∫ r in Set.Icc (0 : ℝ) b, F (a + r)) = ∫ r in (0 : ℝ)..b, F (a + r) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hb]
  refine ⟨?_, ?_⟩
  · exact (integrableOn_Icc_iff_integrableOn_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 hI3)
  · rw [hc _ hab, hc _ ha, hc', intervalIntegral.integral_comp_add_left (fun r => F r) a]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    simp


variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem eqlaw_isStrongSolution_mono {P : Measure Ω} {D : DynData d} {T T' : ℝ} (hT : T' ≤ T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : IsStrongSolution P D T X₀ W X) : IsStrongSolution P D T' X₀ W X where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    exact ⟨Y, hY.mono fun ω hω t ht => hω t (ht.trans hT), hX⟩
  init := h.init
  cont := h.cont
  adapted := h.adapted
  no_collision := h.no_collision.mono fun ω hω t ht => hω t (ht.trans hT)

theorem eqlaw_isStrongSolution_congr {P : Measure Ω} {D : DynData d} {T : ℝ}
    {X₀ X₀' : Ω → Config d N} {W W' : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : IsStrongSolution P D T X₀ W X) (h0 : ∀ᵐ ω ∂P, X₀ ω = X₀' ω)
    (hW : ∀ᵐ ω ∂P, ∀ t, W t ω = W' t ω) : IsStrongSolution P D T X₀' W' X where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    refine ⟨Y, ?_, hX⟩
    filter_upwards [hY, hW] with ω hω hWω t ht
    obtain ⟨h1, h2⟩ := hω t ht
    refine ⟨h1, fun i => ?_⟩
    rw [h2 i, hWω t, hWω 0]
  init := by
    filter_upwards [h.init, h0] with ω h1 h2
    rw [h1, h2]
  cont := h.cont
  adapted := h.adapted
  no_collision := h.no_collision

theorem eqlaw_isStrongSolution_comp {S : Type*} [MeasurableSpace S] {P : Measure Ω} {Q : Measure S}
    (J : Ω → S) (hJ : Measurable J) (hPJ : P.map J = Q) {D : DynData d} {T : ℝ}
    {X₀ : S → Config d N} {W : ℝ≥0 → S → (Fin N → Euc d)} {X : ℝ≥0 → S → Config d N}
    (h : IsStrongSolution Q D T X₀ W X) :
    IsStrongSolution P D T (fun ω => X₀ (J ω)) (fun t ω => W t (J ω)) (fun t ω => X t (J ω)) where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    have hY' := ae_of_ae_map hJ.aemeasurable (hPJ ▸ hY)
    refine ⟨fun t ω => Y t (J ω), hY', ?_⟩
    funext t ω
    rw [hX]
    rfl
  init := ae_of_ae_map hJ.aemeasurable (hPJ ▸ h.init)
  cont := ae_of_ae_map hJ.aemeasurable (hPJ ▸ h.cont)
  adapted t := (h.adapted t).comp hJ
  no_collision := ae_of_ae_map hJ.aemeasurable (hPJ ▸ h.no_collision)

theorem eqlaw_isStrongSolution_shift {P : Measure Ω} {D : DynData d} {u : ℝ≥0} {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : IsStrongSolution P D ((u : ℝ) + T) X₀ W X) :
    IsStrongSolution P D T (X u) (fun s ω => W (u + s) ω - W u ω) (fun s => X (u + s)) where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    refine ⟨fun s => Y (u + s), ?_, by subst hX; rfl⟩
    filter_upwards [hY] with ω hω t ht
    have hT0 : (0 : ℝ) ≤ T := le_trans (NNReal.coe_nonneg t) ht
    have hut : ((u + t : ℝ≥0) : ℝ) ≤ (u : ℝ) + T := by rw [NNReal.coe_add]; linarith
    have huu : ((u : ℝ≥0) : ℝ) ≤ (u : ℝ) + T := by linarith
    obtain ⟨hi1, he1⟩ := hω (u + t) hut
    obtain ⟨hi2, he2⟩ := hω u huu
    set F : Fin N → ℝ → Euc d := fun i x => particleDrift D (projectPath Y (Real.toNNReal x) ω) i
      with hF
    have hcoe : ((u + t : ℝ≥0) : ℝ) = (u : ℝ) + t := NNReal.coe_add u t
    have hsh : ∀ i, IntegrableOn (fun r => F i ((u : ℝ) + r)) (Set.Icc 0 (t : ℝ)) ∧
        (∫ r in Set.Icc (0 : ℝ) ((u : ℝ) + t), F i r) - (∫ r in Set.Icc (0 : ℝ) (u : ℝ), F i r) =
          ∫ r in Set.Icc (0 : ℝ) (t : ℝ), F i ((u : ℝ) + r) := fun i =>
      eqlaw_shift_integral (F i) (NNReal.coe_nonneg u) (NNReal.coe_nonneg t) (by rw [← hcoe]; exact hi1 i)
    have hconv : ∀ i, Set.EqOn (fun r : ℝ => particleDrift D
        (projectPath (fun s => Y (u + s)) (Real.toNNReal r) ω) i) (fun r => F i ((u : ℝ) + r))
        (Set.Icc 0 (t : ℝ)) := by
      intro i r hr
      have : Real.toNNReal ((u : ℝ) + r) = u + Real.toNNReal r := by
        rw [Real.toNNReal_add (NNReal.coe_nonneg u) hr.1, Real.toNNReal_coe]
      show _ = particleDrift D (projectPath Y (Real.toNNReal ((u : ℝ) + r)) ω) i
      rw [this]
      rfl
    refine ⟨fun i => (hsh i).1.congr_fun (hconv i).symm measurableSet_Icc, fun i => ?_⟩
    rw [setIntegral_congr_fun measurableSet_Icc (hconv i), ← (hsh i).2]
    have e1 : Y (u + t) ω i = (Y 0 ω i + ∫ r in Set.Icc (0 : ℝ) ((u : ℝ) + t), F i r) +
        √(2 * D.invβ) • (W (u + t) ω i - W 0 ω i) := by
      have := he1 i
      rw [hcoe] at this
      exact this
    have e2 : Y u ω i = (Y 0 ω i + ∫ r in Set.Icc (0 : ℝ) (u : ℝ), F i r) +
        √(2 * D.invβ) • (W u ω i - W 0 ω i) := he2 i
    simp only [add_zero]
    rw [e1, e2]
    simp only [Pi.sub_apply, sub_self, sub_zero, smul_sub]
    abel
  init := by
    filter_upwards [h.init] with ω hω
    simp
  cont := by
    filter_upwards [h.cont] with ω hω i
    exact (hω i).comp (continuous_const.add continuous_id)
  adapted s := h.adapted (u + s)
  no_collision := by
    filter_upwards [h.no_collision] with ω hω t ht
    exact hω (u + t) (by rw [NNReal.coe_add]; linarith)

end HRS.MD.EQLawPath
