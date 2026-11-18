import HRS.Main.T25PAux29

/-!
# T25P, part 30: re-basing a linear fluctuation solution on an independent initial datum

If `(Y₀, Y)` is a linear fluctuation solution on `P'` and `κ` a probability law on `E_m`, then
`Ȳ^t(ω', x) = Y^t(ω') - V^{t,0} Y₀(ω') + V^{t,0} x` is a linear fluctuation solution on `P' ⊗ κ` with initial datum `x ~ κ`
(same Gaussian part `Z = Y - V Y₀`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_rebase (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ} {T' : ℝ} (hT' : 0 < T')
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hplain : IsPlainEvolution Vev T') {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω' : Type} [mΩ' : MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (hY₀ : Measurable Y₀) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T' Y₀ Y)
    (κ : Measure (NegSobolev d m)) [IsProbabilityMeasure κ] :
    IsLinearFluctuationSolution (P'.prod κ) htr.dyn ρ m β⁻¹ T'
      (fun w : Ω' × NegSobolev d m => w.2)
      (fun t w => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2) where
  init := by
    have h0 : Vev 0 0 = 1 := hplain.1 0 ⟨le_rfl, hT'.le⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hY.init] with w hw
    have h1x : ∀ x : NegSobolev d m, Vev 0 0 x = x := fun x => by rw [h0]; rfl
    simp only [h1x, hw]
    abel
  cont := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hY.cont] with w hw
    exact (hw.sub (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2 (Y₀ w.1))).add
      (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2 w.2)
  meas := fun t => by
    have h1 : Measurable fun w : Ω' × NegSobolev d m => Y t w.1 := (hY.meas t).comp measurable_fst
    have h2 : Measurable fun w : Ω' × NegSobolev d m => Vev t 0 (Y₀ w.1) :=
      (Vev t 0).continuous.measurable.comp (hY₀.comp measurable_fst)
    have h3 : Measurable fun w : Ω' × NegSobolev d m => Vev t 0 w.2 :=
      (Vev t 0).continuous.measurable.comp measurable_snd
    exact (h1.sub h2).add h3
  gaussian_part := by
    intro p ts φ hts hφ
    obtain ⟨hind, hlaw⟩ := hY.gaussian_part p ts φ hts hφ
    set GY : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) with hGY
    have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
      HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
    have hGeq : (fun w : Ω' × NegSobolev d m => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Y (ts a) w.1 - Vev (ts a) 0 (Y₀ w.1) + Vev (ts a) 0 w.2) (φ a) -
          NegSobolev.eval w.2 (propagator htr.dyn ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) =
        fun w => GY w.1 := by
      funext w
      ext a
      have h1 := hdual 0 (ts a) le_rfl (hts a).1 (Y₀ w.1) (φ a) (hφ a)
      have h2 := hdual 0 (ts a) le_rfl (hts a).1 w.2 (φ a) (hφ a)
      have hadd : NegSobolev.eval (Y (ts a) w.1 - Vev (ts a) 0 (Y₀ w.1) + Vev (ts a) 0 w.2) (φ a) =
          NegSobolev.eval (Y (ts a) w.1) (φ a) - NegSobolev.eval (Vev (ts a) 0 (Y₀ w.1)) (φ a) +
            NegSobolev.eval (Vev (ts a) 0 w.2) (φ a) := by
        rw [← gfb4_ell_apply (hmemφ a), map_add, map_sub, gfb4_ell_apply (hmemφ a),
          gfb4_ell_apply (hmemφ a), gfb4_ell_apply (hmemφ a)]
      simp only [hGY, PiLp.sub_apply, WithLp.ofLp_toLp, hadd, h1, h2]
      ring
    have hGYm : Measurable GY := by
      refine measurable_toLp_eval fun a => ?_
      have hmemU : MemSobolev m (propagator htr.dyn ρ 0 (ts a) (φ a)) := by
        exact t25p_memSobolev_propagator hd htr hdual hK le_rfl (hts a).1
          (hKb 0 (ts a) le_rfl (hts a).1 (hts a).2) (hφ a)
      exact ((continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)).sub
        ((continuous_eval_const hmemU).measurable.comp hY₀)
    refine ⟨?_, ?_⟩
    · rw [hGeq]
      exact indepFun_prod (X := GY) (Y := fun x : NegSobolev d m => x) hGYm measurable_id
    · rw [hGeq]
      have : (P'.prod κ).map (fun w : Ω' × NegSobolev d m => GY w.1) = P'.map GY := by
        rw [← Function.comp_def GY Prod.fst, ← Measure.map_map hGYm measurable_fst, Measure.map_fst_prod,
          measure_univ, one_smul]
      show (P'.prod κ).map _ = _
      rw [this]
      exact hlaw

end HRS.T25P
