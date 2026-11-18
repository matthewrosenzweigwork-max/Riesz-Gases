import HRS.MC.E214E3

/-!
# E214E4: the coupled pair (final assembly of P1)

`exists_coupled_pair_proof`: the statement of `HRS.MC.E214D.exists_coupled_pair` (the hypotheses of
`HRS.Sec7.quadratic_relaxation`): on `Ω = (E_r × E_r) × Ω_G`, `P = (ν₀ ⊗ νs) ⊗ P_G`, `Y₀ = pr₁₁`, `Ys₀ = pr₁₂`,
`η t = Vev t 0 Y₀ + Zs t (pr₂)`, `ηs t = Vev' t 0 Ys₀ + Zs' t (pr₂)` with `(Zs, Zs')` the convolutions of the two
components of ONE block martingale on `E_r × E_r` (`e214d_pair_components`, `e214d_global_conv`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214E

open HRS HRS.Sec7 HRS.Uniform HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213N HRS.MC.E214D

variable {d : ℕ}

theorem measurable_toLp_sum {ι ι' : Type} [Fintype ι] [Fintype ι'] {Ω : Type*} [MeasurableSpace Ω]
    {f : ι ⊕ ι' → Ω → ℝ} (hf : ∀ a, Measurable (f a)) :
    Measurable fun ω => (WithLp.toLp 2 fun a => f a ω : EuclideanSpace ℝ (ι ⊕ ι')) :=
  (PiLp.continuous_toLp 2 (fun _ : ι ⊕ ι' => ℝ)).measurable.comp (measurable_pi_iff.2 hf)

/-- Measurability of the noise part of `η t = Vev t 0 Y₀ + Zs t`, on `E × Ω_G`. -/
theorem noisePart_meas {D : DynData d} {ρ : ℝ → Torus d → ℝ} {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution D ρ m Vev)
    {Ωg : Type} [MeasurableSpace Ωg] {Zs : ℝ → Ωg → NegSobolev d m} (hZm : ∀ t, Measurable (Zs t))
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, 0 ≤ ts a)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (fun q : NegSobolev d m × Ωg => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Vev (ts a) 0 q.1 + Zs (ts a) q.2) (φ a) -
          NegSobolev.eval q.1 (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) =
      fun q => (WithLp.toLp 2 fun a => NegSobolev.eval (Zs (ts a) q.2) (φ a) : EuclideanSpace ℝ (Fin p)) := by
  funext q
  ext a
  show NegSobolev.eval (Vev (ts a) 0 q.1 + Zs (ts a) q.2) (φ a) -
    NegSobolev.eval q.1 (propagator D ρ 0 (ts a) (φ a)) = NegSobolev.eval (Zs (ts a) q.2) (φ a)
  rw [HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth m (hφ a)),
    hdual 0 (ts a) le_rfl (hts a) q.1 (φ a) (hφ a)]
  ring

theorem noisePart_meas' {D : DynData d} {ρ : ℝ → Torus d → ℝ} {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution D ρ m Vev)
    {Ωg : Type} [MeasurableSpace Ωg] {Zs : ℝ → Ωg → NegSobolev d m} (hZm : ∀ t, Measurable (Zs t))
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, 0 ≤ ts a)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    Measurable fun q : NegSobolev d m × Ωg => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Vev (ts a) 0 q.1 + Zs (ts a) q.2) (φ a) -
          NegSobolev.eval q.1 (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p)) := by
  rw [noisePart_meas hdual hZm p ts φ hts hφ]
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hGz : Measurable fun ω : Ωg => (WithLp.toLp 2 fun a => NegSobolev.eval (Zs (ts a) ω) (φ a) :
      EuclideanSpace ℝ (Fin p)) :=
    HRS.Uniform.Q54c.measurable_toLp_eval fun a =>
      (HRS.Uniform.Q54c.continuous_eval_const (hmemφ a)).measurable.comp (hZm _)
  exact hGz.comp measurable_snd

end HRS.MC.E214E

end
