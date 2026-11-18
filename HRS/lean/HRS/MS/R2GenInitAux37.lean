import HRS.MS.R2GenInitAux36

/-!
# S10.5 window comparison, packet E3: measurability on the original probability space of the covariance-error functional

`s105_trace_meas`: the functional `ζ ↦ ∫_0^{τ₀} ‖Σ_r(X_r(ζ)) - C̄_r‖_1 dr` of a progressive process is measurable, so the trace bound of the hypothesis
transfers along measure-preserving enlargements.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

theorem s105_trace_meas {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) {N : ℕ} (q : ℝ)
    (Db : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) (hDbm : ∀ u v, Measurable fun r => Db r u v)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) τ₀, ENNReal.ofReal (traceNormForm
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ r) (X (Real.toNNReal (mrrClamp τ₀ r)) ζ k.1)) - Db r))) := by
  have hX := mrr_prog_meas ℱ X hprog hτ
  have hΦm : ∀ k : Fin N × Fin d, Measurable fun p : ℝ × Ω => Real.sqrt (2 * q / N) •
      Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1) := by
    intro k
    have h1 : Measurable fun p : ℝ × Ω => ((p.1, X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1) : ℝ × Euc d) :=
      measurable_fst.prodMk ((measurable_pi_apply k.1).comp hX)
    have hg := (s105_feat_meas hτ h k.2).comp h1
    exact hg.const_smul (Real.sqrt (2 * q / N))
  have hent : ∀ u v : KSpace d m T, Measurable fun p : ℝ × Ω =>
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1)) - Db p.1) u v := by
    intro u v
    simp only [sub_apply]
    refine Measurable.sub ?_ ((hDbm u v).comp measurable_fst)
    have e : ∀ p : ℝ × Ω, hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1)) u v =
        ∑ k : Fin N × Fin d, inner ℝ (Real.sqrt (2 * q / N) •
          Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1)) u *
          inner ℝ (Real.sqrt (2 * q / N) •
          Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1)) v := by
      intro p
      rw [hsCovForm_apply Summable.of_finite, tsum_fintype]
    simp_rw [e]
    exact Finset.measurable_sum _ fun k _ => ((hΦm k).inner measurable_const).mul ((hΦm k).inner measurable_const)
  have hT : Measurable fun p : ℝ × Ω => traceNormForm
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ p.1) (X (Real.toNNReal (mrrClamp τ₀ p.1)) p.2 k.1)) - Db p.1) :=
    HRS.measurable_traceNormForm _ hent
  have hf : Measurable fun p : Ω × ℝ => ENNReal.ofReal (traceNormForm
      (hsCovForm (fun k : Fin N × Fin d => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ p.2) (X (Real.toNNReal (mrrClamp τ₀ p.2)) p.1 k.1)) - Db p.2)) :=
    (hT.comp measurable_swap).ennreal_ofReal
  exact hf.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) τ₀))

end HRS.MS.R2GenInit
