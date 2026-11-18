import HRS.MS.WsStatAux14

/-!
# S21 packet F3b: Fubini for the commutator forcing (stationary case)

`s21_fubini_comm`: in the setting of `field_remainder_centered` (S5.3, `S53Orbit` input, stationary law, the variance hypothesis)
the forcing `c_alpha(r, zeta) = commForcing C s m mu X alpha t r zeta` satisfies, for every `alpha` and `t in [0,T]`,
`E int_0^t c_alpha(r,.) dr = int_0^t E c_alpha(r,.) dr`, with `r |-> E c_alpha(r,.)` integrable on `[0,t]` and `zeta |-> int_0^t c_alpha(r,zeta) dr` integrable.

Proof: as in `s53_field_remainder_centered_of_orbit` (modification `X'` jointly measurable, `S53Var`, mean bound `Cm`,
`s53_alpha_c`: a.s. `int_0^t |c| dr <= g(zeta) + T Cm L` with `g in L^2`), the jointly measurable comparison function
`c~(zeta,r) = D_k(G0 alpha (clamp(t - r)))(X'_r zeta)`, integrable on `P x vol|[0,t]` (Tonelli), then `integral_integral_swap`;
the inner integrals of `c` and `c~` agree on `[0,t]` for `zeta` in the good set.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S53

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B

variable {d : ℕ}

theorem s21_fubini_comm (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m T : ℝ)
    (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) (D : WholeDyn d) (C : WholeCoeff d)
    {b : MultiIndex d → ℝ} {K : ℝ} {G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ}
    (O : S53Orbit C m T K b G0 G1 G2) (CA : ℝ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P D T X₀ W X)
    (hstat0 : ∀ t ∈ Set.Icc (0 : ℝ) T, law P (X (Real.toNNReal t)) = law P (X 0))
    (hvar0 : ∀ f : Euc d → ℝ, MemCb 2 f →
        (N : ℝ≥0∞) * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d s (fun x => gradient f x)) (X 0 ζ) (HRS.Whole.withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d s N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2))
    (α : MultiIndex d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntegrableOn (fun r => ∫ ζ, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P)
        (Set.Icc 0 t) ∧
      ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ) ∂P =
        ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P ∧
      Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
        commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ) P := by
  obtain ⟨Mρ, ctx⟩ := s53_ctx_of_schwartz hd hs0 hsd hρ
  have hNpos : 0 < N := by omega
  have hδ := s53_deltaN_nonneg (d := d) (N := N) s hNpos
  obtain ⟨X', Gs, hGsm, hGs0, hGs, hX'm, hX'j⟩ := s53_modify P X hX.cont hX.adapted
  have hGsae : ∀ᵐ ζ ∂P, ζ ∈ Gs := by
    rw [ae_iff]; exact hGs0
  have hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ := fun t => hGsae.mono fun ζ hζ => hGs ζ hζ t
  have H : S53Var s ρ P X' T CA (deltaN d s N) := by
    refine ⟨hX'm, fun t ht => ?_, fun f hf => ?_⟩
    · rw [Measure.map_congr (hae _), Measure.map_congr (hae 0)]
      exact hstat0 t ht
    · have := hvar0 f hf
      rw [s53_evariance_congr (f := fun ζ => s53_Dk s ρ f (X' 0 ζ)) (g := fun ζ => s53_Dk s ρ f (X 0 ζ))
        ((hae 0).mono fun ζ hζ => by beta_reduce; rw [hζ])]
      exact this
  obtain ⟨Cm, hCm0, hCm⟩ := s53_mean_bound ctx hNpos hδ H
  obtain ⟨g, hgm, hgint, hgpath⟩ :=
    s53_alpha_c (P := P) (X := X) (X' := X') (Gs := Gs) ctx hNpos hδ hT H hCm0 hCm (C := C) (m := m)
      (α := α) (O.hom α) (O.mem0 α) (O.mem1 α) (O.mem2 α) (O.diff0 α) (O.diff1 α)
      (L := K * b α) (O.cb0 α) (O.cb1 α) hX'j hGs hGsae
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  -- the jointly measurable comparison function
  have hc0 : S53Cont T (G0 α) := s53_cont_of_diff (O.mem0 α) (O.mem1 α) (O.diff0 α)
  have hGm := s53_grad_measurable hT (O.mem0 α) hc0
  have hFm : Measurable fun p : ℝ × Euc d => gradient ((fun τ : ℝ => G0 α (s53_clamp T (t - τ))) p.1) p.2 :=
    hGm.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  have hDm := s53_Dk_measurable (N := N) (s := s) ctx.hρ (F := fun τ : ℝ => G0 α (s53_clamp T (t - τ))) hFm
  set ct : Ω × ℝ → ℝ := fun q => s53_Dk s ρ (G0 α (s53_clamp T (t - q.2))) (X' (Real.toNNReal q.2) q.1)
    with hct
  have hpr : Measurable fun q : Ω × ℝ => (q.2, X' (Real.toNNReal q.2) q.1) :=
    measurable_snd.prodMk (hX'j.comp measurable_swap)
  have hctm : Measurable ct := by
    have h := hDm.comp hpr
    exact h
  -- agreement with the forcing
  have hagree : ∀ ζ ∈ Gs, ∀ r ∈ Set.Icc (0 : ℝ) t,
      commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ = ct (ζ, r) := by
    intro ζ hζ r hr
    have hrT : r ≤ T := hr.2.trans ht.2
    have h1 : propagatorW C r t (oscTestFun m α) = G0 α (t - r) := O.hom α r t hr.1 hr.2 ht.2
    have hcl : s53_clamp T (t - r) = t - r :=
      s53_clamp_of_mem ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    rw [s53_comm_eq, h1, hct]
    simp only [hcl, hGs ζ hζ]
  -- integrability of `ct` on the product
  have hbound : ∀ ζ ∈ Gs, ∫⁻ r in Set.Icc (0 : ℝ) t, ‖ct (ζ, r)‖ₑ ≤
      g ζ + ENNReal.ofReal T * ENNReal.ofReal (Cm * (K * b α)) := by
    intro ζ hζ
    obtain ⟨-, h2, -⟩ := hgpath ζ hζ t ht
    refine le_trans (le_of_eq ?_) h2
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [hagree ζ hζ r hr]
  have hgfin : ∫⁻ ζ, g ζ ∂P < ⊤ := by
    have h1 : ∫⁻ ζ, g ζ ∂P ≤ ∫⁻ ζ, (1 + g ζ ^ 2) ∂P := lintegral_mono fun ζ => by
      by_cases h : g ζ ≤ 1
      · exact h.trans le_self_add
      · push_neg at h
        calc g ζ ≤ g ζ ^ 2 := by
              have := h.le
              calc g ζ = g ζ ^ 1 := (pow_one _).symm
                _ ≤ g ζ ^ 2 := pow_le_pow_right₀ this (by norm_num)
          _ ≤ 1 + g ζ ^ 2 := le_add_self
    refine lt_of_le_of_lt h1 ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ?_⟩
    have hW : (N : ℝ≥0∞) * ∫⁻ ζ, g ζ ^ 2 ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hgint
      simp [ENNReal.mul_eq_top, ENNReal.add_eq_top]
    have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hNpos.ne'
    exact lt_top_iff_ne_top.2 fun h => hW (by rw [h, ENNReal.mul_top hNne])
  have hint : Integrable ct (P.prod μ) := by
    refine ⟨hctm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖ct q‖ₑ ∂(P.prod μ) < ⊤
    rw [lintegral_prod _ hctm.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono_ae (hGsae.mono fun ζ hζ => hbound ζ hζ)) ?_
    rw [lintegral_add_left' hgm.aemeasurable, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨hgfin, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  have hswap := integral_integral_swap (μ := P) (ν := μ) (f := fun ζ r => ct (ζ, r)) hint
  have hint2 : Integrable (fun r => ∫ ζ, ct (ζ, r) ∂P) μ := hint.integral_prod_right
  -- transfer to the forcing
  have e1 : ∀ ζ ∈ Gs, ∫ r in Set.Icc (0 : ℝ) t, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ =
      ∫ r, ct (ζ, r) ∂μ := fun ζ hζ =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => hagree ζ hζ r hr
  have e2 : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ ζ, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P =
      ∫ ζ, ct (ζ, r) ∂P := fun r hr =>
    integral_congr_ae (hGsae.mono fun ζ hζ => hagree ζ hζ r hr)
  have hL : ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ) ∂P =
      ∫ ζ, ∫ r, ct (ζ, r) ∂μ ∂P := integral_congr_ae (hGsae.mono fun ζ hζ => e1 ζ hζ)
  have hR : ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P =
      ∫ r, ∫ ζ, ct (ζ, r) ∂P ∂μ :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => e2 r hr
  refine ⟨?_, ?_, ?_⟩
  · refine (hint2.congr ?_ : IntegrableOn _ _ _)
    rw [hμ, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun r hr => (e2 r hr).symm
  · rw [hL, hR]
    exact hswap
  · exact hint.integral_prod_left.congr (hGsae.mono fun ζ hζ => (e1 ζ hζ).symm)

end HRS.MS.S53
