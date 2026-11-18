import HRS.MS.CritForceDefs
import HRS.MS.FeatDecTie
import HRS.MS.FldRemCenTie
import HRS.MS.WsStatAux15

/-!
# S8.2.04: genuine adjoints and integrals for the weighted critical forcing

The qualitative clauses of `HRS.Whole.weighted_critical_forcing`: classical adjoint existence for
every terminal time, almost sure integrability of the `r`-integrands on a common full-measure set,
`P`-integrability of the forcing at each `r` and integrability of its mean in time, and the
resulting pathwise integrability of the centered integrand.  Route: for every natural horizon `H`
the S5.3 orbit of the critical coefficient, `s53_field_remainder_centered_of_orbit` (pathwise
integrability), `s21_fubini_comm` (mean in time) and the first-moment bound `s53_L1_bound`
(integrability in `ζ` at each `r`); a countable intersection over `H` gives the frozen quantifier
order (one null set for all `α` and all `t ≥ 0`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82BD

open HRS HRS.Whole HRS.MS.S53 HRS.MS.Ul HRS.MS.S52B

variable {d : ℕ}

/-- Integrability in `ζ` of the forcing at every fixed `r ∈ [0,t]`, `t ≤ T`. -/
theorem s82_forcing_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m T : ℝ)
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
    (α : MultiIndex d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    Integrable (fun ζ => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ) P := by
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
  have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
  have hcl : s53_clamp T (t - r) ∈ Set.Icc (0 : ℝ) T := s53_clamp_mem hT _
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
  have hagree : ∀ ζ ∈ Gs, commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ = ct (ζ, r) := by
    intro ζ hζ
    have h1 : propagatorW C r t (oscTestFun m α) = G0 α (t - r) := O.hom α r t hr.1 hr.2 ht.2
    have hcl' : s53_clamp T (t - r) = t - r :=
      s53_clamp_of_mem ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    rw [s53_comm_eq, h1, hct]
    simp only [hcl', hGs ζ hζ]
  have hmeas : Measurable fun ζ => ct (ζ, r) := hctm.comp (measurable_id.prodMk measurable_const)
  have hL1 := s53_L1_bound ctx hNpos hδ H hCm0 hCm hrT (O.mem0 α _ hcl) (L := K * b α)
    (O.cb0 α _ hcl)
  have hint : Integrable (fun ζ => ct (ζ, r)) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    show ∫⁻ ζ, ‖ct (ζ, r)‖ₑ ∂P < ⊤
    refine lt_of_le_of_lt hL1 ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩,
      ENNReal.ofReal_lt_top⟩
  exact hint.congr (hGsae.mono fun ζ hζ => (hagree ζ hζ).symm)

/-- The S5.3 orbit input for the critical coefficient on the horizon `T`, for any `m ≥ 24d+240`. -/
theorem s82_orbit (hd : 2 ≤ d) (a β : ℝ) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ)
    (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ),
      S53Orbit (critCoeff d a β ρ) m T K b G0 G1 G2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hk : (d : ℝ) / 2 + 6 < ((d + 9 : ℕ) : ℝ) := by
    push_cast; linarith
  have hm' : ((2 * (d + 9) + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m := by
    have : (wholeSpaceIndex d : ℝ) = 24 * d + 240 := by
      unfold wholeSpaceIndex; push_cast; ring
    push_cast; linarith
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d ((d : ℝ) / 2) β⁻¹ ρ (fun _ => (0 : Euc d))
      (fun x => (fun _ : Euc d => (0 : Euc d)) x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρ.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρ T
  rw [s53_coeff_eq] at huniq
  obtain ⟨b, K, G0, G1, G2, Orb⟩ := s53_orbit_of_uniq hO
    (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) m hT huniq
    (s53_index_bound ((d : ℝ) / 2) hs0 hsd (d + 9) hk m hm')
  rw [← s53_coeff_eq] at Orb
  rw [HRS.MS.S85.s85_crit_eq]
  exact ⟨b, K, G0, G1, G2, Orb⟩

/-- Everything on one natural horizon `H`. -/
theorem s82_horizon (hd : 2 ≤ d) (a β : ℝ) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (H : ℝ) (hH : 0 ≤ H)
    {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) (CA : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hbm : IsVectorBrownian P W)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d ((d : ℝ) / 2) a β) H X₀ W X)
    (hstat0 : ∀ t ∈ Set.Icc (0 : ℝ) H, law P (X (Real.toNNReal t)) = law P (X 0))
    (hvar0 : ∀ f : Euc d → ℝ, MemCb 2 f →
        (N : ℝ≥0∞) * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d ((d : ℝ) / 2) (fun x => gradient f x)) (X 0 ζ)
            (HRS.Whole.withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d ((d : ℝ) / 2) N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2)) :
    (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) H,
      IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
    (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun ζ =>
        commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρ) X α t r ζ) P) ∧
      IntegrableOn (fun r => ∫ ζ, commForcing (critCoeff d a β ρ)
        ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P) (Set.Icc 0 t)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨b, K, G0, G1, G2, O⟩ := s82_orbit hd a β hβ m hm H hH hρ
  refine ⟨?_, fun α t ht => ⟨fun r hr => ?_, ?_⟩⟩
  · obtain ⟨CT, hCT⟩ := s53_field_remainder_centered_of_orbit hd hs0 hsd m H hH hρ
      (quadraticGradientDyn d ((d : ℝ) / 2) a β) (critCoeff d a β ρ) O CA
    exact (hCT N hN P X₀ W X hbm hX hstat0 hvar0).1
  · exact s82_forcing_integrable hd hs0 hsd m H hH hρ (quadraticGradientDyn d ((d : ℝ) / 2) a β)
      (critCoeff d a β ρ) O CA hN P X₀ W X hX hstat0 hvar0 α ht hr
  · exact (s21_fubini_comm hd hs0 hsd m H hH hρ (quadraticGradientDyn d ((d : ℝ) / 2) a β)
      (critCoeff d a β ρ) O CA hN P X₀ W X hX hstat0 hvar0 α ht).1

theorem s82_well_defined (d : ℕ) (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    (N : ℕ) (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) :
    (∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      ∃ f, IsClassicalAdjointW (critCoeff d a β ρ) t (oscTestFun m α) f) ∧
    (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
    (∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun ζ =>
        commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρ) X α t r ζ) P) ∧
      IntegrableOn (fun r => ∫ ζ, commForcing (critCoeff d a β ρ)
        ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P) (Set.Icc 0 t)) ∧
    (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun r => s82Centered d N a β m ρ P X α t r ζ) (Set.Icc 0 t)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm
    simp
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  obtain ⟨CA, hCA⟩ := HRS.MS.S21.s21_var_hyp hd hs0 hsd ha hβ
  have hlaw : ∀ t : ℝ≥0, law P (X t) =
      HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β :=
    fun t => hX.invariant P (t : ℝ) X₀ W X hX.brownian hX.indep hX.init (hX.solution t) t le_rfl
  have hS : ∀ H : ℕ,
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) (H : ℝ),
        IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
      (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) (H : ℝ),
        (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun ζ =>
          commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
            (HRS.Whole.withDensityReal ρ) X α t r ζ) P) ∧
        IntegrableOn (fun r => ∫ ζ, commForcing (critCoeff d a β ρ)
          ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P) (Set.Icc 0 t)) := by
    intro H
    exact s82_horizon hd a β hβ m hm (H : ℝ) (Nat.cast_nonneg H) hρS CA hN P X₀ W X
      hX.brownian (hX.solution (H : ℝ))
      (fun t _ => (hlaw _).trans (hlaw 0).symm)
      (fun f hf => hCA N hN P (X 0) ((hX.solution (H : ℝ)).adapted 0) (hlaw 0) ρ hρ f hf)
  have hcover : ∀ t : ℝ, 0 ≤ t → t ∈ Set.Icc (0 : ℝ) ((⌈t⌉₊ : ℕ) : ℝ) :=
    fun t ht => ⟨ht, Nat.le_ceil t⟩
  have h1 : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      ∃ f, IsClassicalAdjointW (critCoeff d a β ρ) t (oscTestFun m α) f := by
    intro α t ht
    rw [HRS.MS.S85.s85_crit_eq]
    exact (HRS.MS.S85.s85_exists_adjoint hd hs0 hsd hν _ hQ hρS t ht m α t ⟨ht, le_rfl⟩).1
  have hae : ∀ᵐ ζ ∂P, ∀ H : ℕ, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) (H : ℝ),
        IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t) :=
    ae_all_iff.2 fun H => (hS H).1
  have h2 : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t) :=
    hae.mono fun ζ hζ α t ht => hζ ⌈t⌉₊ α t (hcover t ht)
  have h3 : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun ζ =>
        commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρ) X α t r ζ) P) ∧
      IntegrableOn (fun r => ∫ ζ, commForcing (critCoeff d a β ρ)
        ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P) (Set.Icc 0 t) :=
    fun α t ht => (hS ⌈t⌉₊).2 α t (hcover t ht)
  refine ⟨h1, h2, h3, ?_⟩
  filter_upwards [h2] with ζ hζ α t ht
  have h4 : IntegrableOn (fun r => commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ -
      ∫ ζ', commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P) (Set.Icc 0 t) :=
    Integrable.sub (hζ α t ht) (h3 α t ht).2
  exact Integrable.const_mul h4 (Real.sqrt N / 2)

end HRS.MS.S82BD
