import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldAux
import HRS.PDE.WellPosed

/-!
# The equilibrium semigroup generator for `2 ≤ d` (package MF-01, packet P9)

Proof of `equilibriumSemigroup_generator` for `2 ≤ d` (`equilibriumSemigroup_generator_of_two`), from
Proposition 3.9(a) (`adjoint_torus_classical`) for the frozen coefficient `μ ≡ ρβ`, the uniqueness
of classical adjoint solutions (time-homogeneity), and `MFAux.operator_order_core`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFSemigroup

variable {d : ℕ}

/-! ### Centering -/

theorem isProb_withDensityReal {ρ : Torus d → ℝ} (h : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ := by
    by_contra hn
    have := h.integral_one
    rw [integral_undef hn] at this
    norm_num at this
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall h.nonneg),
    h.integral_one]
  simp

theorem pair_projMean (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (f : Torus d → ℝ) :
    pair μ (projMean μ f) = 0 := by
  by_cases hf : Integrable f μ
  · unfold pair projMean
    rw [integral_sub hf (integrable_const _)]
    simp [pair]
  · have h0 : pair μ f = 0 := integral_undef hf
    unfold projMean
    rw [h0]
    simp only [sub_zero]
    exact h0

theorem grad_projMean (μ : Measure (Torus d)) (f : Torus d → ℝ) :
    Torus.grad (projMean μ f) = Torus.grad f := by
  funext x
  unfold Torus.grad projMean
  have : Torus.lift (fun x => f x - pair μ f) = fun y => Torus.lift f y - pair μ f := rfl
  rw [this]
  unfold gradient
  rw [fderiv_sub_const]

theorem lop_projMean (μ : Measure (Torus d)) (ρ f : Torus d → ℝ) :
    Lop ρ (projMean μ f) = Lop ρ f := by
  unfold Lop
  rw [grad_projMean]

/-! ### Time-homogeneity for the frozen coefficient -/

/-- Time shift of a classical adjoint solution for a time-independent coefficient. -/
theorem shift_classical (D : DynData d) (ρ : Torus d → ℝ) {T' τ : ℝ} (hτT : τ ≤ T')
    {ψ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) :
    IsClassicalAdjointSolution D (fun _ => ρ) τ ψ (fun r => F (r + (T' - τ))) := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) τ, r + (T' - τ) ∈ Set.Icc (0 : ℝ) T' := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let φ : Set.Icc (0 : ℝ) τ → Set.Icc (0 : ℝ) T' := fun r => ⟨r.1 + (T' - τ), hmem r.1 r.2⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.add continuous_const
  refine ⟨fun r hr => hF.c2 _ (hmem r hr), fun j hj => ?_, ?_, ?_, ?_⟩
  · exact (hF.cont_c2 j hj).comp (hφ.prodMap continuous_id)
  · have := hF.terminal
    simpa using this
  · intro x r hr
    have h1 : r + (T' - τ) ∈ Set.Ioo 0 T' := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (hF.time_deriv x _ h1).comp_add_const r (T' - τ)
  · refine (hF.cont_time_deriv.comp (hφ.prodMap continuous_id)).congr ?_
    intro p
    rfl

/-- `classical_adjoint_unique` for `2 ≤ d`, avoiding the `d = 1` kernel black box
(`ClassicalAux.convKernelFacts_one`): the same proof with the kernel facts of `Convention.lean`. -/
theorem classical_adjoint_unique_of_two (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φ : Torus d → ℝ)
    (f₁ f₂ : ℝ → Torus d → ℝ) (h₁ : IsClassicalAdjointSolution D μ t φ f₁)
    (h₂ : IsClassicalAdjointSolution D μ t φ f₂) : ∀ r ∈ Set.Icc 0 t, f₁ r = f₂ r := by
  intro r hr
  have hμ1 : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 1 (μ r) := fun r hr =>
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
      (hA.hμ.smooth r ⟨hr.1, hr.2.trans ht.2⟩)
  have hV1 : Torus.IsCk 1 D.V :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
  have hK : ClassicalAux.ConvKernelFacts d D.s :=
    ClassicalAux.convKernelFacts_of_two_le hd D.hs0 D.hsd
  obtain ⟨hs₁, -⟩ := ClassicalAux.classicalToCoeff_aux D hK hV1 μ t hμ1 φ f₁ h₁
  obtain ⟨hs₂, -⟩ := ClassicalAux.classicalToCoeff_aux D hK hV1 μ t hμ1 φ f₂ h₂
  have w₁ := weakContinuousInHs_mono (by norm_num : (1 : ℝ) ≤ 2)
    (ClassicalAux.weakContinuousInHs_two h₁)
  have w₂ := weakContinuousInHs_mono (by norm_num : (1 : ℝ) ≤ 2)
    (ClassicalAux.weakContinuousInHs_two h₂)
  have hu := forward_unique_H1 (by omega) s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht (coeffOf φ) _ _
    hs₁ w₁ hs₂ w₂ (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simp only [sub_sub_cancel] at hu
  exact ClassicalAux.eq_of_coeffOf_eq (ClassicalAux.continuous_f_apply h₁ hr)
    (ClassicalAux.continuous_f_apply h₂ hr) hu

/-- Time-homogeneity: for the frozen coefficient, the propagator on `[0,τ]` is the time-shifted
classical solution with terminal time `T' ≥ τ`: `U^{0,τ}ψ = F(T' - τ)`. -/
theorem propagator_frozen_eq (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {T' : ℝ} (hT' : T' ∈ Set.Ioc 0 T)
    {ψ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T') :
    propagator D (fun _ => ρ) 0 τ ψ = F (T' - τ) := by
  have hG := shift_classical D ρ hτ.2 hF
  have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρ) τ ψ f := ⟨_, hG⟩
  have hu := classical_adjoint_unique_of_two hd s hs0 hsd m hm R MB Λ VB D ν₀ T (fun _ => ρ) hA τ
    ⟨hτ.1, hτ.2.trans hT'.2⟩ ψ _ _ hex.choose_spec hG 0 ⟨le_rfl, hτ.1.le⟩
  simp only [propagator, hex, dite_true]
  rw [hu]
  simp

/-! ### The case `τ = 0` -/

theorem continuous_backwardGenerator (D : DynData d) (hK : ClassicalAux.ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) {ρ u : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hu : Torus.IsCk 2 u) :
    Continuous (backwardGenerator D ρ u) := by
  rw [ClassicalAux.backwardGenerator_eq_fun]
  have hu1 : Torus.IsCk 1 u := ClassicalAux.isCk_of_le (by norm_num) hu
  refine Continuous.sub (Continuous.add (continuous_const.mul (ClassicalAux.continuous_laplacian hu))
    (continuous_finsetSum _ fun j _ => ?_)) (continuous_finsetSum _ fun j _ => ?_)
  · exact (ClassicalAux.continuous_bfun hK hV hρ j).mul (continuous_partialDeriv j u hu1)
  · exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      (hK.cont _ (ClassicalAux.isCk_wfun D hρ hu j)))

/-- The constant path is a classical adjoint solution at terminal time `0`. -/
theorem isClassical_zero (D : DynData d) (hK : ClassicalAux.ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) (μ : ℝ → Torus d → ℝ) (hμ : Torus.IsCk 1 (μ 0)) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) : IsClassicalAdjointSolution D μ 0 ψ (fun _ => ψ) := by
  refine ⟨fun r hr => hψ, fun j hj => ?_, rfl, ?_, ?_⟩
  · have : Continuous fun y : Euc d => iteratedFDeriv ℝ j (Torus.lift ψ) y :=
      hψ.continuous_iteratedFDeriv (by exact_mod_cast hj)
    exact this.comp continuous_snd
  · intro x r hr
    exfalso
    simp at hr
  · have hc : Continuous (backwardGenerator D (μ 0) ψ) :=
      continuous_backwardGenerator D hK hV hμ hψ
    have h0 : ∀ p : Set.Icc (0 : ℝ) 0 × Torus d, p.1.1 = 0 := fun p => by
      have := p.1.2
      exact le_antisymm this.2 this.1
    refine (hc.comp continuous_snd).congr fun p => ?_
    simp only [Function.comp_apply, h0 p]

theorem propagator_zero (D : DynData d) (hK : ClassicalAux.ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) (μ : ℝ → Torus d → ℝ) (hμ : Torus.IsCk 1 (μ 0)) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) : propagator D μ 0 0 ψ = ψ := by
  have hex : ∃ f, IsClassicalAdjointSolution D μ 0 ψ f := ⟨_, isClassical_zero D hK hV μ hμ hψ⟩
  simp only [propagator, hex, dite_true]
  exact hex.choose_spec.terminal

/-! ### Smooth functions lie in every `H^m` -/

theorem isCk_nat_of_isSmooth {b : Torus d → ℝ} (hb : Torus.IsSmooth b) (n : ℕ) :
    Torus.IsCk (n : ℕ) b :=
  ClassicalAux.isCk_of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) hb

theorem memHs_nat_of_isCk : ∀ (n : ℕ) (b : Torus d → ℝ), Torus.IsCk (n : ℕ) b →
    MemHs (n : ℝ) (coeffOf b)
  | 0, b, hb => by
    simpa using (coeffOf_memHs_zero (ClassicalAux.continuous_of_lift_aux hb.continuous)).1
  | n + 1, b, hb => by
    have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have h0 : MemHs (n : ℝ) (coeffOf b) :=
      memHs_nat_of_isCk n b (hb.of_le (by exact_mod_cast Nat.le_succ n))
    have hj : ∀ j, MemHs (n : ℝ) (coeffOf (Torus.partialDeriv j b)) := fun j =>
      memHs_nat_of_isCk n _ (ProdAux.isCk_partialDeriv hb j)
    have key : ∀ k, sobWeight ((n + 1 : ℕ) : ℝ) k * ‖coeffOf b k‖ ^ 2 =
        sobWeight (n : ℝ) k * ‖coeffOf b k‖ ^ 2 +
          ∑ j, sobWeight (n : ℝ) k * ‖coeffOf (Torus.partialDeriv j b) k‖ ^ 2 := by
      intro k
      have e : ∀ j, ‖coeffOf (Torus.partialDeriv j b) k‖ ^ 2 =
          (2 * Real.pi * ((k j : ℤ) : ℝ)) ^ 2 * ‖coeffOf b k‖ ^ 2 := by
        intro j
        rw [coeffOf_partialDeriv j b hb1, norm_derivCoeff, mul_pow, mul_pow, sq_abs]
        ring
      simp only [e]
      push_cast
      rw [sobWeight_add, sobWeight_one_eq_sum]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    exact (h0.add (summable_sum (s := Finset.univ) fun j _ => hj j)).congr fun k => (key k).symm

theorem memHs_of_isSmooth {b : Torus d → ℝ} (hb : Torus.IsSmooth b) (m : ℝ) :
    MemHs m (coeffOf b) := by
  have := memHs_nat_of_isCk ⌈m⌉₊ b (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hb)
  exact this.mono (Nat.le_ceil m)

theorem memSobolev_of_isSmooth {b : Torus d → ℝ} (hb : Torus.IsSmooth b) (m : ℝ) :
    MemSobolev m b :=
  memSobolev_of_memHs m b (ClassicalAux.memLp_two_of_continuous
    (ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hb))) (memHs_of_isSmooth hb m)

/-! ### The frozen coefficient satisfies the hypotheses of Proposition 3.9 -/

theorem adjointData_frozen (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (m : ℕ) :
    ∃ (R : Regime) (MB Λ VB : ℝ), ∀ (ν₀ T : ℝ), 0 < T →
      AdjointData s m R MB Λ VB (mfData d s hs0 hsd V β hβ) ν₀ T (fun _ => ρβ) := by
  have hρ3 : Torus.IsCk (m + 3 : ℕ) ρβ := isCk_nat_of_isSmooth hρC _
  have hV3 : Torus.IsCk (m + 3 : ℕ) V := isCk_nat_of_isSmooth hV _
  have hcont : Continuous ρβ :=
    ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hρC 1)
  have hM : MatBound 1 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro i j
    by_cases h : i = j <;> simp [h]
  have hsym : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    unfold Torus.SymNonpos Torus.symPart
    simp only [Matrix.transpose_neg, Matrix.transpose_one]
    have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + -1))) = 1 := by
      rw [← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
      norm_num
    rw [this]
    exact Matrix.PosSemidef.one
  have common : ∀ (R : Regime) (ν₀ T : ℝ), 0 < T →
      R.Holds d s (-1 : Matrix (Fin d) (Fin d) ℝ) β⁻¹ ν₀ T (fun _ => ρβ) →
      AdjointData s m R 1 (Torus.cbNorm (m + 3 : ℕ) ρβ) (Torus.cbNorm (m + 3 : ℕ) V)
        (mfData d s hs0 hsd V β hβ) ν₀ T (fun _ => ρβ) := fun R ν₀ T hT hR =>
    ⟨rfl, hM, ⟨hV3, le_rfl⟩, ⟨fun r _ => hprob, fun r _ => hρ3, fun r _ => le_rfl,
      fun ψ _ => continuousOn_const⟩, hT, hR⟩
  by_cases hs : s ≤ (d : ℝ) - 2
  · exact ⟨.R1, 1, _, _, fun ν₀ T hT => common _ ν₀ T hT hs⟩
  · obtain ⟨x0, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
      hcont.continuousOn
    refine ⟨.R2b (ρβ x0), 1, _, _, fun ν₀ T hT => common _ ν₀ T hT ⟨by linarith, hsym, hpos x0,
      fun r _ x => hmin (Set.mem_univ x)⟩⟩

/-! ### Differentiating the centered solution in the terminal time -/

/-- The endpoint derivative: a function continuous on `[0,T']`, differentiable on `(0,T')` with a
derivative that extends continuously to `0`, has this derivative from the right at `0`
(mean value theorem). -/
theorem hasDerivWithinAt_Ici_zero {G Gd : ℝ → ℝ} {T' : ℝ} (hT : 0 < T')
    (hd : ∀ σ ∈ Set.Ioo 0 T', HasDerivAt G (Gd σ) σ)
    (hG : ContinuousOn G (Set.Icc 0 T')) (hGd : ContinuousOn Gd (Set.Icc 0 T')) :
    HasDerivWithinAt G (Gd 0) (Set.Ici 0) 0 := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 T')
    (fun σ hσ => (hd σ hσ).differentiableAt.differentiableWithinAt)
    ((hG 0 (Set.left_mem_Icc.2 hT.le)).mono Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hT) ?_
  have h1 : ContinuousWithinAt Gd (Set.Ioi 0) 0 :=
    (hGd 0 (Set.left_mem_Icc.2 hT.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hT)
  refine h1.tendsto.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hT] with σ hσ
  exact (hd σ hσ).deriv.symm

theorem pair_withDensityReal {ρ : Torus d → ℝ} (h : IsProbDensity ρ) (f : Torus d → ℝ) :
    pair (withDensityReal ρ) f = ∫ y, ρ y * f y :=
  integral_withDensityReal_eq ρ h.measurable h.nonneg f

section Core

variable {D : DynData d} {ρ : Torus d → ℝ} {T' : ℝ} {ψ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}

theorem continuous_F (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) :
    Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d => F p.1 p.2 := by
  refine ClassicalAux.continuous_prod_of_lift (X := Set.Icc (0 : ℝ) T') (fun r x => F r x) ?_
  have h0 := ClassicalAux.continuous_iteratedFDeriv_eval
    (G := fun r : Set.Icc (0 : ℝ) T' => Torus.lift (F r)) 0 (hF.cont_c2 0 (by norm_num)) ![]
  simp only [iteratedFDeriv_zero_apply] at h0
  exact h0

theorem continuousOn_F_apply (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) (x : Torus d) :
    ContinuousOn (fun r => F r x) (Set.Icc (0 : ℝ) T') :=
  continuousOn_iff_continuous_domRestrict.2 ((continuous_F hF).comp (continuous_id.prodMk continuous_const))

theorem continuousOn_bg_apply (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) (x : Torus d) :
    ContinuousOn (fun r => backwardGenerator D ρ (F r) x) (Set.Icc (0 : ℝ) T') :=
  continuousOn_iff_continuous_domRestrict.2 <| by
    have h : Continuous fun r : Set.Icc (0 : ℝ) T' => backwardGenerator D ρ (F r.1) x :=
      (hF.cont_time_deriv.comp (continuous_id.prodMk (continuous_const (y := x))) :)
    exact h

theorem continuousOn_pair_F (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) :
    ContinuousOn (fun r => pair (withDensityReal ρ) (F r)) (Set.Icc (0 : ℝ) T') := by
  simp only [pair_withDensityReal hρ]
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (r : Set.Icc (0 : ℝ) T') (y : Torus d) => ρ y * F r y)
    (hρc.comp continuous_snd |>.mul (continuous_F hF)) isCompact_univ
  simp only [MeasureTheory.Measure.restrict_univ] at this
  exact this

theorem continuousOn_pair_bg (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) :
    ContinuousOn (fun r => pair (withDensityReal ρ) (backwardGenerator D ρ (F r)))
      (Set.Icc (0 : ℝ) T') := by
  simp only [pair_withDensityReal hρ]
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (r : Set.Icc (0 : ℝ) T') (y : Torus d) => ρ y * backwardGenerator D ρ (F r) y)
    (hρc.comp continuous_snd |>.mul hF.cont_time_deriv) isCompact_univ
  simp only [MeasureTheory.Measure.restrict_univ] at this
  exact this

theorem hasDerivAt_F (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) (x : Torus d) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 T') :
    HasDerivAt (fun σ' => F (T' - σ') x) (backwardGenerator D ρ (F (T' - σ)) x) σ := by
  have h := hF.time_deriv x (T' - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  exact (h.comp σ ((hasDerivAt_id σ).const_sub T')).congr_deriv (by simp)

theorem hasDerivAt_pair_F (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 T') :
    HasDerivAt (fun σ' => pair (withDensityReal ρ) (F (T' - σ')))
      (pair (withDensityReal ρ) (backwardGenerator D ρ (F (T' - σ)))) σ := by
  simp only [pair_withDensityReal hρ]
  obtain ⟨B, hB0, hB⟩ := ClassicalAux.exists_bound_bg hF
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR (Classical.arbitrary (Torus d)) (Set.mem_univ _))
  have hε : 0 < min σ (T' - σ) := lt_min hσ.1 (by linarith [hσ.2])
  have hball : ∀ σ' ∈ Metric.ball σ (min σ (T' - σ)), σ' ∈ Set.Ioo (0 : ℝ) T' := by
    intro σ' h
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h
    have h1 := min_le_left σ (T' - σ)
    have h2 := min_le_right σ (T' - σ)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmem : ∀ σ' ∈ Set.Ioo (0 : ℝ) T', T' - σ' ∈ Set.Icc (0 : ℝ) T' := fun σ' h =>
    ⟨by linarith [h.2], by linarith [h.1]⟩
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (F := fun σ' y => ρ y * F (T' - σ') y)
    (F' := fun σ' y => ρ y * backwardGenerator D ρ (F (T' - σ')) y) (x₀ := σ)
    (bound := fun _ => R * B) (Metric.ball_mem_nhds σ hε) ?_ ?_ ?_ ?_ (integrable_const _) ?_
  · exact this.2
  · filter_upwards [Metric.ball_mem_nhds σ hε] with σ' h
    exact (hρc.mul (ClassicalAux.continuous_f_apply hF (hmem σ' (hball σ' h)))).aestronglyMeasurable
  · exact (hρc.mul (ClassicalAux.continuous_f_apply hF (hmem σ (hball σ (Metric.mem_ball_self hε))))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hρc.mul (ClassicalAux.continuous_bg_apply hF (hmem σ hσ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y σ' h => ?_
    rw [norm_mul]
    exact mul_le_mul (hR y (Set.mem_univ _)) (by
      have := hB (T' - σ') (hmem σ' (hball σ' h)) y
      rwa [Real.norm_eq_abs]) (norm_nonneg _) hR0
  · exact Filter.Eventually.of_forall fun y σ' h => (hasDerivAt_F hF y (hball σ' h)).const_mul (ρ y)

end Core

/-! ### Existence of the classical solution (Proposition 3.9(a)) for the frozen coefficient -/

theorem frozen_classical (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (T' : ℝ) (hT' : 0 < T') :
    ∃ (R : Regime) (MB Λ VB : ℝ),
      AdjointData s (mStar d) R MB Λ VB (mfData d s hs0 hsd V β hβ) 0 T' (fun _ => ρβ) ∧
      ∃ F : ℝ → Torus d → ℝ,
        IsClassicalAdjointSolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) T' ψ F := by
  obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρC hpos (mStar d)
  refine ⟨R, MB, Λ, VB, hA 0 T' hT', ?_⟩
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical (by omega) s hs0 hsd (mStar d) le_rfl R MB Λ VB
  have hψc : Continuous ψ :=
    ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hψ 1)
  obtain ⟨h1, -⟩ := hmain _ 0 T' (fun _ => ρβ) (hA 0 T' hT') T' ⟨hT', le_rfl⟩ ψ hψc
    (memSobolev_of_isSmooth hψ _)
  exact ⟨_, h1⟩

/-! ### The main theorem -/

/-- `equilibriumSemigroup_generator` (`HRS/PDE/MeanField.lean`) for `2 ≤ d`. -/
theorem equilibriumSemigroup_generator_of_two (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ) :
    equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 ψ = projMean (withDensityReal ρβ) ψ ∧
    (∀ τ, 0 ≤ τ → pair (withDensityReal ρβ)
      (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ ψ) = 0) ∧
    ∀ x, ∀ τ, 0 ≤ τ →
      HasDerivWithinAt (fun τ' => equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ' ψ x)
        (equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ τ ψ) x)
        (Set.Ici 0) τ := by
  set D := mfData d s hs0 hsd V β hβ with hD
  have hprob : IsProbDensity ρβ := hρβ.1
  have := isProb_withDensityReal hprob
  have hK : ClassicalAux.ConvKernelFacts d D.s :=
    ClassicalAux.convKernelFacts_of_two_le hd hs0 hsd
  have hV1 : Torus.IsCk 1 D.V := isCk_nat_of_isSmooth hV 1
  have hV2 : Torus.IsCk 2 D.V := isCk_nat_of_isSmooth hV 2
  have hρ1 : Torus.IsCk 1 ρβ := isCk_nat_of_isSmooth hρC 1
  have hρ2 : Torus.IsCk 2 ρβ := isCk_nat_of_isSmooth hρC 2
  have hψ2 : Torus.IsCk 2 ψ := isCk_nat_of_isSmooth hψ 2
  have hρc : Continuous ρβ := ClassicalAux.continuous_of_isCk hρ1
  have h0 : propagator D (fun _ => ρβ) 0 0 ψ = ψ := propagator_zero D hK hV1 _ hρ1 hψ2
  refine ⟨?_, fun τ _ => pair_projMean _ _, ?_⟩
  · unfold equilibriumSemigroup
    rw [h0]
  intro x τ0 hτ0
  obtain ⟨R, MB, Λ, VB, hA, F, hF⟩ := frozen_classical hd s hs0 hsd β hβ V hV ρβ hprob hρC hpos ψ hψ
    (τ0 + 1) (by linarith)
  set T' := τ0 + 1 with hT'
  have hT0 : 0 < T' := by linarith
  have hlt : τ0 < T' := by linarith
  have hmem : ∀ σ ∈ Set.Icc 0 T', T' - σ ∈ Set.Icc 0 T' := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hprop : ∀ σ ∈ Set.Icc 0 T', propagator D (fun _ => ρβ) 0 σ ψ = F (T' - σ) := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h, h0, sub_zero]
      exact hF.terminal.symm
    · exact propagator_frozen_eq hd s hs0 hsd (mStar d) (by unfold mStar; omega) R MB Λ VB D 0 T'
        ρβ hA ⟨hT0, le_rfl⟩ hF ⟨h, hσ.2⟩
  let G : ℝ → ℝ := fun σ => F (T' - σ) x - pair (withDensityReal ρβ) (F (T' - σ))
  let Gd : ℝ → ℝ := fun σ => backwardGenerator D ρβ (F (T' - σ)) x -
    pair (withDensityReal ρβ) (backwardGenerator D ρβ (F (T' - σ)))
  have hsub : ContinuousOn (fun σ : ℝ => T' - σ) (Set.Icc 0 T') :=
    continuousOn_const.sub continuousOn_id
  have hGcont : ContinuousOn G (Set.Icc 0 T') :=
    ((continuousOn_F_apply hF x).comp hsub hmem).sub
      ((continuousOn_pair_F hprob hρc hF).comp hsub hmem)
  have hGdcont : ContinuousOn Gd (Set.Icc 0 T') :=
    ((continuousOn_bg_apply hF x).comp hsub hmem).sub
      ((continuousOn_pair_bg hprob hρc hF).comp hsub hmem)
  have hder : HasDerivWithinAt G (Gd τ0) (Set.Ici 0) τ0 := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]
      exact hasDerivWithinAt_Ici_zero hT0
        (fun σ hσ => (hasDerivAt_F hF x hσ).sub (hasDerivAt_pair_F hprob hρc hF hσ))
        hGcont hGdcont
    · exact ((hasDerivAt_F hF x ⟨h, hlt⟩).sub
        (hasDerivAt_pair_F hprob hρc hF ⟨h, hlt⟩)).hasDerivWithinAt
  have hS : ∀ σ ∈ Set.Icc 0 T', equilibriumSemigroup D ρβ σ ψ x = G σ := by
    intro σ hσ
    simp only [equilibriumSemigroup, projMean, hprop σ hσ, G]
  have hmem0 : τ0 ∈ Set.Icc 0 T' := ⟨hτ0, hlt.le⟩
  have hval : equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup D ρβ τ0 ψ) x = Gd τ0 := by
    have hf2 : Torus.IsCk 2 (F (T' - τ0)) := hF.c2 _ (hmem τ0 hmem0)
    have hS0 : equilibriumSemigroup D ρβ τ0 ψ = projMean (withDensityReal ρβ) (F (T' - τ0)) := by
      unfold equilibriumSemigroup
      rw [hprop τ0 hmem0]
    have hord := congrFun (MFAux.operator_order_core hd D rfl β hβ rfl hV2 ρβ hρβ hρ2 hpos
      (F (T' - τ0)) hf2) x
    rw [hS0]
    unfold equilibriumGen
    rw [lop_projMean]
    exact hord.symm
  have hev : (fun τ' => equilibriumSemigroup D ρβ τ' ψ x) =ᶠ[𝓝[Set.Ici 0] τ0] G := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds hlt)] with σ hσ
    exact hS σ ⟨hσ.1, hσ.2.le⟩
  exact (hder.congr_of_eventuallyEq hev (hS τ0 hmem0)).congr_deriv hval.symm

end HRS.PDE.MFSemigroup
