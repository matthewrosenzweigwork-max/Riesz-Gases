import HRS.PDE.MeanFieldThermal
import HRS.PDE.MeanFieldAux
import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.KernelInputsD1

/-!
# `C:eq:operator-order` and the equilibrium semigroup generator for every `d ≥ 1` (package MF-01, D1W)

Copies of `MFAux.operator_order_core` and `MFSemigroup.equilibriumSemigroup_generator_of_two`
with `1 ≤ d`: the kernel inputs come from `HRS/PDE/KernelInputsD1.lean` and
`MFThermalAssembly.kernelFacts`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFOneLe

variable {d : ℕ}

theorem integrable_periodicRiesz (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) :=
  (MFThermalAssembly.kernelFacts hd s hs0 hsd).integrable


theorem coeffOf_convFun (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hh : Continuous h) (k : Lattice d) :
    coeffOf (convFun (periodicRiesz d s) h) k = (rieszCoeff d s k : ℂ) * coeffOf h k := by
  unfold coeffOf
  rw [MFAux.funFourierCoeff_convFun (integrable_periodicRiesz hd s hs0 hsd) hh k,
    (MFThermalAssembly.kernelFacts hd s hs0 hsd).fourierCoeff k]


/-- `∇g * ρ = ∇(g * ρ)` (cancellation convention), for `C¹` `ρ` with `g * ρ ∈ C¹`. -/
theorem convGradConv_eq_partialDeriv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hφ : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ))
    (j : Fin d) (x : Torus d) :
    (convGradConv (periodicRieszGrad d s) ρ x) j =
      Torus.partialDeriv j (convFun (periodicRiesz d s) ρ) x := by
  have hρc := MFAux.continuous_of_isCk hρ
  have hu : Continuous fun x => (convGradConv (periodicRieszGrad d s) ρ x) j :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
      (convGradConv_continuous_of_one_le hd hs0 hsd ρ hρ)
  have hv : Continuous (Torus.partialDeriv j (convFun (periodicRiesz d s) ρ)) :=
    continuous_partialDeriv j _ hφ
  have := MFAux.eq_of_funFourierCoeff_eq hu hv (fun k => by
    have h1 := congrFun (convGradConv_coeff_of_one_le hd hs0 hsd ρ hρ j) k
    have h2 := congrFun (coeffOf_partialDeriv j _ hφ) k
    have h3 := coeffOf_convFun hd s hs0 hsd hρc k
    unfold coeffOf at h1 h2 h3
    rw [h1, h2]
    simp only [derivCoeff, gradRieszCoeff, rieszMult] at *
    rw [h3])
  exact congrFun this x

/-- `∑_j ∂_j g * H_j = g * ∑_j ∂_j H_j` (cancellation convention). -/
theorem sum_convGradConv_eq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : Fin d → Torus d → ℝ) (hH : ∀ j, Torus.IsCk 1 (H j)) (x : Torus d) :
    ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j =
      convFun (periodicRiesz d s) (fun y => ∑ j, Torus.partialDeriv j (H j) y) x := by
  have hDc : Continuous fun y => ∑ j, Torus.partialDeriv j (H j) y :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  have hu : Continuous fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j :=
    continuous_finsetSum _ fun j _ => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
      (convGradConv_continuous_of_one_le hd hs0 hsd (H j) (hH j))
  have hv : Continuous (convFun (periodicRiesz d s) fun y => ∑ j, Torus.partialDeriv j (H j) y) :=
    MFAux.continuous_convFun (integrable_periodicRiesz hd s hs0 hsd) hDc
  have := MFAux.eq_of_funFourierCoeff_eq hu hv (fun k => by
    have e1 : coeffOf (fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j) k =
        ∑ j, coeffOf (fun x => (convGradConv (periodicRieszGrad d s) (H j) x) j) k :=
      MFAux.coeffOf_sum Finset.univ _ (fun j => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
        (convGradConv_continuous_of_one_le hd hs0 hsd (H j) (hH j))) k
    have e2 := coeffOf_convFun hd s hs0 hsd hDc k
    have e3 : coeffOf (fun y => ∑ j, Torus.partialDeriv j (H j) y) k =
        ∑ j, coeffOf (Torus.partialDeriv j (H j)) k :=
      MFAux.coeffOf_sum Finset.univ _ (fun j => continuous_partialDeriv j _ (hH j)) k
    show coeffOf (fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j) k =
      coeffOf (convFun (periodicRiesz d s) fun y => ∑ j, Torus.partialDeriv j (H j) y) k
    rw [e1, e2, e3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [convGradConv_coeff_of_one_le hd hs0 hsd (H j) (hH j) j, coeffOf_partialDeriv j _ (hH j)]
    simp only [gradRieszCoeff, derivCoeff, rieszMult]
    ring)
  exact congrFun this x


/-- Pointwise generator formula: `𝓛f = -ν L f + g * Div(ρ∇f)` for the gradient-flow generator
(`M = -I`), via the Gibbs relation. -/
theorem generator_eq (hd : 1 ≤ d) (D : DynData d) (hM : D.M = -1) (β : ℝ) (hβ : 0 < β)
    (hinv : D.invβ = β⁻¹) (hV : Torus.IsCk 2 D.V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d D.s) D.V β ρ) (hρC : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) (x : Torus d) :
    backwardGenerator D ρ f x = -(D.invβ * Lop ρ f x) +
      convFun (periodicRiesz d D.s) (fun y => ∑ j, Torus.partialDeriv j
        (fun y' => ρ y' * Torus.partialDeriv j f y') y) x := by
  have hρ1 : Torus.IsCk 1 ρ := hρC.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 D.V := hV.of_le (by norm_num)
  obtain ⟨hgibbs, hdiff⟩ := MFAux.gibbs_partialDeriv D.V ρ (convFun (periodicRiesz d D.s) ρ) β hβ.ne'
    (∫ y, Real.exp (-β * (D.V y + convFun (periodicRiesz d D.s) ρ y))) hρ1 hV1 hpos hρβ.2
  have hc : ∀ j, (convGradConv (periodicRieszGrad d D.s) ρ x) j + Torus.partialDeriv j D.V x =
      -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) := by
    intro j
    rw [convGradConv_eq_partialDeriv hd D.s D.hs0 D.hsd hρ1 hgibbs j x, hdiff j x]
    ring
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j
  rw [MFAux.backwardGenerator_negOne D hM ρ f x, sum_convGradConv_eq hd D.s D.hs0 D.hsd _ hH x]
  simp_rw [hc]
  have hDh : ∑ j, Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') x =
      ∑ j, (Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
        ρ x * Torus.partialDeriv j (Torus.partialDeriv j f) x) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact MFAux.partialDeriv_mul j ρ _ hρ1 (isCk_one_partialDeriv j f hf) x
  have hLop : Lop ρ f x = -(ρ x)⁻¹ * ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') x := by
    unfold Lop
    rw [MFAux.div_smul_grad ρ f hρ1 hf x]
  rw [hLop, hDh, laplacian_eq_sum f hf x, hinv]
  have hρx := (hpos x).ne'
  have e1 : ∑ j, (-β⁻¹ * (Torus.partialDeriv j ρ x / ρ x)) * Torus.partialDeriv j f x =
      -β⁻¹ * (ρ x)⁻¹ * ∑ j, Torus.partialDeriv j ρ x * Torus.partialDeriv j f x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have e2 : ∑ j, (Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
      ρ x * Torus.partialDeriv j (Torus.partialDeriv j f) x) =
      ∑ j, Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
        ρ x * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) x := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e1, e2]
  field_simp
  ring

/-- `Q_β 𝓛_β f = -(ν L_β f + K_β L_β f)` for the gradient-flow generator (`M = -I`). -/
theorem operator_order_core_of_one_le (hd : 1 ≤ d) (D : DynData d) (hM : D.M = -1) (β : ℝ) (hβ : 0 < β)
    (hinv : D.invβ = β⁻¹) (hV : Torus.IsCk 2 D.V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d D.s) D.V β ρ) (hρC : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) :
    projMean (withDensityReal ρ) (backwardGenerator D ρ f) =
      fun x => -(D.invβ * Lop ρ f x +
        Kop (periodicRiesz d D.s) (withDensityReal ρ) (Lop ρ f) x) := by
  have hρ1 : Torus.IsCk 1 ρ := hρC.of_le (by norm_num)
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j
  set Dh : Torus d → ℝ := fun y => ∑ j, Torus.partialDeriv j
    (fun y' => ρ y' * Torus.partialDeriv j f y') y with hDh
  have hDc : Continuous Dh :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  set g := periodicRiesz d D.s with hg
  set E : Torus d → ℝ := convFun g Dh with hE
  have hEc : Continuous E := MFAux.continuous_convFun (integrable_periodicRiesz hd D.s D.hs0 D.hsd) hDc
  have hgen : ∀ x, backwardGenerator D ρ f x = -(D.invβ * Lop ρ f x) + E x :=
    fun x => generator_eq hd D hM β hβ hinv hV ρ hρβ hρC hpos f hf x
  have hLop : ∀ x, ρ x * Lop ρ f x = - Dh x := by
    intro x
    have : Lop ρ f x = -(ρ x)⁻¹ * Dh x := by
      unfold Lop
      rw [MFAux.div_smul_grad ρ f hρ1 hf x]
    rw [this]
    have := (hpos x).ne'
    field_simp
  have hLopc : Continuous (Lop ρ f) := by
    have : Lop ρ f = fun x => -(ρ x)⁻¹ * Dh x := by
      funext x
      unfold Lop
      rw [MFAux.div_smul_grad ρ f hρ1 hf x]
    rw [this]
    exact ((hρc.inv₀ fun x => (hpos x).ne').neg).mul hDc
  have hint0 : ∫ x, Dh x = 0 := by
    rw [hDh]
    show ∫ x, ∑ j, Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') x = 0
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero fun j _ => MFAux.integral_partialDeriv_eq_zero j _ (hH j)
    · intro j _
      exact (continuous_partialDeriv j _ (hH j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hKinner : ∀ x, ∫ y, g (x - y) * Lop ρ f y ∂(withDensityReal ρ) = -E x := by
    intro x
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    have : ∀ y, ρ y * (g (x - y) * Lop ρ f y) = -(g (x - y) * Dh y) := by
      intro y
      have := hLop y
      linear_combination g (x - y) * this
    simp_rw [this]
    rw [integral_neg]
    rfl
  have hpairE : pair (withDensityReal ρ) E = ∫ x, ρ x * E x := by
    unfold pair
    exact integral_withDensityReal_eq ρ hρm hρ0 E
  have hKop : ∀ x, Kop g (withDensityReal ρ) (Lop ρ f) x = -E x + ∫ x, ρ x * E x := by
    intro x
    unfold Kop projMean
    simp_rw [hKinner]
    unfold pair
    rw [integral_neg, ← hpairE]
    unfold pair
    ring
  have hpairL : pair (withDensityReal ρ) (backwardGenerator D ρ f) = ∫ x, ρ x * E x := by
    unfold pair
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    have : ∀ x, ρ x * backwardGenerator D ρ f x = D.invβ * Dh x + ρ x * E x := by
      intro x
      rw [hgen x]
      have := hLop x
      linear_combination (-D.invβ) * this
    simp_rw [this]
    rw [integral_add, integral_const_mul, hint0, mul_zero, zero_add]
    · exact (hDc.const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (hρc.mul hEc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  funext x
  unfold projMean
  rw [hpairL, hgen x, hKop x]
  ring


/-- Time-homogeneity: for the frozen coefficient, the propagator on `[0,τ]` is the time-shifted
classical solution with terminal time `T' ≥ τ`: `U^{0,τ}ψ = F(T' - τ)`. -/
theorem propagator_frozen_eq_of_one_le (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {T' : ℝ} (hT' : T' ∈ Set.Ioc 0 T)
    {ψ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D (fun _ => ρ) T' ψ F) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T') :
    propagator D (fun _ => ρ) 0 τ ψ = F (T' - τ) := by
  have hG := MFSemigroup.shift_classical D ρ hτ.2 hF
  have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρ) τ ψ f := ⟨_, hG⟩
  have hu := classical_adjoint_unique hd s hs0 hsd m hm R MB Λ VB D ν₀ T (fun _ => ρ) hA τ
    ⟨hτ.1, hτ.2.trans hT'.2⟩ ψ _ _ hex.choose_spec hG 0 ⟨le_rfl, hτ.1.le⟩
  simp only [propagator, hex, dite_true]
  rw [hu]
  simp

theorem frozen_classical_of_one_le (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (T' : ℝ) (hT' : 0 < T') :
    ∃ (R : Regime) (MB Λ VB : ℝ),
      AdjointData s (mStar d) R MB Λ VB (mfData d s hs0 hsd V β hβ) 0 T' (fun _ => ρβ) ∧
      ∃ F : ℝ → Torus d → ℝ,
        IsClassicalAdjointSolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) T' ψ F := by
  obtain ⟨R, MB, Λ, VB, hA⟩ := MFSemigroup.adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρC hpos (mStar d)
  refine ⟨R, MB, Λ, VB, hA 0 T' hT', ?_⟩
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd (mStar d) le_rfl R MB Λ VB
  have hψc : Continuous ψ :=
    ClassicalAux.continuous_of_isCk (MFSemigroup.isCk_nat_of_isSmooth hψ 1)
  obtain ⟨h1, -⟩ := hmain _ 0 T' (fun _ => ρβ) (hA 0 T' hT') T' ⟨hT', le_rfl⟩ ψ hψc
    (MFSemigroup.memSobolev_of_isSmooth hψ _)
  exact ⟨_, h1⟩

/-! ### The main theorem -/

/-- `equilibriumSemigroup_generator` (`HRS/PDE/MeanField.lean`) for `2 ≤ d`. -/
theorem equilibriumSemigroup_generator_of_one_le (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
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
  have := MFSemigroup.isProb_withDensityReal hprob
  have hK : ClassicalAux.ConvKernelFacts d D.s :=
    ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := MFSemigroup.isCk_nat_of_isSmooth hV 1
  have hV2 : Torus.IsCk 2 D.V := MFSemigroup.isCk_nat_of_isSmooth hV 2
  have hρ1 : Torus.IsCk 1 ρβ := MFSemigroup.isCk_nat_of_isSmooth hρC 1
  have hρ2 : Torus.IsCk 2 ρβ := MFSemigroup.isCk_nat_of_isSmooth hρC 2
  have hψ2 : Torus.IsCk 2 ψ := MFSemigroup.isCk_nat_of_isSmooth hψ 2
  have hρc : Continuous ρβ := ClassicalAux.continuous_of_isCk hρ1
  have h0 : propagator D (fun _ => ρβ) 0 0 ψ = ψ := MFSemigroup.propagator_zero D hK hV1 _ hρ1 hψ2
  refine ⟨?_, fun τ _ => MFSemigroup.pair_projMean _ _, ?_⟩
  · unfold equilibriumSemigroup
    rw [h0]
  intro x τ0 hτ0
  obtain ⟨R, MB, Λ, VB, hA, F, hF⟩ := frozen_classical_of_one_le hd s hs0 hsd β hβ V hV ρβ hprob hρC hpos ψ hψ
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
    · exact propagator_frozen_eq_of_one_le hd s hs0 hsd (mStar d) (by unfold mStar; omega) R MB Λ VB D 0 T'
        ρβ hA ⟨hT0, le_rfl⟩ hF ⟨h, hσ.2⟩
  let G : ℝ → ℝ := fun σ => F (T' - σ) x - pair (withDensityReal ρβ) (F (T' - σ))
  let Gd : ℝ → ℝ := fun σ => backwardGenerator D ρβ (F (T' - σ)) x -
    pair (withDensityReal ρβ) (backwardGenerator D ρβ (F (T' - σ)))
  have hsub : ContinuousOn (fun σ : ℝ => T' - σ) (Set.Icc 0 T') :=
    continuousOn_const.sub continuousOn_id
  have hGcont : ContinuousOn G (Set.Icc 0 T') :=
    ((MFSemigroup.continuousOn_F_apply hF x).comp hsub hmem).sub
      ((MFSemigroup.continuousOn_pair_F hprob hρc hF).comp hsub hmem)
  have hGdcont : ContinuousOn Gd (Set.Icc 0 T') :=
    ((MFSemigroup.continuousOn_bg_apply hF x).comp hsub hmem).sub
      ((MFSemigroup.continuousOn_pair_bg hprob hρc hF).comp hsub hmem)
  have hder : HasDerivWithinAt G (Gd τ0) (Set.Ici 0) τ0 := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]
      exact MFSemigroup.hasDerivWithinAt_Ici_zero hT0
        (fun σ hσ => (MFSemigroup.hasDerivAt_F hF x hσ).sub (MFSemigroup.hasDerivAt_pair_F hprob hρc hF hσ))
        hGcont hGdcont
    · exact ((MFSemigroup.hasDerivAt_F hF x ⟨h, hlt⟩).sub
        (MFSemigroup.hasDerivAt_pair_F hprob hρc hF ⟨h, hlt⟩)).hasDerivWithinAt
  have hS : ∀ σ ∈ Set.Icc 0 T', equilibriumSemigroup D ρβ σ ψ x = G σ := by
    intro σ hσ
    simp only [equilibriumSemigroup, projMean, hprop σ hσ, G]
  have hmem0 : τ0 ∈ Set.Icc 0 T' := ⟨hτ0, hlt.le⟩
  have hval : equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup D ρβ τ0 ψ) x = Gd τ0 := by
    have hf2 : Torus.IsCk 2 (F (T' - τ0)) := hF.c2 _ (hmem τ0 hmem0)
    have hS0 : equilibriumSemigroup D ρβ τ0 ψ = projMean (withDensityReal ρβ) (F (T' - τ0)) := by
      unfold equilibriumSemigroup
      rw [hprop τ0 hmem0]
    have hord := congrFun (operator_order_core_of_one_le hd D rfl β hβ rfl hV2 ρβ hρβ hρ2 hpos
      (F (T' - τ0)) hf2) x
    rw [hS0]
    unfold equilibriumGen
    rw [MFSemigroup.lop_projMean]
    exact hord.symm
  have hev : (fun τ' => equilibriumSemigroup D ρβ τ' ψ x) =ᶠ[𝓝[Set.Ici 0] τ0] G := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds hlt)] with σ hσ
    exact hS σ ⟨hσ.1, hσ.2.le⟩
  exact (hder.congr_of_eventuallyEq hev (hS τ0 hmem0)).congr_deriv hval.symm


end HRS.PDE.MFOneLe
