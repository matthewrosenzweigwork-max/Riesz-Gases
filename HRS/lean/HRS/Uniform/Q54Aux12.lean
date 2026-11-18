import HRS.Uniform.Q54Aux11
import HRS.PDE.MeanFieldPairSeries

/-!
# Q54, part 12: linearity, constants, self and semigroup properties of the propagator on `Dom J`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem propagatorCoeff_sub' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {ψc ψc' : Coeff d} (hψ : MemHs (m : ℝ) ψc) (hψ' : MemHs (m : ℝ) ψc') {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D μ m t (ψc - ψc') τ = propagatorCoeff D μ m t ψc τ - propagatorCoeff D μ m t ψc' τ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, w1, -⟩ := hspec D ν₀ T μ hA t ht ψc hψ
  obtain ⟨h2, w2, -⟩ := hspec D ν₀ T μ hA t ht ψc' hψ'
  have hsol := MFAdjoint.isForwardSolution_sub hd hA ht h1 h2
  have hw := MFAdjoint.weakContinuousInHs_sub (weakContinuousInHs_mono hm1 w1)
    (weakContinuousInHs_mono hm1 w2)
  exact MFAdjoint.propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht (memHs_sub hψ hψ') hsol hw τ hτ

theorem propagatorCoeff_lin (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {a b : Coeff d} (ha : MemHs (m : ℝ) a) (hb : MemHs (m : ℝ) b) (α β : ℂ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D μ m t (fun k => α * a k + β * b k) τ =
      fun k => α * propagatorCoeff D μ m t a τ k + β * propagatorCoeff D μ m t b τ k := by
  have hsa := MFThermalReg.memHs_smul ha α
  have hsb := MFThermalReg.memHs_smul hb (-β)
  have e : (fun k => α * a k + β * b k) = (fun k => α * a k) - (fun k => (-β) * b k) := by
    funext k; simp only [Pi.sub_apply]; ring
  rw [e, propagatorCoeff_sub' hd hs0 hsd hm hA ht hsa hsb hτ,
    MFPair.propagatorCoeff_smul_aux hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA ht α ha hτ,
    MFPair.propagatorCoeff_smul_aux hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA ht (-β) hb hτ]
  funext k; simp only [Pi.sub_apply]; ring

theorem coeffOf_lin {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (α β : ℝ) :
    coeffOf (fun x => α * φ x + β * ψ x) = fun k => (α : ℂ) * coeffOf φ k + (β : ℂ) * coeffOf ψ k := by
  funext k
  have := MFThermalReg.coeffOf_add_fun (φ := fun x => α * φ x) (ψ := fun x => β * ψ x)
    (continuous_const.mul hφ) (continuous_const.mul hψ) k
  rw [this, MFThermalReg.coeffOf_const_mul_fun, MFThermalReg.coeffOf_const_mul_fun]

theorem dom_closed {J : ℕ} {φ ψ : Torus d → ℝ} (hφ : Dom J φ) (hψ : Dom J ψ) (α β : ℝ) :
    Dom J (fun x => α * φ x + β * ψ x) := by
  have hc : Continuous (fun x => α * φ x + β * ψ x) :=
    (continuous_const.mul hφ.1).add (continuous_const.mul hψ.1)
  refine ⟨hc, memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous hc) ?_⟩
  rw [coeffOf_lin hφ.1 hψ.1]
  have h1 := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  have h2 := (hsNormSq_coeffOf (J : ℝ) ψ hψ.2).1
  exact MFThermalReg.memHs_add (MFThermalReg.memHs_smul h1 (α : ℂ)) (MFThermalReg.memHs_smul h2 (β : ℂ))

theorem dom_smooth {J : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Dom J φ :=
  ⟨ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hφ),
    MFSemigroup.memSobolev_of_isSmooth hφ _⟩

/-- reality and summability of the coefficient path -/
theorem pc_data (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ1 : 1 ≤ J) (hJd : (d : ℝ) / 2 < J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ}
    (hφ : Dom J φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    IsRealCoeff (propagatorCoeff D μ J t (coeffOf φ) τ) ∧
      Summable (fun k => ‖propagatorCoeff D μ J t (coeffOf φ) τ k‖) := by
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht (coeffOf φ) hφc
  have hre0 : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (hφ.2.1.integrable one_le_two)
  exact ⟨ClassicalPart.propagatorCoeff_real hd s hs0 hsd J hJ1 R MB Λ VB D ν₀ T μ hA t ht
    (coeffOf φ) hφc hre0 τ hτ, summable_norm_of_memHs (J : ℝ) hJd _ (hw.1 τ hτ)⟩

theorem prop_lin (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ ψ : Torus d → ℝ}
    (hφ : Dom J φ) (hψ : Dom J ψ) (α β : ℝ) {u : ℝ} (hu : u ∈ Set.Icc 0 t) :
    propagator D μ u t (fun x => α * φ x + β * ψ x) =
      fun x => α * propagator D μ u t φ x + β * propagator D μ u t ψ x := by
  have hJ3 := ClassicalPart.three_le_mStar d
  have hJ1 : 1 ≤ J := by omega
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hχ := dom_closed hφ hψ α β
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [(prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hχ hu).1,
    (prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hφ hu).1,
    (prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hψ hu).1]
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  have hψc : MemHs (J : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf (J : ℝ) ψ hψ.2).1
  rw [coeffOf_lin hφ.1 hψ.1, propagatorCoeff_lin hd hs0 hsd hJ1 hA ht hφc hψc (α : ℂ) (β : ℂ) hτ]
  obtain ⟨-, hs1⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB Λ VB D ν₀ T μ hA ht hφ hτ
  obtain ⟨-, hs2⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB Λ VB D ν₀ T μ hA ht hψ hτ
  funext x
  have e1 := MFPair.toFun_add_aux (fun k => (α : ℂ) * propagatorCoeff D μ J t (coeffOf φ) (t - u) k)
    (fun k => (β : ℂ) * propagatorCoeff D μ J t (coeffOf ψ) (t - u) k) (by
      simpa [norm_mul] using hs1.mul_left ‖(α : ℂ)‖) (by simpa [norm_mul] using hs2.mul_left ‖(β : ℂ)‖) x
  have e2 : (fun k => (α : ℂ) * propagatorCoeff D μ J t (coeffOf φ) (t - u) k +
      (β : ℂ) * propagatorCoeff D μ J t (coeffOf ψ) (t - u) k) =
      (fun k => (α : ℂ) * propagatorCoeff D μ J t (coeffOf φ) (t - u) k) +
        (fun k => (β : ℂ) * propagatorCoeff D μ J t (coeffOf ψ) (t - u) k) := rfl
  rw [e2, e1, MFPair.toFun_smul_aux, MFPair.toFun_smul_aux]

theorem prop_const (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (c : ℝ)
    {u : ℝ} (hu : u ∈ Set.Icc 0 t) :
    propagator D μ u t (fun _ => c) = fun _ => c := by
  have hJ3 := ClassicalPart.three_le_mStar d
  have hJ1 : 1 ≤ J := by omega
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hdom : Dom J (fun _ : Torus d => c) := dom_smooth (isSmooth_const' c)
  rw [(prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hdom hu).1]
  have hcoef : coeffOf (fun _ : Torus d => c) = (c : ℂ) • deltaCoeff (0 : Lattice d) := by
    funext j; rw [coeffOf_const]; rfl
  have hφc : MemHs (J : ℝ) (coeffOf (fun _ : Torus d => c)) := (hsNormSq_coeffOf (J : ℝ) _ hdom.2).1
  have hsol : IsForwardSolution D μ t (coeffOf (fun _ : Torus d => c)) (fun _ => coeffOf (fun _ : Torus d => c)) := by
    refine ⟨fun τ _ => hφc.mono (by exact_mod_cast hJ1), fun k => ?_, fun k τ hτ => ?_⟩
    · have : (fun σ => forwardGen D (μ (t - σ)) (coeffOf (fun _ : Torus d => c)) k) = fun _ => 0 := by
        funext σ; rw [hcoef, MFAdjoint.forwardGen_smul_delta]; rfl
      rw [this]; exact integrableOn_const (by simp) (by simp)
    · have : ∀ σ, forwardGen D (μ (t - σ)) (coeffOf (fun _ : Torus d => c)) k = 0 := by
        intro σ; rw [hcoef, MFAdjoint.forwardGen_smul_delta]; rfl
      simp [this]
  have hw : WeakContinuousInHs 1 (fun _ : ℝ => coeffOf (fun _ : Torus d => c)) t :=
    ⟨fun τ _ => hφc.mono (by exact_mod_cast hJ1), fun G _ => continuousOn_const⟩
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hpc := MFAdjoint.propagatorCoeff_eq_of_solution hd hs0 hsd hJ1 hA ht hφc hsol hw (t - u) hτ
  rw [hpc]
  have hs : Summable fun k => ‖coeffOf (fun _ : Torus d => c) k‖ :=
    summable_norm_of_memHs (J : ℝ) hJd _ hφc
  exact toFun_coeffOf (fun _ : Torus d => c) continuous_const hs

theorem prop_self_pos (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ}
    (hφ : Dom J φ) : propagator D μ t t φ = φ := by
  have hJ3 := ClassicalPart.three_le_mStar d
  have hJ1 : 1 ≤ J := by omega
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hut : t ∈ Set.Icc 0 t := ⟨ht.1.le, le_rfl⟩
  rw [(prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hφ hut).1, sub_self]
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht (coeffOf φ) hφc
  have h0 : propagatorCoeff D μ J t (coeffOf φ) 0 = coeffOf φ := by
    funext k
    have := hsol.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  rw [h0]
  exact toFun_coeffOf φ hφ.1 (summable_norm_of_memHs (J : ℝ) hJd _ hφc)

theorem prop_self_zero (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    propagator D μ 0 0 φ = φ := by
  have hK : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ J + 3)) hA.hV.1
  have hμ1 : Torus.IsCk 1 (μ 0) := ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ J + 3))
    (hA.hμ.smooth 0 ⟨le_rfl, hA.hT.le⟩)
  exact MFSemigroup.propagator_zero D hK hV1 μ hμ1 (MFSemigroup.isCk_nat_of_isSmooth hφ 2)

end HRS.Uniform.Q54
