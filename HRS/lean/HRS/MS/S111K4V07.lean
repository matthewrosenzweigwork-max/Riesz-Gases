import HRS.MS.S111K4R6
import HRS.MS.S111K4Q5
import HRS.Whole.Window

/-!
# S11.1 / V02 (S11K4): `stationary_cubic_reinterpretation` (Pro `R26-T6C.V07/V08`), concrete assembly

For the thermal reference and `γ = β`, the cubic tensor of the window `[0,T]` is the cubic tensor of the window `[u,u+T]`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData)

variable {d : ℕ}

/-- The response inverse is the response, `ν`-a.e. -/
theorem k4_responseInverse_ae (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {f h : Euc d → ℝ}
    (hresp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h) :
    HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f
      =ᵐ[HRS.Whole.withDensityReal ρ] h := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  have hex' : ∃ u, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f u :=
    ⟨h, hresp⟩
  have hr' : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f) := by
    unfold HRS.Whole.responseInverse
    rw [dif_pos hex']
    exact hex'.choose_spec
  exact T.uniq _ _ _ hr' hresp

/-- **V07 core** (Pro `R26-T6C.V07`, here without the hypothesis `0 < T`): for the window `[u, u+T]` the cubic
formula and its integrability transport from the window-`0` data `χ0`. -/
theorem k4_v07 (hd : 2 ≤ d) (s a β T u : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    (hu : 0 ≤ u) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) (τ : Fin 3 → Icc (0 : ℝ) T)
    (φ : Fin 3 → Euc d → ℝ) (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i))
    (χ χ0 : Fin 3 → ℝ → Euc d → ℝ)
    (hχ : IsR2CrossDensities d s a β β ρ T u τ φ χ)
    (hχ0 : IsR2CrossDensities d s a β β ρ T 0 τ φ χ0)
    (hbase : CubicFormulaIntegrable (quadraticGradientDyn d s a β) (fun _ => ρ) β (HRS.Whole.withDensityReal ρ)
      (fun i => (τ i : ℝ)) φ χ0) :
    cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρ) β β (HRS.Whole.withDensityReal ρ)
        (fun i => u + (τ i : ℝ)) φ χ =
      cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρ) β β (HRS.Whole.withDensityReal ρ)
        (fun i => (τ i : ℝ)) φ χ0 ∧
    CubicFormulaIntegrable (quadraticGradientDyn d s a β) (fun _ => ρ) β (HRS.Whole.withDensityReal ρ)
      (fun i => u + (τ i : ℝ)) φ χ := by
  classical
  obtain ⟨M, TD⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu TD.prob
  set ν := HRS.Whole.withDensityReal ρ with hν
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hKd := TD.en.K
  have hτ0 : ∀ i, 0 ≤ (τ i : ℝ) := fun i => (τ i).2.1
  have hτT : ∀ i, (τ i : ℝ) ≤ T := fun i => (τ i).2.2
  have hT0 : 0 ≤ T := (hτ0 0).trans (hτT 0)
  set t : Fin 3 → ℝ := fun i => u + (τ i : ℝ) with ht
  have htu : ∀ i, u ≤ t i := fun i => by simp only [ht]; linarith [hτ0 i]
  have ht0 : ∀ i, 0 ≤ t i := fun i => hu.trans (htu i)
  have hexi : ∀ i, ∃ F, IsClassicalAdjointW C (t i) (φ i) F := fun i =>
    HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ (t i) (ht0 i) (φ i) (hφ i)
  set f : Fin 3 → ℝ → Euc d → ℝ := fun i r => propagatorW C r (t i) (φ i) with hfdef
  have hf : ∀ i, IsClassicalAdjointW C (t i) (φ i) (f i) := fun i => k4_prop_cls (hexi i)
  have hIcc : ∀ i, Icc (0 : ℝ) u ⊆ Icc 0 (t i) := fun i => Icc_subset_Icc le_rfl (htu i)
  obtain ⟨h, hresph, -, -, -, hFTC, Bh, hBh0, hhb, hcont⟩ :=
    k4_screened_triple hd s a β u hs0 hs ha hβ hu ρ hρ t htu φ hφ
  have hhm : ∀ i, ∀ v ∈ Icc (0 : ℝ) u, MemLp (h i v) 2 ν := fun i v hv =>
    HRS.MS.Tc5.tc5_memLp_of_cb (hresph i v hv).2
  have hhmeas : ∀ i, ∀ v ∈ Icc (0 : ℝ) u, Measurable (h i v) := fun i v hv =>
    (hresph i v hv).2.1.continuous.measurable
  choose B0 B1 B2 hB0 hB1 hB2 hBd using fun i => HRS.MS.S111X1.classical_bounds (hf i)
  set B1m : ℝ := ∑ i, B1 i with hB1m
  have hB1m0 : 0 ≤ B1m := Finset.sum_nonneg fun i _ => hB1 i
  have hg : ∀ i, ∀ r ∈ Icc (0 : ℝ) u, ∀ x, ‖gradient (f i r) x‖ ≤ B1m := by
    intro i r hr x
    rw [s111x2_norm_gradient]
    exact (hBd i r (hIcc i hr) x).2.1.trans
      (Finset.single_le_sum (f := B1) (fun j _ => hB1 j) (Finset.mem_univ i))
  have hgc : ∀ i, ∀ r ∈ Icc (0 : ℝ) u, Continuous (gradient (f i r)) := fun i r hr =>
    s111x2_gradient_continuous (((hf i).c2 r (hIcc i hr)).of_le (by norm_num))
  have hgcr : ∀ i, ∀ x, ContinuousOn (fun r => gradient (f i r) x) (Icc 0 u) := fun i x =>
    (k4_grad_cont_r (hf i) x).mono (hIcc i)
  set Ct : Fin 3 → ℝ → ℝ := fun i r => ∫ p : Euc d × Euc d,
    commutatorKernel d s (gradient (f i r)) p.1 p.2 * h (i + 1) r p.1 * h (i + 2) r p.2 ∂(ν.prod ν) with hCtdef
  set Dt : Fin 3 → ℝ → ℝ := fun i r => ∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) *
    h (i + 2) r x ∂ν with hDtdef
  have hCt : ∀ i, ContinuousOn (Ct i) (Icc 0 u) := fun i =>
    k4_comm_cont hKd TD.prob (S := Icc 0 u) (fun r => gradient (f i r)) (fun r hr => (hgc i r hr).measurable)
      (B1 := B1m) (fun r hr => hg i r hr) (hgcr i) (fun r => h (i + 1) r) (fun r => h (i + 2) r)
      (fun r hr => hhmeas (i + 1) r hr) (fun r hr => hhmeas (i + 2) r hr) (Bh := Bh)
      (fun r hr => hhb (i + 1) r hr) (fun r hr => hhb (i + 2) r hr)
      (fun r hr => hhm (i + 1) r hr) (fun r hr => hhm (i + 2) r hr)
      (fun r hr => hcont (i + 1) r hr) (fun r hr => hcont (i + 2) r hr)
  have hDt : ∀ i, ContinuousOn (Dt i) (Icc 0 u) := fun i =>
    k4_dir_cont TD.prob (S := Icc 0 u) (fun r => gradient (f i r)) (fun r => gradient (f (i + 1) r))
      (fun r hr => (hgc i r hr).measurable) (fun r hr => (hgc (i + 1) r hr).measurable)
      (B1 := B1m) (fun r hr => hg i r hr) (fun r hr => hg (i + 1) r hr) (hgcr i) (hgcr (i + 1))
      (fun r => h (i + 2) r) (fun r hr => hhmeas (i + 2) r hr) (Bh := Bh)
      (fun r hr => hhb (i + 2) r hr) (fun r hr => hhm (i + 2) r hr) (fun r hr => hcont (i + 2) r hr)
  have hχlow : ∀ j, ∀ r ∈ Icc (0 : ℝ) u, χ j r =ᵐ[volume] fun x => ρ x * h j r x := by
    intro j r hr
    have hrT : r ∈ Icc (0 : ℝ) (u + T) := ⟨hr.1, hr.2.trans (by linarith)⟩
    obtain ⟨-, hcov⟩ := hχ j r hrT
    exact k4_cross_ident0 hd s a β hs0 hs ha hβ ρ hρ hr.1 (hr.2.trans (htu j)) (hφ j) (hresph j r hr).1
      (hhm j r hr) (fun ψ hψ => (hcov ψ hψ).1) (fun ψ hψ => (hcov ψ hψ).2)
  have hlowC : ∀ i, ∀ r ∈ Icc (0 : ℝ) u,
      Integrable (fun p : Euc d × Euc d =>
        commutatorKernel d s (fun z => gradient (f i r) z) p.1 p.2 * χ (i + 1) r p.1 * χ (i + 2) r p.2) ∧
      (∫ x, ∫ y, commutatorKernel d s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y) =
        Ct i r := fun i r hr =>
    k4_comm_low hKd TD.prob (hgc i r hr).measurable (hg i r hr) (hhmeas (i + 1) r hr) (hhmeas (i + 2) r hr)
      (hhb (i + 1) r hr) (hhb (i + 2) r hr) (hχlow (i + 1) r hr) (hχlow (i + 2) r hr)
  have hlowD : ∀ i, ∀ r ∈ Icc (0 : ℝ) u,
      Integrable (fun x => inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) ∧
      (∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x) = Dt i r :=
    fun i r hr =>
    k4_dir_low TD.prob (G := fun x => inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x))
      ((hgc i r hr).measurable.inner (hgc (i + 1) r hr).measurable) (BG := B1m * B1m)
      (fun x => (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hg i r hr x) (hg (i + 1) r hr x) (norm_nonneg _) hB1m0))
      (hhmeas (i + 2) r hr) (hhb (i + 2) r hr) (hχlow (i + 2) r hr)
  -- the shift
  have hfs : ∀ i, ∀ b ∈ Icc (0 : ℝ) (τ i : ℝ), f i (u + b) = propagatorW C b (τ i : ℝ) (φ i) := by
    intro i b hb
    obtain ⟨F', hF'⟩ := hexi i
    exact s111x2_prop_shift hd hs0 hs ha hβ hρ hu hb.1 hb.2 hF'
  have hχs : ∀ j, ∀ b ∈ Icc (0 : ℝ) T, χ j (u + b) =ᵐ[volume] χ0 j b := by
    intro j b hb
    obtain ⟨-, hcov⟩ := hχ j (u + b) ⟨by linarith [hb.1], by linarith [hb.2]⟩
    obtain ⟨-, hcov0⟩ := hχ0 j b ⟨hb.1, by simpa using hb.2⟩
    exact k4_density_shift hd s a β hs0 hs ha hβ ρ hρ hu hb.1 (hτ0 j) (hφ j)
      (fun ψ hψ => (hcov ψ hψ).1) (fun ψ hψ => (hcov0 ψ hψ).1) (fun ψ hψ => (hcov ψ hψ).2)
      (fun ψ hψ => by rw [(hcov0 ψ hψ).2, zero_add])
  have hI0 := (k4_cfi_iff (quadraticGradientDyn d s a β) (fun _ => ρ) β ν (fun i => (τ i : ℝ)) φ χ0).1 hbase
  -- the initial terms
  have hri : ∀ i, ∀ v ∈ Icc (0 : ℝ) u,
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f i v) =ᵐ[ν] h i v := fun i v hv =>
    k4_responseInverse_ae hd s a β hs0 hs ha hβ ρ hρ (hresph i v hv).1
  have hriu : ∀ i, HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β
      (propagatorW C 0 (τ i : ℝ) (φ i)) =ᵐ[ν] h i u := by
    intro i
    have := hfs i 0 ⟨le_rfl, hτ0 i⟩
    rw [add_zero] at this
    rw [← this]
    exact hri i u ⟨hu, le_rfl⟩
  have h0u : (0 : ℝ) ∈ Icc (0 : ℝ) u := ⟨le_rfl, hu⟩
  have huu : u ∈ Icc (0 : ℝ) u := ⟨hu, le_rfl⟩
  have hAu : Integrable (fun x => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 0 0) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 1 0) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 2 0) x) ν := by
    have hb : Integrable (fun x => h 0 0 x * h 1 0 x * h 2 0 x) ν := by
      refine (integrable_const (Bh * Bh * Bh)).mono'
        (((hhmeas 0 0 h0u).mul (hhmeas 1 0 h0u)).mul (hhmeas 2 0 h0u)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hhb 0 0 h0u x) (hhb 1 0 h0u x) (abs_nonneg _) hBh0) (hhb 2 0 h0u x)
        (abs_nonneg _) (by positivity)
    refine hb.congr ?_
    filter_upwards [hri 0 0 h0u, hri 1 0 h0u, hri 2 0 h0u] with x h1 h2 h3
    rw [h1, h2, h3]
  have hAeq_u : (∫ x, HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 0 0) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 1 0) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f 2 0) x ∂ν) =
      ∫ x, h 0 0 x * h 1 0 x * h 2 0 x ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hri 0 0 h0u, hri 1 0 h0u, hri 2 0 h0u] with x h1 h2 h3
    rw [h1, h2, h3]
  have hAeq_0 : (∫ x, HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β
        (propagatorW C 0 (τ 0 : ℝ) (φ 0)) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (propagatorW C 0 (τ 1 : ℝ) (φ 1)) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (propagatorW C 0 (τ 2 : ℝ) (φ 2)) x ∂ν) =
      ∫ x, h 0 u x * h 1 u x * h 2 u x ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hriu 0, hriu 1, hriu 2] with x h1 h2 h3
    rw [h1, h2, h3]
  obtain ⟨hCFIu, hdiff⟩ := k4_shift_core (s := s) (β := β) (μ0 := ν) hu (fun i => (τ i : ℝ)) (hτ0) (hτT)
    (T := T) (f := f) (g := fun i a => propagatorW C a (τ i : ℝ) (φ i)) (χ := χ) (χ0 := χ0)
    (r0 := fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f i 0))
    (r0' := fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β
      (propagatorW C 0 (τ i : ℝ) (φ i)))
    hfs hχs Ct Dt hlowC hlowD hCt hDt hI0 hAu
  -- the screened-forcing identity
  have hCtI : ∀ i, IntegrableOn (Ct i) (Icc 0 u) := fun i => (hCt i).integrableOn_Icc
  have hDtI : ∀ i, IntegrableOn (Dt i) (Icc 0 u) := fun i => (hDt i).integrableOn_Icc
  have hsfint : (∫ q in Icc (0 : ℝ) u, k4_screenedForcing s β ν f h q) =
      -(∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Ct i r) + (2 / β) * ∑ i : Fin 3, ∫ r in Icc (0 : ℝ) u, Dt i r := by
    have e : ∀ q, k4_screenedForcing s β ν f h q = -(∑ i : Fin 3, Ct i q) + (2 / β) * ∑ i : Fin 3, Dt i q :=
      fun q => rfl
    simp_rw [e]
    have hi1 : Integrable (fun q => -(∑ i : Fin 3, Ct i q)) (volume.restrict (Icc (0 : ℝ) u)) :=
      (integrable_finset_sum _ (fun i _ => hCtI i)).neg
    have hi2 : Integrable (fun q => (2 / β) * ∑ i : Fin 3, Dt i q) (volume.restrict (Icc (0 : ℝ) u)) :=
      (integrable_finset_sum _ (fun i _ => hDtI i)).const_mul _
    rw [integral_add hi1 hi2, integral_neg, integral_const_mul,
      integral_finset_sum _ (fun i _ => hCtI i), integral_finset_sum _ (fun i _ => hDtI i)]
  have hF : (∫ x, h 0 u x * h 1 u x * h 2 u x ∂ν) - (∫ x, h 0 0 x * h 1 0 x * h 2 0 x ∂ν) =
      ∫ q in Icc (0 : ℝ) u, k4_screenedForcing s β ν f h q := hFTC 0 u le_rfl hu le_rfl
  refine ⟨?_, (k4_cfi_iff (quadraticGradientDyn d s a β) (fun _ => ρ) β ν (fun i => u + (τ i : ℝ)) φ χ).2
    hCFIu⟩
  rw [k4_cf_eq, k4_cf_eq]
  have hz : K4Cf s β ν (fun i => u + ↑(τ i)) f
      (fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β (f i 0)) χ -
      K4Cf s β ν (fun i => ↑(τ i)) (fun i a => propagatorW C a (↑(τ i)) (φ i))
        (fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) ν β
          (propagatorW C 0 (↑(τ i)) (φ i))) χ0 = 0 := by
    rw [hdiff, hAeq_u, hAeq_0]
    linarith [hF, hsfint]
  exact sub_eq_zero.1 hz

/-- Pro `R26-T6C.V07` (`r26t6c_stationary_formula_shift`) with its exact hypotheses. -/
theorem k4_v07_pro (hd : 2 ≤ d) (s a β T u : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hu : 0 ≤ u) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (τ : Fin 3 → Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ) (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i))
    (χ χ0 : Fin 3 → ℝ → Euc d → ℝ)
    (hχ : IsR2CrossDensities d s a β β ρ T u τ φ χ)
    (hχ0 : IsR2CrossDensities d s a β β ρ T 0 τ φ χ0)
    (hbase : CubicFormulaIntegrable (quadraticGradientDyn d s a β) (fun _ => ρ) β (HRS.Whole.withDensityReal ρ)
      (fun i => (τ i : ℝ)) φ χ0) :
    cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρ) β β (HRS.Whole.withDensityReal ρ)
        (fun i => u + (τ i : ℝ)) φ χ =
      cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρ) β β (HRS.Whole.withDensityReal ρ)
        (fun i => (τ i : ℝ)) φ χ0 ∧
    CubicFormulaIntegrable (quadraticGradientDyn d s a β) (fun _ => ρ) β (HRS.Whole.withDensityReal ρ)
      (fun i => u + (τ i : ℝ)) φ χ :=
  k4_v07 hd s a β T u hs0 hs ha hβ hu ρ hρ τ φ hφ χ χ0 hχ hχ0 hbase

end HRS.MS.S111K4
