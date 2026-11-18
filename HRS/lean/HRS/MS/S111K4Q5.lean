import HRS.MS.S111K4Q4

/-!
# S11.1 / T03 (S11K4), Pro `R26-T6C.P09` (= `S111.T03` with the orbit hypothesis discharged): the screened triple identity

For oscillator tests `φ_i`, times `t_i ≥ H` and the thermal reference, there are smooth response representatives `h_i(v)`, `v ∈ [0,H]`, of the
classical adjoint orbits `f_i(v) = U^{v,t_i} φ_i` such that `K(v) = ∫ h_0 h_1 h_2 dμ` is absolutely continuous with a.e. derivative the screened forcing.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

theorem k4_prop_cls {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} (hex : ∃ F, IsClassicalAdjointW C t φ F) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = hex.choose := by
    funext r
    unfold propagatorW
    rw [dif_pos hex]
  rw [this]
  exact hex.choose_spec

theorem k4_screened_triple (hd : 2 ≤ d) (s a β H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (hH : 0 ≤ H) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (t : Fin 3 → ℝ) (ht : ∀ i, H ≤ t i) (φ : Fin 3 → Euc d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) :
    ∃ h : Fin 3 → ℝ → Euc d → ℝ,
      (∀ i, ∀ v ∈ Icc (0 : ℝ) H,
        HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) v (t i) (φ i)) (h i v) ∧
        MemCb 2 (h i v)) ∧
      AbsolutelyContinuousOnInterval
        (fun v => ∫ x, h 0 v x * h 1 v x * h 2 v x ∂(HRS.Whole.withDensityReal ρ)) 0 H ∧
      IntegrableOn (k4_screenedForcing s β (HRS.Whole.withDensityReal ρ)
        (fun i v => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) v (t i) (φ i)) h)
        (Icc 0 H) ∧
      (∀ v ∈ Ioo 0 H, HasDerivAt
        (fun v => ∫ x, h 0 v x * h 1 v x * h 2 v x ∂(HRS.Whole.withDensityReal ρ))
        (k4_screenedForcing s β (HRS.Whole.withDensityReal ρ)
          (fun i v => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) v (t i) (φ i)) h v) v) ∧
      (∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ H →
        (∫ x, h 0 w x * h 1 w x * h 2 w x ∂(HRS.Whole.withDensityReal ρ)) -
          (∫ x, h 0 v x * h 1 v x * h 2 v x ∂(HRS.Whole.withDensityReal ρ)) =
        ∫ q in Icc v w, k4_screenedForcing s β (HRS.Whole.withDensityReal ρ)
          (fun i v => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) v (t i) (φ i)) h q) ∧
      ∃ Bh : ℝ, 0 ≤ Bh ∧ (∀ i, ∀ v ∈ Icc (0 : ℝ) H, ∀ x, |h i v x| ≤ Bh) ∧
        ∀ i, ∀ v ∈ Icc (0 : ℝ) H,
          ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (h i q)) (Icc 0 H) v := by
  classical
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hKd := T.en.K
  -- the classical orbits
  have hex : ∀ i, ∃ F, IsClassicalAdjointW C (t i) (φ i) F := fun i =>
    HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ (t i) (hH.trans (ht i)) (φ i) (hφ i)
  set f : Fin 3 → ℝ → Euc d → ℝ := fun i v => propagatorW C v (t i) (φ i) with hfdef
  have hf : ∀ i, IsClassicalAdjointW C (t i) (φ i) (f i) := fun i => k4_prop_cls (hex i)
  choose Bi hBi using fun i => k4_cb_of_classical (hf i)
  choose B0 B1 B2 h0 h1 h2 hBd using fun i => HRS.MS.S111X1.classical_bounds (hf i)
  obtain ⟨Cr, hCr0, hCr⟩ := k4_resp_rep hd s a β hs0 hs ha hβ ρ hρ
  have hIcc : ∀ i, Icc (0 : ℝ) H ⊆ Icc 0 (t i) := fun i => Icc_subset_Icc le_rfl (ht i)
  have hrep : ∀ i, ∀ v ∈ Icc (0 : ℝ) H, ∃ r : Euc d → ℝ,
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (f i v) r ∧ MemCb 2 r ∧
        cbNorm 2 r ≤ Cr * cbNorm 2 (f i v) := fun i v hv => hCr (f i v) (hBi i v (hIcc i hv)).1
  set h : Fin 3 → ℝ → Euc d → ℝ := fun i v => if hv : v ∈ Icc (0 : ℝ) H then (hrep i v hv).choose else 0 with hhdef
  have hhspec : ∀ i, ∀ v (hv : v ∈ Icc (0 : ℝ) H),
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (f i v) (h i v) ∧ MemCb 2 (h i v) ∧
        cbNorm 2 (h i v) ≤ Cr * cbNorm 2 (f i v) := by
    intro i v hv
    simp only [hhdef, dif_pos hv]
    exact (hrep i v hv).choose_spec
  have hhm : ∀ i v, MemLp (h i v) 2 μ := by
    intro i v
    by_cases hv : v ∈ Icc (0 : ℝ) H
    · exact HRS.MS.Tc5.tc5_memLp_of_cb (hhspec i v hv).2.1
    · simp only [hhdef, dif_neg hv]
      exact MeasureTheory.MemLp.zero'
  set Bh : ℝ := Cr * ∑ i, |Bi i| with hBhdef
  have hBh0 : 0 ≤ Bh := by positivity
  have hhb : ∀ i, ∀ v ∈ Icc (0 : ℝ) H, ∀ x, |h i v x| ≤ Bh := by
    intro i v hv x
    have h1 := HRS.MS.Tc5.tc5_cb_sup_le (hhspec i v hv).2.1 x
    have h2 := (hhspec i v hv).2.2
    have h3 := (hBi i v (hIcc i hv)).2
    have h4 : Bi i ≤ ∑ j, |Bi j| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Bi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    rw [← Real.norm_eq_abs]
    calc ‖h i v x‖ ≤ cbNorm 2 (h i v) := h1
      _ ≤ Cr * cbNorm 2 (f i v) := h2
      _ ≤ Cr * Bi i := mul_le_mul_of_nonneg_left h3 hCr0
      _ ≤ Bh := mul_le_mul_of_nonneg_left h4 hCr0
  refine ⟨h, fun i v hv => ⟨(hhspec i v hv).1, (hhspec i v hv).2.1⟩, ?_⟩
  set K : ℝ → ℝ := fun v => ∫ x, h 0 v x * h 1 v x * h 2 v x ∂μ with hKdef
  set sf : ℝ → ℝ := k4_screenedForcing s β μ f h with hsfdef
  -- derivative
  have hderK : ∀ v ∈ Ioo (0 : ℝ) H, HasDerivAt K (sf v) v := by
    intro v hv
    have hvI : v ∈ Icc (0 : ℝ) H := ⟨hv.1.le, hv.2.le⟩
    set dh : Fin 3 → Euc d → ℝ := fun i x => β⁻¹ * s111x2_L ρ (f i v) x with hdh
    have hCbD : ∀ i, CbD (f i v) (B1 i) (B2 i) := fun i =>
      ⟨(hf i).c2 v (hIcc i hvI), fun x => (hBd i v (hIcc i hvI) x).2.1, fun x => (hBd i v (hIcc i hvI) x).2.2⟩
    have hdm : ∀ i, MemLp (dh i) 2 μ := fun i => (s111x2_L_memLp T (hCbD i)).const_mul _
    have hder : ∀ i, HasDerivAt (fun q => (hhm i q).toLp (h i q)) ((hdm i).toLp (dh i)) v := by
      intro i
      have := k4_orbit_deriv hd s a β H hs0 hs ha hβ ρ hρ (ht i) (hf i) (h i) (hhm i)
        (fun q hq => (hhspec i q hq).1) hv
      have e1 : (fun q => k4_toL μ (h i q)) = fun q => (hhm i q).toLp (h i q) := by
        funext q; exact k4_toL_eq (hhm i q)
      rw [e1, k4_toL_eq (hdm i)] at this
      exact this
    have hbdd : ∀ᶠ q in 𝓝 v, ∀ i, ∀ᵐ x ∂μ, |h i q x| ≤ Bh := by
      filter_upwards [Icc_mem_nhds hv.1 hv.2] with q hq i
      exact ae_of_all _ (hhb i q hq)
    have hKd' := k4_triple_derivative μ h dh v Bh hBh0 hhm hdm hder hbdd
    have hst := k4_static_screened_triple hd s a β hs0 hs ha hβ ρ hρ (fun i => f i v) (fun i => h i v)
      (fun i => (hBi i v (hIcc i hvI)).1) (fun i => (hhspec i v hvI).2.1) (fun i => (hhspec i v hvI).1)
    have hsfv : sf v = ∑ i : Fin 3, ∫ x, dh i x * h (i + 1) v x * h (i + 2) v x ∂μ := by
      calc sf v = k4_screenedForcing s β (HRS.Whole.withDensityReal ρ) (fun i _ => f i v) (fun i _ => h i v) 0 := rfl
        _ = ∑ i : Fin 3, ∫ x, β⁻¹ * s111x2_L ρ (f i v) x * h (i + 1) v x * h (i + 2) v x
              ∂(HRS.Whole.withDensityReal ρ) := hst.symm
        _ = _ := rfl
    rw [hsfv]
    exact hKd'
  -- continuity on the closed interval
  have hKc : ContinuousOn K (Icc 0 H) := by
    intro v hv
    have hc : ∀ i, Tendsto (fun q => ‖k4_toL μ (h i q) - k4_toL μ (h i v)‖) (𝓝[Icc 0 H] v) (𝓝 0) := by
      intro i
      have := k4_orbit_cont hd s a β H hs0 hs ha hβ ρ hρ (ht i) (hf i) (h i) (hhm i)
        (fun q hq => (hhspec i q hq).1) hv
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 this)
    have hz : Tendsto (fun q => Bh ^ 2 * (‖k4_toL μ (h 0 q) - k4_toL μ (h 0 v)‖ +
        ‖k4_toL μ (h 1 q) - k4_toL μ (h 1 v)‖ + ‖k4_toL μ (h 2 q) - k4_toL μ (h 2 v)‖)) (𝓝[Icc 0 H] v) (𝓝 0) := by
      have := (((hc 0).add (hc 1)).add (hc 2)).const_mul (Bh ^ 2)
      simpa using this
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun q => dist_nonneg) ?_ hz
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [Real.dist_eq]
    exact k4_trip_diff hBh0 (hhm 0 v) (hhm 0 q) (hhm 1 v) (hhm 1 q) (hhm 2 v) (hhm 2 q)
      (ae_of_all _ (hhb 0 v hv)) (ae_of_all _ (hhb 1 v hv)) (ae_of_all _ (hhb 1 q hq)) (ae_of_all _ (hhb 2 q hq))
  -- the bound of the forcing
  set B1m : ℝ := ∑ i, B1 i with hB1m
  set J : ℝ := ∫ p : Euc d × Euc d, ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)
    ∂(volume.prod volume) with hJ
  set A : ℝ := 6 * B1m * Bh ^ 2 * J + 6 / β * (B1m ^ 2 * Bh) with hA
  have hsfb : ∀ q ∈ Icc (0 : ℝ) H, |sf q| ≤ A := by
    intro q hq
    have hg : ∀ i x, ‖gradient (f i q) x‖ ≤ B1m := fun i x => by
      rw [s111x2_norm_gradient]
      exact (hBd i q (hIcc i hq) x).2.1.trans
        (Finset.single_le_sum (f := B1) (fun j _ => h1 j) (Finset.mem_univ i))
    have hgc : ∀ i, Continuous (gradient (f i q)) := fun i =>
      s111x2_gradient_continuous (((hf i).c2 q (hIcc i hq)).of_le (by norm_num))
    have hhc : ∀ i, Continuous (h i q) := fun i => (hhspec i q hq).2.1.1.continuous
    exact k4_sf_bound hKd T.prob hβ (fun i => f i q) (fun i => h i q) hg hgc (fun i x => hhb i q hq x) hhc
  -- measurability and integrability
  have hae : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) H)), sf v = deriv K v :=
    s111x2_ae_icc_of_ioo fun r hr => (hderK r hr).deriv.symm
  have hmeas : AEStronglyMeasurable sf (volume.restrict (Icc (0 : ℝ) H)) :=
    (measurable_deriv K).aestronglyMeasurable.congr (hae.mono fun v hv => hv.symm)
  have hint : IntegrableOn sf (Icc 0 H) :=
    Integrable.mono' (integrable_const A) hmeas
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun v hv => by
        rw [Real.norm_eq_abs]; exact hsfb v hv))
  have hext : ∃ Bh : ℝ, 0 ≤ Bh ∧ (∀ i, ∀ v ∈ Icc (0 : ℝ) H, ∀ x, |h i v x| ≤ Bh) ∧
        ∀ i, ∀ v ∈ Icc (0 : ℝ) H,
          ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (h i q)) (Icc 0 H) v :=
    ⟨Bh, hBh0, hhb, fun i v hv => k4_orbit_cont hd s a β H hs0 hs ha hβ ρ hρ (ht i) (hf i) (h i) (hhm i)
      (fun q hq => (hhspec i q hq).1) hv⟩
  rcases hH.eq_or_lt with h0 | hHpos
  · subst h0
    refine ⟨AbsolutelyContinuousOnInterval.rfl, hint, hderK, ?_, hext⟩
    intro v w hv hvw hw
    have hv0 : v = 0 := le_antisymm (hvw.trans hw) hv
    have hw0 : w = 0 := le_antisymm hw (hv.trans hvw)
    subst hv0; subst hw0
    simp
  · have := k4_triple_ftc H hHpos K sf hKc hint hderK A (fun v hv => hsfb v ⟨hv.1.le, hv.2.le⟩)
    exact ⟨this.1, hint, hderK, this.2, hext⟩

end HRS.MS.S111K4
