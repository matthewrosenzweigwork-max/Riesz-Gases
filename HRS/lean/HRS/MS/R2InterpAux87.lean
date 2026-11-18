import HRS.MS.R2InterpAux86

/-!
# S10.2 (worker S10R), part 87 (packet F5g): the centred Itô identity for the orbit `U^{r,t}φ_α` along the particle path

`ζ_N^τ(f_τ) = ζ_N^0(f_0) + (√N √(2ν)/N) ∫_0^τ ∇f_r(X_r) · dW'_r - N^{-1/2} ∫_0^τ B_N^r(f_r) dr` a.s., for all `τ ∈ [0,t]`, with `B_N = r2QuadField`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem s102_orbit_zeta (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X) {M L p K : ℝ}
    (hp : 1 < p) (hρR : IsRound2Density d s M L ρ)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (m : ℝ) (α : MultiIndex d)
    (hcls : ∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t (oscTestFun m α) f) :
    ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t,
      s102_zf P X ζ τ (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) τ t (oscTestFun m α)) =
        s102_zf P X ζ 0 (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t (oscTestFun m α)) +
        (Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N)) *
          itoIntegral P ℱ W' (s102_Ig (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t
            (oscTestFun m α)) t X) τ ζ +
        ∫ r in Icc (0 : ℝ) τ, (-(Real.sqrt N)⁻¹ * r2QuadField s (HRS.Whole.withDensityReal ρ) P X r ζ
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t (oscTestFun m α))) := by
  classical
  set D := quadraticGradientDyn d s a β with hD
  set C := D.coeff (fun _ => ρ) with hC
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hμp : IsProbabilityMeasure μ := HRS.MS.R2Mt.s92_isProb_mu hρR.prob
  set f : ℝ → Euc d → ℝ := fun r => propagatorW C r t (oscTestFun m α) with hfdef
  have hf : IsClassicalAdjointW C t (oscTestFun m α) f := s102_propagator_classical hcls
  have hN0 : 0 < N := by omega
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have hsub : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  -- the duality identity
  have hdual := s102_duality hd hs0 hs ha hβ hρ hT P X₀ W X hX ℱ W' hF ht m α
  -- the kernel family
  set V : ℝ → Euc d → Euc d := fun r x => if r ∈ Icc (0 : ℝ) t then gradient (f r) x else 0 with hV
  have hVm : Measurable fun p : ℝ × Euc d => V p.1 p.2 := s102_gradJoint_meas hf
  set hK : ℝ → Euc d → Euc d → ℝ := fun r => commutatorKernel d s (V r) with hKdef
  have hKm : Measurable fun q : ℝ × Euc d × Euc d => hK q.1 q.2.1 q.2.2 := s102_kernelFam_meas s V hVm
  have hKr : ∀ r ∈ Icc (0 : ℝ) t, hK r = commutatorKernel d s (fun x => gradient (f r) x) := by
    intro r hr
    simp only [hKdef, hV, if_pos hr]
  obtain ⟨B, hB⟩ := s102_orbit_kernel_bdd hs0 hf
  have hKb : ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel s B (hK r) := fun r hr => by rw [hKr r hr]; exact hB r hr
  have hXm : Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2 :=
    measurable_progressive_min_gen (u := ofNNRealTime X) hF.progressive t
  have hdens' : ∀ r ∈ Icc (0 : ℝ) t, HasR2ActualDensity s β p K μ (P.map (X r.toNNReal)) :=
    fun r hr => hdens r (hsub r hr)
  obtain ⟨hI1, hI2⟩ := s102_quad_prodInt hd hs0 hs M L β p K B hβ hp hρR hN P X t hXm hdens' hK hKm hKb
  have he : Integrable (fun q : ℝ × Ω => pairEnergy (hK q.1) (X q.1.toNNReal q.2) μ)
      ((volume.restrict (Icc (0 : ℝ) t)).prod P) := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
    refine (hI1.const_mul (N : ℝ)⁻¹).congr (Eventually.of_forall fun q => ?_)
    simp only
    field_simp
    rfl
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  -- fluctuation interaction = - pair energy
  have hFe : ∀ᵐ ζ ∂P, ∀ r ∈ Icc (0 : ℝ) t, flucInteractionRd D (f r) (X r.toNNReal ζ) ((fun _ => ρ) r) =
      -pairEnergy (hK r) (X r.toNNReal ζ) μ := by
    filter_upwards [hX.no_collision] with ζ hno r hr
    have hint : ∀ a : Euc d, Integrable (commutatorKernel d D.s (fun z => gradient (f r) z) a) μ := fun a => by
      have := (HRS.MS.R2Mt.s92_kernel_integrable (by omega) hs0 hsd M hρR.prob hρR.bdd (hKb r hr)).1 a
      rw [hKr r hr] at this
      exact this
    have := s102_flucInteractionRd_eq D rfl hN0 (f r) (X r.toNNReal ζ)
      (hno r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans ht.2)) ρ hint
    rw [this, hKr r hr]
    rfl
  -- bounds and measurability of the orbit
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |f r x| ≤ Bf := by
    obtain ⟨Bf, hBf⟩ := hf.bdd 0 (Nat.zero_le _)
    refine ⟨Bf, fun r hr x => ?_⟩
    have := hBf r hr x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hfm : ∀ r ∈ Icc (0 : ℝ) t, Measurable (f r) := fun r hr => (hf.c2 r hr).continuous.measurable
  have hXτm : ∀ τ : ℝ, Measurable (X τ.toNNReal) := fun τ => hX.adapted _
  set aR : ℝ → Ω → ℝ := fun τ ζ => HRS.Whole.pair (HRS.Whole.empirical (X τ.toNNReal ζ)) (f τ) -
    HRS.Whole.pair μ (f τ) with hadef
  set I : ℝ → Ω → ℝ := itoIntegral P ℱ W' (s102_Ig f t X) with hIdef
  have ha_int : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (aR τ) P := fun τ hτ =>
    (s102_pairEmp_int hN0 (hXτm τ) (hfm τ hτ) (hBf τ hτ)).sub (integrable_const _)
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf X
  have hΦ : IsProgressiveL2 P ℱ (s102_Ig f t X) :=
    IsProgressiveL2.of_bounded P (s102_Ig_progressive hf hF.progressive) Bg hBg
  have hI_int : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (I τ) P := fun τ _ =>
    (memLp_two_itoIntegral hF.brownian hΦ τ).integrable (by norm_num)
  have hI0 : ∀ τ ∈ Icc (0 : ℝ) t, ∫ ζ, I τ ζ ∂P = 0 := fun τ _ => integral_itoIntegral hF.brownian hΦ τ
  have hid : ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t, aR τ ζ = aR 0 ζ + (Real.sqrt (2 * β⁻¹) / N) * I τ ζ -
      ∫ r in Icc (0 : ℝ) τ, pairEnergy (hK r) (X r.toNNReal ζ) μ := by
    filter_upwards [hdual, hFe] with ζ h1 h2 τ hτ
    obtain ⟨-, h3⟩ := h1 τ hτ
    have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 t := Icc_subset_Icc le_rfl hτ.2
    have h4 : ∫ r in Icc (0 : ℝ) τ, flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) ((fun _ => ρ) r) =
        -∫ r in Icc (0 : ℝ) τ, pairEnergy (hK r) (X r.toNNReal ζ) μ := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Icc fun r hr => h2 r (hsubτ hr)
    have h6 : aR 0 ζ = HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (f 0) - HRS.Whole.pair μ (f 0) := by
      simp only [hadef, Real.toNNReal_zero]
    have h3' : aR τ ζ = (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (f 0) - HRS.Whole.pair μ (f 0)) +
        (Real.sqrt (2 * β⁻¹) / N) * I τ ζ +
        ∫ r in Icc (0 : ℝ) τ, flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) ((fun _ => ρ) r) := h3
    rw [h3', h6, h4]
    ring
  have hcent := s102_centered_identity (c := Real.sqrt (2 * β⁻¹) / N) aR I
    (fun q => pairEnergy (hK q.1) (X q.1.toNNReal q.2) μ) he ha_int hI_int hI0 ht0 hid
  have hsq : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
    have h0 : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN0)
    have h1 : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by positivity)).symm
    rw [inv_mul_eq_iff_eq_mul₀ h0.ne']; exact h1
  filter_upwards [hcent] with ζ hζ τ hτ
  have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 t := Icc_subset_Icc le_rfl hτ.2
  have hint2 : ∫ r in Icc (0 : ℝ) τ, (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r)) =
      -Real.sqrt N * ∫ r in Icc (0 : ℝ) τ, (pairEnergy (hK r) (X r.toNNReal ζ) μ -
        ∫ ζ', pairEnergy (hK r) (X r.toNNReal ζ') μ ∂P) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hr' := hsubτ hr
    simp only [r2QuadField, hKr r hr']
    rw [← mul_assoc]
    congr 1
    rw [neg_mul, hsq]
  have hz := fun τ' (h : τ' ∈ Icc (0 : ℝ) t) =>
    s102_zf_eq hN0 P X τ' (hXτm τ') μ (hfm τ' h) (hBf τ' h) ζ
  show s102_zf P X ζ τ (f τ) = s102_zf P X ζ 0 (f 0) + (Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N)) * I τ ζ +
    ∫ r in Icc (0 : ℝ) τ, (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r))
  rw [hz τ hτ, hz 0 ht0, hint2]
  have := hζ τ hτ
  show Real.sqrt N * (aR τ ζ - ∫ ζ', aR τ ζ' ∂P) = Real.sqrt N * (aR 0 ζ - ∫ ζ', aR 0 ζ' ∂P) + _ + _
  rw [this]
  ring

end HRS.MS.R2Interp

end
