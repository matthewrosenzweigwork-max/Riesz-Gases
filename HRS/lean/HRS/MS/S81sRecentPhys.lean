import HRS.MS.S81sRecent
import HRS.MS.S81sItoShift
import HRS.MS.GenPathAux22
import HRS.MS.WsStatAux10

/-!
# S8.1 (worker S81S): physical identification of the recent current

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

* `s81s_ident_gen`: `s56_ident` (the coordinates of `𝒯M` are the adjoint stochastic convolution) for an ARBITRARY Hilbert-Schmidt feature
  integrand agreeing with `c₀ Γ_{r,a}(X_i(r))` on `[0,T]` (the frozen `finite_noise` integrand is not clamped at `T`).
* `s81s_prop_shift`: time homogeneity `U^{h+r,h+v} φ_α = U^{r,v} φ_α` of the critical propagator on oscillator test functions.
* `s81s_recent_phys`: the coordinates of the recent window `(𝒯M)(b+t)` of the shifted system are the increment `∫_0^{h+b+t} K dW - ∫_0^h K dW`
  of the Duhamel noise integral of the ORIGINAL system, `K = 1_{[0,h+b+t]} √(2/(Nβ)) ∂_a U^{r,h+b+t}φ_α(X_i(r))`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem

namespace HRS.Whole.S81S

variable {d : ℕ}

theorem s81s_ident_gen (C : WholeCoeff d) (m T c0 : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → Fin N × Fin d → KSpace d m T)
    (hΦeq : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (ω : Ω) (k : Fin N × Fin d),
      Φ r ω k = c0 • gradFeature C m T k.2 r (X (Real.toNNReal r) ω k.1))
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' Φ)
    (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (hC : OscAdjointInput C m T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T M ζ t) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then c0 *
          gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := by
  classical
  intro t ht α
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hW' : IsBrownianFiltration P ℱ W := s52_brownian_of_cyl hW
  set u1 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y1 m T t α) with hu1
  set u2 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y2 m T α) with hu2
  have hL1 : IsProgressiveL2 P ℱ u1 := s52_pairL2 hΦ _
  have hL2 : IsProgressiveL2 P ℱ u2 := s52_pairL2 hΦ _
  have hLd : IsProgressiveL2 P ℱ (fun r ω k => u1 r ω k - u2 r ω k) := isProgressiveL2_sub hL1 hL2
  set ud : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => u1 r ω k - u2 r ω k with hud
  -- pointwise values of the pairings
  have hu2val : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω (k : Fin N × Fin d), u2 r ω k =
      c0 * gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1) := by
    intro r hr ω k
    simp only [hu2]
    rw [hΦeq r hr ω k, inner_smul_left, s52_pair_grad_y2 hC hT]
    simp
  have hu1val : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω (k : Fin N × Fin d), u1 r ω k =
      c0 * (if r ≤ t then gradComp k.2 (propagatorW C r t (oscTestFun m α))
        (X (Real.toNNReal r) ω k.1) else gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1)) := by
    intro r hr ω k
    simp only [hu1]
    rw [hΦeq r hr ω k, inner_smul_left, s52_pair_grad_y1 hC ht.2 k.2 hr]
    simp
  -- the pairings with the Itô integrals
  have hp1T := s52_pair_ito hW' hM (s52y1 m T t α)
    (pc_isProgressiveL2_inner hΦ (s52y1 m T t α) Finset.univ) hT
  have hp2T := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) hT
  have hp2t := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) ht.1
  have hsub := itoIntegral_sub hW' hL1 hL2
  -- the integral of the difference stops at `t`
  have hagreeE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω, ud r ω = (fun r ω k => if r ≤ t then ud r ω k else 0) r ω := by
    intro r hr ω
    funext k
    by_cases hrt : r ≤ t
    · simp [hrt]
    · simp only [hrt, if_false, hud, hu2val r hr ω k, hu1val r hr ω k]
      simp
  have hLdt : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then ud r ω k else 0) := by
    have := s52_isProgressiveL2_ite hLd (measurableSet_Iic (a := t))
    simpa using this
  have hlcE := s52_lc hW' hLd hLdt hT hagreeE
  have hkillE := s52_kill hW' hLd ht.1
  -- the target integrand
  set ψ : ℝ → Ω → Fin N × Fin d → ℝ := fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then c0 *
    gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0 with hψ
  have hψeq : ψ = fun r ω k => if r ∈ Set.Icc (0 : ℝ) t then u1 r ω k else 0 := by
    funext r ω k
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t
    · have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      simp only [hψ, hr, if_true, hu1val r hrT ω k, hr.2]
    · simp only [hψ, if_neg hr]
  have hLψ : IsProgressiveL2 P ℱ ψ := by
    rw [hψeq]; exact s52_isProgressiveL2_ite hL1 measurableSet_Icc
  have hagreeG : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, u1 r ω = ψ r ω := by
    intro r hr ω
    rw [hψeq]
    simp [hr]
  have hlcG := s52_lc hW' hL1 hLψ ht.1 hagreeG
  filter_upwards [hp1T, hp2T, hp2t, hsub, hlcE, hkillE, hlcG] with ζ h1 h2 h3 h4 h5 h6 h7
  rw [s52_coord_recon ht.1 ht.2]
  have k0a : inner ℝ (M T ζ) (s52y1 m T t α) = itoIntegral P ℱ W u1 T ζ := h1
  have k0b : inner ℝ (M T ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 T ζ := h2
  have k0c : inner ℝ (M t ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 t ζ := h3
  have k1 : itoIntegral P ℱ W ud T ζ = itoIntegral P ℱ W u1 T ζ - itoIntegral P ℱ W u2 T ζ := h4 T
  have k2 : itoIntegral P ℱ W ud t ζ = itoIntegral P ℱ W u1 t ζ - itoIntegral P ℱ W u2 t ζ := h4 t
  have k3 : itoIntegral P ℱ W ud (min T T) ζ =
      itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) (min T T) ζ := h5 T hT
  have k4 : itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) T ζ =
      itoIntegral P ℱ W ud (min T t) ζ := h6 T hT
  have k5 : itoIntegral P ℱ W u1 (min t t) ζ = itoIntegral P ℱ W ψ (min t t) ζ := h7 t ht.1
  rw [min_self] at k3 k5
  rw [min_eq_right ht.2] at k4
  rw [k0a, k0b, k0c]
  linarith




/-- Time homogeneity of the critical propagator on oscillator test functions. -/
theorem s81s_prop_shift (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (m : ℝ) (α : MultiIndex d) {h r σ : ℝ}
    (hh : 0 ≤ h) (hr : 0 ≤ r) (hrσ : r ≤ σ) :
    propagatorW (critCoeff d a β ρβ) (h + r) (h + σ) (oscTestFun m α) =
      propagatorW (critCoeff d a β ρβ) r σ (oscTestFun m α) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have hρS : IsSchwartzDensity ρβ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  obtain ⟨θ, hθ⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  have O : HRS.MS.Ul.UlOrb d ((d : ℝ) / 2) β⁻¹ ρβ (fun _ => 0) (HRS.MS.S85.s85c ((d : ℝ) / 2) ρβ) θ :=
    ⟨hd, hs0, hsd, hν, hρS.2, HRS.MS.S85.s85_sigma d, rfl, hθ⟩
  set K : ℕ := ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hKdef
  have hK : (4 : ℝ) + (d : ℝ) / 2 < K := by
    rw [hKdef]; push_cast; exact Nat.lt_floor_add_one _
  obtain ⟨f, hf, -⟩ := HRS.MS.S52B.s52b_phi (d := d) m α
  have hφ0 : HRS.Whole.UlClosure K θ (oscTestFun m α) := by
    have := HRS.MS.Ul.ul6_closure O (a • (1 : Matrix (Fin d) (Fin d) ℝ)) f 0 K
    rw [← hf]; exact this
  rw [critCoeff, HRS.MS.S21.s21_dyn_eq, HRS.MS.S85.s85_coeff_fv (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ ρβ]
  have e1 := HRS.MS.S21.s21_shift hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hρS (h + σ)
    (by linarith) hθ hK hφ0 (h + r) (h + σ) (by linarith) (by linarith) le_rfl
  have e2 := HRS.MS.S21.s21_shift hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hρS (h + σ)
    (by linarith) hθ hK hφ0 r σ hr hrσ (by linarith)
  rw [e1, e2]
  congr 1
  ring

theorem s81s_brownian_of_cyl {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {κ : Type*} [Fintype κ] [DecidableEq κ] {B : ℝ≥0 → Ω → κ → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) : IsBrownianFiltration P ℱ B :=
  HRS.GF.gfb3_isBrownianFiltration_restrict (ι := ↥(Finset.univ : Finset κ)) (ι' := κ)
    (fun k => (⟨k, Finset.mem_univ k⟩ : ↥(Finset.univ : Finset κ)))
    (fun x y hxy => by simpa using hxy) (hB Finset.univ)

/-- **Identification of the recent current.** -/
theorem s81s_recent_phys (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T b : ℝ) (hT : 0 < T) (hb : 0 ≤ b) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {N : ℕ} (hN : 2 ≤ N)
    {Ω₁ : Type} [mΩ₁ : MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
    (W : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X : ℝ≥0 → Ω₁ → EucConfig d N)
    (ℱ₁ : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ)
    (hWc : IsCylindricalBrownian Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2))
    (hF : IsWholeFilteredSolution Q₁ ℱ₁ W'' W X) (h : ℝ≥0)
    (M : ℝ → Ω₁ → KSpace d m (b + T))
    (hHS : ∀ τ : ℝ, IsHSIntegrand Q₁ (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h) τ
      (s81s_Phi d N a β ρβ m (b + T) (HRS.Whole.S79.s79p_shiftX h X)))
    (hM : IsHilbertItoIntegral Q₁ (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
      (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW h W t z ia.1 ia.2)
      (s81s_Phi d N a β ρβ m (b + T) (HRS.Whole.S79.s79p_shiftX h X)) M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂Q₁,
      OscDual.coord (reconstructPath m (b + T) M ζ (b + t)) α =
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2)
          (fun r z (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (h + (b + t)) then
            Real.sqrt (2 / (N * β)) * gradComp ia.2
              (propagatorW (critCoeff d a β ρβ) r (h + (b + t)) (oscTestFun m α))
              (X (Real.toNNReal r) z ia.1) else 0) (h + (b + t)) ζ -
        itoIntegral Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2)
          (fun r z (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (h + (b + t)) then
            Real.sqrt (2 / (N * β)) * gradComp ia.2
              (propagatorW (critCoeff d a β ρβ) r (h + (b + t)) (oscTestFun m α))
              (X (Real.toNNReal r) z ia.1) else 0) h ζ := by
  classical
  intro t ht α
  have hN1 : 1 ≤ N := by omega
  have hL1 : 0 < b + T := by linarith
  have ht1 : b + t ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht2 : h + (b + t) ∈ Set.Icc (0 : ℝ) (h + (b + T)) :=
    ⟨by linarith [ht1.1, h.coe_nonneg], by linarith [ht1.2]⟩
  have hL2 : 0 < (h : ℝ) + (b + T) := by linarith [h.coe_nonneg]
  obtain ⟨θ1, Λ1, K1, C1, S1, hbv1, -, -, -, hScoeff1, -, hSadj1⟩ := s81s_setup hd ha hβ hρβ hm hL1
  obtain ⟨θ2, Λ2, K2, C2, S2, hbv2, -, -, -, hScoeff2, -, hSadj2⟩ := s81s_setup hd ha hβ hρβ hm hL2
  set c0 : ℝ := Real.sqrt (2 / (N * β)) with hc0
  -- shifted system
  have hFh := HRS.Whole.BreakdownS81.s81b_filtered_shift hF h
  have hWh := s81s_cyl_shift_vec hWc h
  have hC1 : OscAdjointInput (critCoeff d a β ρβ) m (b + T) := by
    rw [← hScoeff1 N]; exact hSadj1 N
  have hid := s81s_ident_gen (critCoeff d a β ρβ) m (b + T) c0 N Q₁
    (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
    (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW h W t z ia.1 ia.2)
    (HRS.Whole.S79.s79p_shiftX h X) M hN1 hWh
    (s81s_Phi d N a β ρβ m (b + T) (HRS.Whole.S79.s79p_shiftX h X))
    (fun r hr ω k => by
      simp only [s81s_Phi, max_eq_left hr.1, hc0])
    hHS hM hC1 (b + t) ht1 α
  have eW : (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW h W t z ia.1 ia.2) =
      HRS.MD.EQLawPath.shiftProc (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) h := by
    funext t z ia
    simp [HRS.Whole.S79.s79p_shiftW, HRS.MD.EQLawPath.shiftProc]
  rw [eW] at hid
  have hWb : IsBrownianFiltration Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) :=
    s81s_brownian_of_cyl hWc
  -- the kernels
  set Kh : ℝ → Ω₁ → (Fin N × Fin d) → ℝ := fun r ζ' ia =>
    if r ∈ Set.Icc (0 : ℝ) (b + t) then c0 * gradComp ia.2
      (propagatorW (critCoeff d a β ρβ) r (b + t) (oscTestFun m α))
      (HRS.Whole.S79.s79p_shiftX h X (Real.toNNReal r) ζ' ia.1) else 0 with hKh
  set K : ℝ → Ω₁ → (Fin N × Fin d) → ℝ := fun r z ia =>
    if r ∈ Set.Icc (0 : ℝ) (h + (b + t)) then c0 * gradComp ia.2
      (propagatorW (critCoeff d a β ρβ) r (h + (b + t)) (oscTestFun m α))
      (X (Real.toNNReal r) z ia.1) else 0 with hK
  have hcl1 := s56_osc_classical (s81s_bounds d a β m (b + T) θ1 Λ1 K1 C1) hbv1 S1 N ht1 α
  have hcl2 := s56_osc_classical (s81s_bounds d a β m (h + (b + T)) θ2 Λ2 K2 C2) hbv2 S2 N ht2 α
  have hcl1' : IsClassicalAdjointW (critCoeff d a β ρβ) (b + t) (oscTestFun m α)
      (fun r => propagatorW (critCoeff d a β ρβ) r (b + t) (oscTestFun m α)) := by
    rw [← hScoeff1 N]; exact hcl1
  have hcl2' : IsClassicalAdjointW (critCoeff d a β ρβ) (h + (b + t)) (oscTestFun m α)
      (fun r => propagatorW (critCoeff d a β ρβ) r (h + (b + t)) (oscTestFun m α)) := by
    rw [← hScoeff2 N]; exact hcl2
  have hprog1 := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := Q₁) ht1.1 hcl1'.isC12TestRd
    hFh.progressive
  have hprog2 := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := Q₁) ht2.1 hcl2'.isC12TestRd
    hF.progressive
  have hKh_prog : IsProgressiveL2 Q₁ (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h) Kh := by
    have e : Kh = fun s z => c0 • HRS.MH.DualityRd.truncGradIntegrand (b + t)
        (fun r => propagatorW (critCoeff d a β ρβ) r (b + t) (oscTestFun m α))
        (HRS.Whole.S79.s79p_shiftX h X) s z := by
      funext r z ia
      by_cases hr : r ∈ Set.Icc (0 : ℝ) (b + t)
      · simp only [hKh, HRS.MH.DualityRd.truncGradIntegrand, if_pos hr, Pi.smul_apply, smul_eq_mul]
      · simp only [hKh, HRS.MH.DualityRd.truncGradIntegrand, if_neg hr, Pi.smul_apply, smul_eq_mul, mul_zero]
    rw [e]; exact hprog1.smul c0
  have hK_prog : IsProgressiveL2 Q₁ ℱ₁ K := by
    have e : K = fun s z => c0 • HRS.MH.DualityRd.truncGradIntegrand (h + (b + t))
        (fun r => propagatorW (critCoeff d a β ρβ) r (h + (b + t)) (oscTestFun m α)) X s z := by
      funext r z ia
      by_cases hr : r ∈ Set.Icc (0 : ℝ) (h + (b + t))
      · simp only [hK, HRS.MH.DualityRd.truncGradIntegrand, if_pos hr, Pi.smul_apply, smul_eq_mul]
      · simp only [hK, HRS.MH.DualityRd.truncGradIntegrand, if_neg hr, Pi.smul_apply, smul_eq_mul, mul_zero]
    rw [e]; exact hprog2.smul c0
  have hrel : ∀ r : ℝ, 0 < r → ∀ (ω : Ω₁) (k : Fin N × Fin d), Kh r ω k = K (h + r) ω k := by
    intro r hr ω k
    by_cases hcond : r ∈ Set.Icc (0 : ℝ) (b + t)
    · have hcond' : (h : ℝ) + r ∈ Set.Icc (0 : ℝ) (h + (b + t)) :=
        ⟨by linarith [h.coe_nonneg], by linarith [hcond.2]⟩
      simp only [hKh, hK, if_pos hcond, if_pos hcond']
      rw [s81s_prop_shift hd ha hβ hρβ m α h.coe_nonneg hcond.1 hcond.2]
      have : HRS.Whole.S79.s79p_shiftX h X (Real.toNNReal r) ω = X (Real.toNNReal ((h : ℝ) + r)) ω := by
        simp only [HRS.Whole.S79.s79p_shiftX]
        rw [Real.toNNReal_add h.coe_nonneg hr.le, Real.toNNReal_coe]
      rw [this]
    · have hn : (h : ℝ) + r ∉ Set.Icc (0 : ℝ) (h + (b + t)) := fun hh => hcond ⟨hr.le, by linarith [hh.2]⟩
      simp only [hKh, hK, if_neg hcond, if_neg hn]
  have hshift := s81s_ito_shift hWb h hK_prog hKh_prog hrel
  filter_upwards [hid, hshift] with ζ h1 h2
  rw [h1]
  exact h2 (b + t) ht1.1

end HRS.Whole.S81S
