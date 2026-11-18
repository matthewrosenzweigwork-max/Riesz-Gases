import HRS.MC.S7E3aAux2
import HRS.MC.S7E1Aux1

/-!
# Packets `s7_E3a/b`, file 3: the tail of `1 - C` along the basis

With `C_ij = <u_i, R u_j>`, `R = (I + beta T)^{-1}`, `T = K P` compact in the sense of file 2:
for every `eta > 0` there is `N` such that for all `x` supported in `[N, L)`,
`x.x - x.C.x <= eta x.x`.  (`1 - C = beta R T` on the span of `u_i`, `i >= N`.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.MC.Sec7.E3Aux3

open HRS HRS.Sec7 HRS.StaticLimitAux HRS.MC.Sec7.E3Aux1 HRS.MC.Sec7.E3Aux2

variable {d : ℕ} {ρ : Torus d → ℝ}

theorem e3_kop_le [IsProbabilityMeasure (withDensityReal ρ)] {g f : Torus d → ℝ}
    (hP : MemLp (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ)) :
    eLpNorm (Kop g (withDensityReal ρ) f) 2 (withDensityReal ρ) ≤
      2 * eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) := by
  have hPi : Integrable (PDE.MFLinear.Phi g ρ f) (withDensityReal ρ) := hP.integrable one_le_two
  set c := pair (withDensityReal ρ) (PDE.MFLinear.Phi g ρ f) with hc
  have hcle : ‖c‖ₑ ≤ eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) := by
    calc ‖c‖ₑ ≤ ∫⁻ x, ‖PDE.MFLinear.Phi g ρ f x‖ₑ ∂(withDensityReal ρ) :=
          enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (PDE.MFLinear.Phi g ρ f) 1 (withDensityReal ρ) :=
          (eLpNorm_one_eq_lintegral_enorm hPi.aestronglyMeasurable).symm
      _ ≤ eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) :=
          eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hconst : eLpNorm (fun _ : Torus d => c) 2 (withDensityReal ρ) = ‖c‖ₑ := by
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne _)]
    simp
  have hK : Kop g (withDensityReal ρ) f = fun x => PDE.MFLinear.Phi g ρ f x - c :=
    PDE.MFLinear.kop_eq_Phi g ρ f
  rw [hK]
  have hsub : eLpNorm (fun x => PDE.MFLinear.Phi g ρ f x - c) 2 (withDensityReal ρ) ≤
      eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) + ‖c‖ₑ := by
    have := eLpNorm_sub_le (μ := withDensityReal ρ) (p := 2) (f := PDE.MFLinear.Phi g ρ f)
      (g := fun _ => c) (by norm_num)
    rw [hconst] at this
    exact this
  calc _ ≤ eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) + ‖c‖ₑ := hsub
    _ ≤ eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) +
        eLpNorm (PDE.MFLinear.Phi g ρ f) 2 (withDensityReal ρ) := add_le_add_right hcle _
    _ = _ := by rw [two_mul]


theorem e3_cov_tail (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ (L : ℕ) (x : Fin L → ℝ), (∀ i : Fin L, (i : ℕ) < N → x i = 0) →
      x ⬝ᵥ x - x ⬝ᵥ ((Matrix.of fun i j : Fin L =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) *ᵥ x) ≤
        η * (x ⬝ᵥ x) := by
  have hd1 : 1 ≤ d := by omega
  have hρc : Continuous ρ := continuous_of_smooth hρ.smooth
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have H : PDE.MFLinear.KS (periodicRiesz d s) ρ Λ :=
    ⟨PDE.MFOneLe.integrable_periodicRiesz hd1 s hs0 hsd, fun x => periodicRiesz_neg x, hρ.density,
      fun x => (le_abs_self _).trans (hΛ x (Set.mem_univ x))⟩
  have hP : IsProbabilityMeasure (withDensityReal ρ) := H.isProb
  obtain ⟨R, hRl, hRr, hRsym, hRpos⟩ := PDE.MFLinear.exists_inverse hd1 s hs0 hsd H hρc β hβ.le
  have hTs := PDE.MFLinear.TLp_symm hd1 s hs0 hsd H hρc
  have hRr' : ∀ y, R y + β • PDE.MFLinear.TLp H (R y) = y := fun y => hRr y
  -- the Gram form of the covariance
  have hGram : ∀ {φ ψ : Torus d → ℝ} (hφ : MemLp φ 2 (withDensityReal ρ))
      (hψ : MemLp ψ 2 (withDensityReal ρ)),
      ∫ x, φ x ∂(withDensityReal ρ) = 0 → ∫ x, ψ x ∂(withDensityReal ρ) = 0 →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ ψ =
        ⟪hφ.toLp φ, R (hψ.toLp ψ)⟫ := by
    intro φ ψ hφ hψ hφ0 hψ0
    have hy1 : ⇑(hφ.toLp φ) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) φ := by
      have : projMean (withDensityReal ρ) φ = φ := PDE.MFLinear.projMean_of_pair_zero hφ0
      rw [this]; exact MemLp.coeFn_toLp hφ
    have hy2 : ⇑(hψ.toLp ψ) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) ψ := by
      have : projMean (withDensityReal ρ) ψ = ψ := PDE.MFLinear.projMean_of_pair_zero hψ0
      rw [this]; exact MemLp.coeFn_toLp hψ
    have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ ⇑(R (hψ.toLp ψ)) :=
      PDE.MFLinear.isResponse_of_A H β ψ _ (by rw [hRr]; exact hy2)
    have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨_, hresp⟩
    obtain ⟨h0, -, huniq⟩ := PDE.MFLinear.exists_unique_response_of_one_le hd1 s hs0 hsd ρ hρ.density
      hρc β hβ.le ψ hψ
    have hch : responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ =ᵐ[withDensityReal ρ]
        ⇑(R (hψ.toLp ψ)) := by
      unfold responseInverse
      simp only [hex, dite_true]
      exact (huniq _ hex.choose_spec).trans (huniq _ hresp).symm
    unfold susceptibilityCov
    rw [PDE.MFLinear.innerLp_eq_l2Inner]
    exact (PDE.MFLinear.l2Inner_congr_ae (Filter.EventuallyEq.refl _ _) hch).trans
      (PDE.MFLinear.l2Inner_congr_ae hy1.symm (Filter.EventuallyEq.refl _ _))
  set u : ℕ → Lp ℝ 2 (withDensityReal ρ) := fun i => (he.memLp i).toLp (e i) with hu_def
  have hu : Orthonormal ℝ u := e3_orthonormal he
  have hCu : ∀ i j, susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j) =
      ⟪u i, R (u j)⟫ := fun i j =>
    hGram (he.memLp i) (he.memLp j) (he.centered i) (he.centered j)
  set η₀ : ℝ := η / (2 * β * (‖R‖ + 1)) with hη₀def
  have hRn := norm_nonneg R
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨N, hN⟩ := e3_kt he H hη₀
  refine ⟨N, fun L x hx => ?_⟩
  set w : Lp ℝ 2 (withDensityReal ρ) := ∑ i : Fin L, x i • u i with hw
  have hwn : ‖w‖ ^ 2 = x ⬝ᵥ x := E1Aux1.e1a_norm_sum hu L x
  have hq : x ⬝ᵥ ((Matrix.of fun i j : Fin L =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) *ᵥ x) = ⟪R w, w⟫ := by
    have key := E0a.s7e_quad u R hRsym L x
    simp only [← hCu, star_trivial] at key
    exact key
  have hwR : w - R w = β • PDE.MFLinear.TLp H (R w) := by
    have h := hRr' w
    calc w - R w = (R w + β • PDE.MFLinear.TLp H (R w)) - R w := by rw [h]
      _ = _ := by abel
  have e1 : ‖w‖ ^ 2 - ⟪R w, w⟫ = β * ⟪R w, PDE.MFLinear.TLp H w⟫ := by
    have : ‖w‖ ^ 2 - ⟪R w, w⟫ = ⟪w - R w, w⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    rw [this, hwR, real_inner_smul_left, hTs (R w) w]
  have e2 : ⟪R w, PDE.MFLinear.TLp H w⟫ ≤ ‖R‖ * ‖w‖ * ‖PDE.MFLinear.TLp H w‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (R.le_opNorm w) (norm_nonneg _))
  -- the smallness of `T w`
  have e3 : ‖PDE.MFLinear.TLp H w‖ ≤ 2 * η₀ * ‖w‖ := by
    set x' : ℕ → ℝ := fun n => if h : n < L then x ⟨n, h⟩ else 0 with hx'
    have hx'N : ∀ i, i < N → x' i = 0 := by
      intro i hi
      simp only [hx']
      split_ifs with h
      · exact hx ⟨i, h⟩ hi
      · rfl
    have hx'fin : ∀ i : Fin L, x' (i : ℕ) = x i := by intro i; simp [hx']
    set wf : Torus d → ℝ := fun y => ∑ i ∈ Finset.range L, x' i * e i y with hwf
    have hwa : ⇑w =ᵐ[(withDensityReal ρ)] wf := by
      have h1 := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin L)) (fun i => x i • u i)
      have h2 : ∀ᵐ y ∂(withDensityReal ρ), ∀ i : Fin L,
          ((x i • u i : Lp ℝ 2 (withDensityReal ρ)) : Torus d → ℝ) y = x i * e i y := by
        rw [ae_all_iff]
        intro i
        filter_upwards [Lp.coeFn_smul (x i) (u i), MemLp.coeFn_toLp (he.memLp i)] with y hy1 hy2
        rw [hy1]
        simp only [Pi.smul_apply, smul_eq_mul]
        simp only [hu_def]
        rw [hy2]
      filter_upwards [h1, h2] with y hy1 hy2
      rw [hw, hy1]
      simp only [hwf]
      rw [← Fin.sum_univ_eq_sum_range (fun n => x' n * e n y) L]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy2 i, hx'fin i]
    have hwfm : MemLp wf 2 (withDensityReal ρ) := by
      have := memLp_finsetSum' (Finset.range L) (fun i _ => (he.memLp i).const_mul (x' i))
      refine this.ae_eq (Filter.Eventually.of_forall fun y => ?_)
      simp [hwf]
    have hpair : pair (withDensityReal ρ) ⇑w = 0 := by
      unfold pair
      rw [integral_congr_ae hwa]
      simp only [hwf]
      rw [integral_finsetSum _ (fun i _ => ((he.memLp i).integrable one_le_two).const_mul _)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, he.centered i, mul_zero]
    have hproj : projMean (withDensityReal ρ) ⇑w = ⇑w := by
      funext y; simp [projMean, hpair]
    have hTc := PDE.MFLinear.TLp_coe H w
    have hPhi : PDE.MFLinear.Phi (periodicRiesz d s) ρ (projMean (withDensityReal ρ) ⇑w) =
        PDE.MFLinear.Phi (periodicRiesz d s) ρ wf := by
      rw [hproj]; exact PDE.MFLinear.Phi_congr hwa
    have hPm : MemLp (PDE.MFLinear.Phi (periodicRiesz d s) ρ wf) 2 (withDensityReal ρ) :=
      (PDE.MFLinear.memLp_Phi H hwfm).1
    set X2 := ∑ i ∈ Finset.range L, x' i ^ 2 with hX2
    have hX2e : X2 = x ⬝ᵥ x := by
      simp only [hX2, dotProduct]
      rw [← Fin.sum_univ_eq_sum_range (fun n => x' n ^ 2) L]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx'fin i, sq]
    have hsq : Real.sqrt X2 = ‖w‖ := by
      rw [hX2e, ← hwn, Real.sqrt_sq (norm_nonneg _)]
    have hnorm : eLpNorm (⇑(PDE.MFLinear.TLp H w)) 2 (withDensityReal ρ) ≤
        2 * ENNReal.ofReal (η₀ * Real.sqrt X2) := by
      calc _ = eLpNorm (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑w)) 2 (withDensityReal ρ) := eLpNorm_congr_ae hTc
        _ ≤ 2 * eLpNorm (PDE.MFLinear.Phi (periodicRiesz d s) ρ (projMean (withDensityReal ρ) ⇑w)) 2 (withDensityReal ρ) :=
            e3_kop_le (by rw [hPhi]; exact hPm)
        _ = 2 * eLpNorm (PDE.MFLinear.Phi (periodicRiesz d s) ρ wf) 2 (withDensityReal ρ) := by rw [hPhi]
        _ ≤ _ := mul_le_mul_right (hN L x' hx'N) _
    rw [Lp.norm_def]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hnorm
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hsq] at this
    simpa [mul_assoc] using this
  have hfin : x ⬝ᵥ x - x ⬝ᵥ ((Matrix.of fun i j : Fin L =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) *ᵥ x) =
      β * ⟪R w, PDE.MFLinear.TLp H w⟫ := by
    rw [hq, ← hwn, e1]
  rw [hfin, ← hwn]
  have hwnn := norm_nonneg w
  calc β * ⟪R w, PDE.MFLinear.TLp H w⟫ ≤ β * (‖R‖ * ‖w‖ * ‖PDE.MFLinear.TLp H w‖) :=
        mul_le_mul_of_nonneg_left e2 hβ.le
    _ ≤ β * (‖R‖ * ‖w‖ * (2 * η₀ * ‖w‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hβ.le
        exact mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = (η * (‖R‖ / (‖R‖ + 1))) * ‖w‖ ^ 2 := by
        rw [hη₀def]; field_simp
    _ ≤ η * ‖w‖ ^ 2 := by
        have : ‖R‖ / (‖R‖ + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith [sq_nonneg ‖w‖, mul_le_mul_of_nonneg_left this hη.le]

end HRS.MC.Sec7.E3Aux3

end
