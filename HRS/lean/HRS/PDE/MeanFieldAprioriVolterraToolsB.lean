import HRS.PDE.MeanFieldAprioriVolterraTools

/-!
# (I3, amended) AP5c1B: time-local versions of the Volterra tools (package MF-01)

* `mild_eq_Icc`: the modewise Duhamel formula for a path that solves the integrated equation only
  on `[0,T]` (unbundled hypotheses `hcont`, `heq`);
* `singular_gronwall_Ioc`, `gronwall_Ioc`: the singular Gronwall inequality with conclusion at
  every `t ∈ (0,1]`, by the rescaling `ψ_s(u) := ψ(s u)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Rescaling for the Gronwall inequalities -/

theorem integral_rescale_aux (γ : ℝ) (ψ : ℝ → ℝ) {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    ∫ r in (0 : ℝ)..s * u, (s * u - r) ^ (-γ) * ψ r =
      s ^ (1 - γ) * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := u)
    (fun r => (s * u - r) ^ (-γ) * ψ r) s
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h]
  have h2 : ∫ r in (0 : ℝ)..u, (s * u - s * r) ^ (-γ) * ψ (s * r) =
      s ^ (-γ) * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hu] at hr
    have : s * u - s * r = s * (u - r) := by ring
    simp only [this]
    rw [Real.mul_rpow hs.le (by linarith [hr.2]), mul_assoc]
  rw [h2, ← mul_assoc, show s ^ (1 - γ) = s * s ^ (-γ) by
    rw [sub_eq_add_neg, Real.rpow_add hs, Real.rpow_one]]

theorem rescale_step (γ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C) (ψ E : ℝ → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hψ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (hE : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ψ t ≤ E t + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) :
    ∀ u ∈ Set.Ioc (0 : ℝ) 1, ψ (s * u) ≤ E (s * u) +
      C * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
  intro u hu
  have hsu : s * u ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨mul_pos hs0 hu.1, by nlinarith [hu.1, hu.2]⟩
  have h1 := hE _ hsu
  rw [integral_rescale_aux γ ψ hs0 hu.1.le] at h1
  have hI : 0 ≤ ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
    refine intervalIntegral.integral_nonneg hu.1.le fun r hr => ?_
    refine mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (hψ _ ⟨by nlinarith [hr.1], ?_⟩)
    nlinarith [hr.1, hr.2, hu.2]
  have hs' : s ^ (1 - γ) ≤ 1 := Real.rpow_le_one hs0.le hs1 (by linarith)
  have : C * (s ^ (1 - γ) * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r)) ≤
      C * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
    refine mul_le_mul_of_nonneg_left ?_ hC
    nlinarith
  linarith

/-- Singular Gronwall, conclusion at every `t ∈ (0,1]`. -/
theorem singular_gronwall_Ioc (γ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ψ : ℝ → ℝ) (A B : ℝ), 0 ≤ A → ContinuousOn ψ (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc 0 1, 0 ≤ ψ t ∧ ψ t ≤ B) →
      (∀ t ∈ Set.Ioc 0 1, ψ t ≤ A * t ^ (-(1 / 2 : ℝ)) +
        C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) →
      ∀ t ∈ Set.Ioc 0 1, ψ t ≤ C' * A * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C', hC'0, hC'⟩ := singular_gronwall γ C hγ0 hγ1 hC
  refine ⟨C', hC'0, fun ψ A B hA hψc hψB hψ t ht => ?_⟩
  have hts : (0 : ℝ) < t := ht.1
  have hψnn : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ u := fun u hu => (hψB u hu).1
  have hmaps : ∀ u ∈ Set.Icc (0 : ℝ) 1, t * u ∈ Set.Icc (0 : ℝ) 1 := fun u hu =>
    ⟨mul_nonneg hts.le hu.1, by nlinarith [hu.1, hu.2, ht.2]⟩
  have hpos : (0 : ℝ) ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hts.le _
  have key := rescale_step γ C hγ0 hγ1 hC ψ (fun r => A * r ^ (-(1 / 2 : ℝ))) hts ht.2 hψnn hψ
  have := hC' (fun u => ψ (t * u)) (A * t ^ (-(1 / 2 : ℝ))) B (mul_nonneg hA hpos)
    (hψc.comp (continuousOn_const.mul continuousOn_id) hmaps)
    (fun u hu => hψB _ (hmaps u hu)) (fun u hu => by
      have h := key u hu
      rw [Real.mul_rpow hts.le hu.1.le] at h
      linarith [h, show A * (t ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ))) =
        A * t ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) by ring])
  simp only [mul_one] at this
  calc ψ t ≤ C' * (A * t ^ (-(1 / 2 : ℝ))) := this
    _ = C' * A * t ^ (-(1 / 2 : ℝ)) := by ring

/-- Gronwall with non-singular data term, conclusion at every `t ∈ (0,1]`. -/
theorem gronwall_Ioc (γ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ψ : ℝ → ℝ) (A B : ℝ), 0 ≤ A → ContinuousOn ψ (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc 0 1, 0 ≤ ψ t ∧ ψ t ≤ B) →
      (∀ t ∈ Set.Ioc 0 1, ψ t ≤ A + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) →
      ∀ t ∈ Set.Ioc 0 1, ψ t ≤ C' * A := by
  obtain ⟨C', hC'0, hC'⟩ := singular_gronwall γ C hγ0 hγ1 hC
  refine ⟨C', hC'0, fun ψ A B hA hψc hψB hψ t ht => ?_⟩
  have hts : (0 : ℝ) < t := ht.1
  have hψnn : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ u := fun u hu => (hψB u hu).1
  have hmaps : ∀ u ∈ Set.Icc (0 : ℝ) 1, t * u ∈ Set.Icc (0 : ℝ) 1 := fun u hu =>
    ⟨mul_nonneg hts.le hu.1, by nlinarith [hu.1, hu.2, ht.2]⟩
  have key := rescale_step γ C hγ0 hγ1 hC ψ (fun _ => A) hts ht.2 hψnn hψ
  have := hC' (fun u => ψ (t * u)) A B hA
    (hψc.comp (continuousOn_const.mul continuousOn_id) hmaps)
    (fun u hu => hψB _ (hmaps u hu)) (fun u hu => by
      have h := key u hu
      have h1 : (1 : ℝ) ≤ u ^ (-(1 / 2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu.2 (by norm_num)
      nlinarith [h, h1, hA])
  simpa using this

/-! ### The modewise Duhamel formula on `[0,T]` -/

open Aux in
/-- `rhs_continuousInHsOn` for an arbitrary time set (the proof uses only `ContinuousInHsOn K ρc S`). -/
theorem rhs_continuousInHsOn_vt (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (S : Set ℝ) (hcont : ContinuousInHsOn K ρc S) :
    ContinuousInHsOn ((K : ℝ) - 2) (fun σ => mfRhsCoeff d s V ν (ρc σ)) S := by
  have hVK := memHs_of_isCk_nat K V hV
  obtain ⟨Cb, hCb0, hCb⟩ := exists_rhs_bound hd s hs0 hsd K hK V hVK ν
  refine ⟨fun τ hτ => (hCb _ (hcont.1 τ hτ)).1, fun τ0 hτ0 => ?_⟩
  set R : ℝ := hsNorm K (ρc τ0) + 1 with hR
  obtain ⟨C, hC0, hC⟩ := exists_rhs_lipschitz hd s hs0 hsd K hK V hVK ν R
  have hT := hcont.2 τ0 hτ0
  have hev : ∀ᶠ τ in 𝓝[S] τ0, hsNorm K (ρc τ - ρc τ0) < 1 :=
    hT.eventually (gt_mem_nhds one_pos)
  have hmem : ∀ᶠ τ in 𝓝[S] τ0, τ ∈ S := self_mem_nhdsWithin
  have hbound : ∀ᶠ τ in 𝓝[S] τ0, hsNorm (K - 2 : ℝ) (mfRhsCoeff d s V ν (ρc τ) -
      mfRhsCoeff d s V ν (ρc τ0)) ≤ C * hsNorm K (ρc τ - ρc τ0) := by
    filter_upwards [hev, hmem] with τ hτ hτm
    have h1 := hsNorm_le_add_sub K (hcont.1 τ hτm) (hcont.1 τ0 hτ0)
    exact (hC _ _ (hcont.1 τ hτm) (hcont.1 τ0 hτ0) (by rw [hR]; linarith)
      (by rw [hR]; linarith)).2
  have hlim : Tendsto (fun τ => C * hsNorm K (ρc τ - ρc τ0)) (𝓝[S] τ0) (𝓝 0) := by
    simpa using hT.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun τ => hsNorm_nonneg _ _) hbound hlim

/-- Modewise Duhamel formula on `[0,T]`, unbundled (no dependency on `MFSolOn`). -/
theorem mild_eq_Icc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) (T : ℝ) (hcont : ContinuousInHsOn K ρc (Set.Icc 0 T))
    (heq : ∀ k, ∀ t ∈ Set.Icc 0 T,
      ρc t k = ρc 0 k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k)
    (k : Lattice d) {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) (hvt : v + t ≤ T) :
    ρc (v + t) k = (heatMult (ν * t) k : ℂ) * ρc v k +
      ∫ σ in (0 : ℝ)..t, (heatMult (ν * (t - σ)) k : ℂ) *
        (mfRhsCoeff d s V ν (ρc (v + σ)) k - (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k) := by
  set L : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hL
  set c : ℝ := ν * L with hc
  have hR : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Icc 0 T) :=
    Aux.continuousOn_mode (rhs_continuousInHsOn_vt hd s hs0 hsd K hK V hV ν ρc _ hcont) k
  have hy : ContinuousOn (fun σ => ρc σ k) (Set.Icc 0 T) := Aux.continuousOn_mode hcont k
  have hshift : ∀ σ ∈ Set.Icc (0 : ℝ) t, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hRs : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k) (Set.Icc 0 t) :=
    hR.comp (continuous_const.add continuous_id).continuousOn hshift
  have hys : ContinuousOn (fun σ => ρc (v + σ) k) (Set.Icc 0 t) :=
    hy.comp (continuous_const.add continuous_id).continuousOn hshift
  -- derivative of a mode on `(0,T)`
  have hderiv : ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun τ' => ρc τ' k) (mfRhsCoeff d s V ν (ρc τ) k) τ := by
    intro τ hτ
    have hco : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Ioo 0 T) :=
      hR.mono Set.Ioo_subset_Icc_self
    have hat : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := Ioo_mem_nhds hτ.1 hτ.2
    have hint : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume 0 τ := by
      refine (hR.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hτ.1.le]
      exact Set.Icc_subset_Icc le_rfl hτ.2.le
    have h1 := intervalIntegral.integral_hasDerivAt_right hint
      (hco.stronglyMeasurableAtFilter isOpen_Ioo τ hτ) (hco.continuousAt hat)
    have h2 := h1.const_add (ρc 0 k)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hat] with τ' hτ'
    exact heq k τ' ⟨hτ'.1.le, hτ'.2.le⟩
  -- the forcing
  set F : ℝ → ℂ := fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k -
    (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k with hF
  have hlap : ∀ w : ℝ, (ν : ℂ) * laplaceCoeff (ρc w) k = -((c : ℝ) : ℂ) * ρc w k := by
    intro w
    simp only [laplaceCoeff, hc, hL]
    push_cast; ring
  have hFeq : ∀ σ, F σ = mfRhsCoeff d s V ν (ρc (v + σ)) k + ((c : ℝ) : ℂ) * ρc (v + σ) k := by
    intro σ; simp only [hF, hlap]; ring
  have hFc : ContinuousOn F (Set.Icc 0 t) := by
    have : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k +
        ((c : ℝ) : ℂ) * ρc (v + σ) k) (Set.Icc 0 t) := hRs.add (continuousOn_const.mul hys)
    exact this.congr (fun σ _ => hFeq σ)
  -- the weighted solution
  set z : ℝ → ℂ := fun τ => ((Real.exp (c * τ) : ℝ) : ℂ) * ρc (v + τ) k with hz
  have hexpc : Continuous (fun τ : ℝ => ((Real.exp (c * τ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hzc : ContinuousOn z (Set.Icc 0 t) := hexpc.continuousOn.mul hys
  have hzd : ∀ τ ∈ Set.Ioo 0 t, HasDerivAt z (((Real.exp (c * τ) : ℝ) : ℂ) * F τ) τ := by
    intro τ hτ
    have hτ0 : v + τ ∈ Set.Ioo (0 : ℝ) T := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have h1 : HasDerivAt (fun τ' => ρc (v + τ') k) (mfRhsCoeff d s V ν (ρc (v + τ)) k) τ :=
      (hderiv _ hτ0).comp_const_add v τ
    have h2 : HasDerivAt (fun τ' : ℝ => ((Real.exp (c * τ') : ℝ) : ℂ))
        (((c * Real.exp (c * τ) : ℝ) : ℂ)) τ := by
      have h3 : HasDerivAt (fun y : ℝ => c * y) c τ := by
        simpa using (hasDerivAt_id τ).const_mul c
      exact (h3.exp.congr_deriv (by ring)).ofReal_comp
    refine (h2.mul h1).congr_deriv ?_
    rw [hFeq]; push_cast; ring
  have hFI : IntervalIntegrable (fun σ => ((Real.exp (c * σ) : ℝ) : ℂ) * F σ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht]
    exact hexpc.continuousOn.mul hFc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hzc hzd hFI
  have hz0 : z 0 = ρc v k := by simp [hz]
  have hzt : z t = ((Real.exp (c * t) : ℝ) : ℂ) * ρc (v + t) k := rfl
  rw [hz0, hzt] at hftc
  -- conclusion
  have hheat : ∀ τ : ℝ, (heatMult (ν * τ) k : ℂ) = ((Real.exp (-(c * τ)) : ℝ) : ℂ) := by
    intro τ
    simp only [heatMult, hc, hL]
    congr 2; ring
  have hint : ∫ σ in (0 : ℝ)..t, (heatMult (ν * (t - σ)) k : ℂ) * F σ =
      ((Real.exp (-(c * t)) : ℝ) : ℂ) *
        ∫ σ in (0 : ℝ)..t, ((Real.exp (c * σ) : ℝ) : ℂ) * F σ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hheat]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring
  rw [hint, hheat, hftc]
  have h1 : ((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  calc ρc (v + t) k = (((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ)) * ρc (v + t) k := by
        rw [h1, one_mul]
    _ = _ := by ring

end HRS.PDE.MFApriori
