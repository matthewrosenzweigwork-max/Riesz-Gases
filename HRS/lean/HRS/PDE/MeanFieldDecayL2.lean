import HRS.PDE.MeanFieldDecayGapB

/-!
# Decay of the finite-regularity mean-field solution, packet P7b (package MF-01)
(plan `MeanFieldDecayPlan.md`, §1 P7b)

Gronwall for the free-energy gap along a real solution (`gap_decay_on`) and the uniform
`L²` decay to the thermal density (`exists_l2_decay`).

Statement check (`pp.parens`): neither packet statement contains an integral, so the
`∫`-precedence trap does not occur; both are proved exactly as stated.  The Gronwall step is done
by monotonicity of `G(τ) e^{κτ}` (`antitoneOn_of_deriv_nonpos` on `[0,T]`, derivative on `(0,T)`,
continuity on `[0,T]`), which avoids the `ε → 0` argument of the plan.

Dependence on the scaffold: `exists_l2_decay` uses `MFGlobal.finite_reg_uniform_bounds` and
`MFGlobal.isRealCoeff_of_isMFSolutionHK`, hence is conditional on
`MFApriori.mf_apriori_bound_real_on` (AP7).  `gap_decay_on` is unconditional.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFDecay

open MFApriori

variable {d : ℕ}

/-! ### Section 1: Gronwall for the gap -/

/-- (B1) Gronwall for the gap along a real solution on `[0,T]` with uniform bounds. -/
theorem gap_decay_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (β : ℝ)
    (hβ : 0 < β) (ρc : ℝ → Coeff d) {T : ℝ} (hT : 0 ≤ T) (H : MFSolRealOn d s V β⁻¹ K ρ₀ ρc T)
    (cL cU : ℝ) (hcL : 0 < cL) (hbd : ∀ t ∈ Set.Icc 0 T, ∀ x, cL ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ cU)
    (hmass : ∀ t ∈ Set.Icc 0 T, ρc t 0 = 1) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρc : Continuous ρβ)
    (lam Lam : ℝ) (hlam : 0 < lam) (hρbd : ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam)
    (hmem : MemHs K (coeffOf ρβ)) :
    ∀ t ∈ Set.Icc 0 T,
      freeEnergy' d s V β⁻¹ (ρc t) - freeEnergy' d s V β⁻¹ (coeffOf ρβ) ≤
        (freeEnergy' d s V β⁻¹ (ρc 0) - freeEnergy' d s V β⁻¹ (coeffOf ρβ)) *
          Real.exp (-(rate d s β cL cU lam Lam) * t) := by
  intro t ht
  set κ : ℝ := rate d s β cL cU lam Lam with hκ
  set G : ℝ → ℝ := fun τ =>
    freeEnergy' d s V β⁻¹ (ρc τ) - freeEnergy' d s V β⁻¹ (coeffOf ρβ) with hG
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  -- the entropy-production inequality along the solution
  have hEP : ∀ τ ∈ Icc 0 T, κ * G τ ≤ dissipation d s V β⁻¹ (ρc τ) := fun τ hτ =>
    entropy_production hd s hs0 hsd (K : ℝ) hK V hV2 β hβ (ρc τ) (H.sol.cont.1 τ hτ)
      (H.real τ hτ) (hmass τ hτ) cL cU hcL (hbd τ hτ) ρβ hρβ hρc lam Lam hlam hρbd hmem
  -- continuity of `G`
  have hGc : ContinuousOn G (Icc 0 T) :=
    (continuousOn_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV β⁻¹ ρc H).sub continuousOn_const
  have hhc : ContinuousOn (fun τ => G τ * Real.exp (κ * τ)) (Icc 0 T) :=
    hGc.mul (by fun_prop)
  have hderiv : ∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => G τ * Real.exp (κ * τ))
      ((-dissipation d s V β⁻¹ (ρc τ)) * Real.exp (κ * τ) + G τ * (Real.exp (κ * τ) * κ)) τ := by
    intro τ hτ
    have hTpos : 0 < T := hτ.1.trans hτ.2
    have h1 := hasDerivAt_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV β⁻¹ ρc H (a := 0) (b := T)
      le_rfl hTpos le_rfl cL hcL (fun t' ht' x => (hbd t' ht' x).1) hτ
    have h2 : HasDerivAt G (-dissipation d s V β⁻¹ (ρc τ)) τ := by
      simpa [hG] using h1.sub_const (freeEnergy' d s V β⁻¹ (coeffOf ρβ))
    have h3 : HasDerivAt (fun τ => Real.exp (κ * τ)) (Real.exp (κ * τ) * κ) τ := by
      simpa using ((hasDerivAt_id τ).const_mul κ).exp
    exact h2.mul h3
  have hanti : AntitoneOn (fun τ => G τ * Real.exp (κ * τ)) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hhc ?_ ?_
    · rw [interior_Icc]
      exact fun τ hτ => (hderiv τ hτ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro τ hτ
      rw [(hderiv τ hτ).deriv]
      have h1 := hEP τ (Ioo_subset_Icc_self hτ)
      have he := Real.exp_pos (κ * τ)
      nlinarith
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have key := hanti h0 ht ht.1
  simp only [mul_zero, Real.exp_zero, mul_one] at key
  have he : 0 < Real.exp (κ * t) := Real.exp_pos _
  have : G t = G t * Real.exp (κ * t) * Real.exp (-κ * t) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  show G t ≤ G 0 * Real.exp (-κ * t)
  rw [this]
  exact mul_le_mul_of_nonneg_right key (Real.exp_pos _).le


/-! ### Section 2: the rate is monotone in the temperature -/

/-- `rate` decreases with `β` (increases with `ν = β⁻¹`): on `β ≤ βp` we have
`rate βp ≤ rate β`. -/
theorem rate_anti (s cL cU lam Lam β βp : ℝ) (hcL : 0 < cL) (hlam : 0 < lam)
    (hM : 0 < max cU Lam) (hβ : 0 < β) (hββ : β ≤ βp) :
    rate d s βp cL cU lam Lam ≤ rate d s β cL cU lam Lam := by
  have hβp : 0 < βp := hβ.trans_le hββ
  have hν : βp⁻¹ ≤ β⁻¹ := inv_anti₀ hβ hββ
  have hν0 : 0 < βp⁻¹ := inv_pos.mpr hβp
  have hq : 0 ≤ |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2 := by positivity
  set q := |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2 with hqdef
  set M := max cU Lam with hMdef
  set ν := β⁻¹ with hνdef
  set ν0 := βp⁻¹ with hν0def
  have hD1 : 0 < ν0 / lam + q := by have := div_pos hν0 hlam; linarith
  have hD2 : 0 < ν / lam + q := by
    have := div_pos (hν0.trans_le hν) hlam; linarith
  unfold rate
  rw [← hqdef, ← hMdef, ← hνdef, ← hν0def]
  rw [div_le_div_iff₀ hD1 hD2]
  have ha : 0 ≤ cL * (2 * Real.pi) ^ 2 / M ^ 2 := by positivity
  have e1 : cL * (2 * Real.pi) ^ 2 * (ν0 / M) ^ 2 = (cL * (2 * Real.pi) ^ 2 / M ^ 2) * ν0 ^ 2 := by
    field_simp
  have e2 : cL * (2 * Real.pi) ^ 2 * (ν / M) ^ 2 = (cL * (2 * Real.pi) ^ 2 / M ^ 2) * ν ^ 2 := by
    field_simp
  rw [e1, e2]
  have hp : 0 ≤ 1 / lam := by positivity
  have key : ν0 ^ 2 * (ν / lam + q) ≤ ν ^ 2 * (ν0 / lam + q) := by
    have h1 : ν0 ^ 2 * (ν / lam) ≤ ν ^ 2 * (ν0 / lam) := by
      have : ν0 ^ 2 * (ν / lam) = (1 / lam) * (ν0 * ν) * ν0 := by ring
      have h' : ν ^ 2 * (ν0 / lam) = (1 / lam) * (ν0 * ν) * ν := by ring
      rw [this, h']
      exact mul_le_mul_of_nonneg_left hν (by positivity)
    have h2 : ν0 ^ 2 * q ≤ ν ^ 2 * q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hν0.le hν 2) hq
    nlinarith
  calc cL * (2 * Real.pi) ^ 2 / M ^ 2 * ν0 ^ 2 * (ν / lam + q)
      = (cL * (2 * Real.pi) ^ 2 / M ^ 2) * (ν0 ^ 2 * (ν / lam + q)) := by ring
    _ ≤ (cL * (2 * Real.pi) ^ 2 / M ^ 2) * (ν ^ 2 * (ν0 / lam + q)) :=
        mul_le_mul_of_nonneg_left key ha
    _ = _ := by ring


/-! ### Section 3: elementary `H⁰` facts -/

theorem hsNormSq_nonneg' (m : ℝ) (c : Coeff d) : 0 ≤ hsNormSq m c :=
  tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)

theorem hsNorm_sq' (m : ℝ) (c : Coeff d) : hsNorm m c ^ 2 = hsNormSq m c :=
  Real.sq_sqrt (hsNormSq_nonneg' m c)

/-- `‖a - b‖²_{H⁰} ≤ 2 ‖a‖²_{H⁰} + 2 ‖b‖²_{H⁰}`. -/
theorem hsNormSq_sub_le (a b : Coeff d) (ha : MemHs 0 a) (hb : MemHs 0 b) :
    hsNormSq 0 (a - b) ≤ 2 * hsNormSq 0 a + 2 * hsNormSq 0 b := by
  have h := Aux.hsNorm_le_add_sub 0 (Aux.memHs_sub ha hb) ha
  rw [sub_sub_cancel_left, Aux.hsNorm_neg] at h
  have h0 : 0 ≤ hsNorm 0 (a - b) := Real.sqrt_nonneg _
  have h1 := pow_le_pow_left₀ h0 h 2
  have e1 := hsNorm_sq' 0 (a - b)
  have e2 := hsNorm_sq' 0 a
  have e3 := hsNorm_sq' 0 b
  nlinarith [sq_nonneg (hsNorm 0 a - hsNorm 0 b)]

/-- `‖ρ̂β‖²_{H⁰} = ∫ ρβ² ≤ Lam²` for a continuous `ρβ` with `|ρβ| ≤ Lam`. -/
theorem hsNormSq_zero_coeffOf_le (ρβ : Torus d → ℝ) (hc : Continuous ρβ) (Lam : ℝ)
    (hb : ∀ x, |ρβ x| ≤ Lam) : hsNormSq 0 (coeffOf ρβ) ≤ Lam ^ 2 := by
  have h := hasSum_norm_sq_coeffOf ρβ hc
  have e : hsNormSq 0 (coeffOf ρβ) = ∫ x, ρβ x ^ 2 := by
    unfold hsNormSq
    simp_rw [Aux.sobWeight_zero_aux, one_mul]
    exact h.tsum_eq
  rw [e]
  have hLam : 0 ≤ Lam := (abs_nonneg _).trans (hb (Classical.arbitrary _))
  calc ∫ x, ρβ x ^ 2 ≤ ∫ _x : Torus d, Lam ^ 2 := by
        refine integral_mono (integrable_of_continuous' (hc.pow 2)) (integrable_const _) ?_
        intro x
        have := hb x
        have h2 : |ρβ x| ^ 2 ≤ Lam ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        simpa [sq_abs] using h2
    _ = Lam ^ 2 := by simp


/-! ### Section 4: the uniform `L²` decay -/

/-- (B2) `L²` decay to the thermal density, uniform in `β ∈ [β₋,β₊]`, for every global
`IsMFSolutionHK` solution. -/
theorem exists_l2_decay (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∃ C₀ κ : ℝ, 0 < C₀ ∧ 0 < κ ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ →
        (∀ x, 0 < ρβ x) → MemSobolev K ρβ →
      ∀ t, 0 ≤ t → MemHs 0 (ρc t - coeffOf ρβ) ∧
        hsNormSq 0 (ρc t - coeffOf ρβ) ≤ C₀ * Real.exp (-κ * t) := by
  have hK2 : (d : ℝ) / 2 + 2 < (K : ℝ) := by linarith [H.hK]
  have hV2 : Torus.IsCk 2 V := H.hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  have hVc : Continuous V := MFAux.continuous_of_isCk (H.hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2)))
  obtain ⟨c, C, hc, hunif⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨lam, Lam, hlam, hth⟩ :=
    exists_thermal_bounds hd s H.hs0 H.hsd βm βp H.hβm H.hββ V hVc
  -- explicit constants
  set cU : ℝ := max (max C c) 1 with hcU
  set Lam' : ℝ := max (max Lam lam) 1 with hLam'
  set M : ℝ := max cU Lam' with hM
  have hM1 : 1 ≤ M := (le_max_right (max C c) 1).trans (le_max_left cU Lam')
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  set g : ℝ := |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) with hg
  have hg0 : 0 ≤ g := by positivity
  have hmem0 : MemHs 0 (coeffOf ρ₀) :=
    Aux.memHs_mono (by exact_mod_cast (Nat.zero_le K))
      (ProdAux.memHs_of_memSobolev (K : ℝ) H.hρ₀H).1
  set A : ℝ := hsNormSq 0 (coeffOf ρ₀) with hA
  have hA0 : 0 ≤ A := hsNormSq_nonneg' _ _
  set P : ℝ := βm⁻¹ / lam + g / 2 with hP
  have hP0 : 0 < P := by
    have : 0 < βm⁻¹ / lam := div_pos (inv_pos.mpr H.hβm) hlam
    positivity
  set B0 : ℝ := 2 * A + 2 * Lam' ^ 2 with hB0
  have hB00 : 0 ≤ B0 := by positivity
  have hβp0 : 0 < βp := H.hβm.trans_le H.hββ
  refine ⟨2 * M * βp * P * B0 + 1, rate d s βp c cU lam Lam', ?_, ?_, ?_⟩
  · have : 0 ≤ 2 * M * βp * P * B0 := by positivity
    linarith
  · exact rate_pos s βp c cU lam Lam' hβp0 hc hlam
      ((le_max_right C c).trans (le_max_left _ 1))
      ((le_max_right Lam lam).trans (le_max_left _ 1))
  · intro β hβ ρc hsol ρβ hρβ hρcont hρpos hSob t ht
    have hβ0 : 0 < β := H.hβm.trans_le hβ.1
    have hν0 : 0 < β⁻¹ := inv_pos.mpr hβ0
    have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hsol
    have Hon : MFSolRealOn d s V β⁻¹ K ρ₀ ρc t := ⟨MFApriori.IsMFSolutionHK.toSolOn hsol t, fun τ hτ => hreal τ hτ.1⟩
    have hmass : ∀ τ ∈ Icc 0 t, ρc τ 0 = 1 := by
      intro τ hτ
      rw [coeff_zero_eq_on hd s V ρ₀ β⁻¹ K ρc (MFApriori.IsMFSolutionHK.toSolOn hsol t) hτ, coeffOf_zero_eq_integral',
        H.hρ₀.integral_one]
      simp
    have hb := hunif β hβ ρc hsol
    have hbd : ∀ τ ∈ Icc 0 t, ∀ x, c ≤ mfPath ρc τ x ∧ mfPath ρc τ x ≤ cU := fun τ hτ x =>
      ⟨((hb τ hτ.1).1 x).1,
        ((hb τ hτ.1).1 x).2.trans ((le_max_left C c).trans (le_max_left _ 1))⟩
    have hmemβ : MemHs (K : ℝ) (coeffOf ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
    have hρbd : ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam' := fun x =>
      ⟨(hth β hβ ρβ hρβ hρcont hρpos x).1,
        (hth β hβ ρβ hρβ hρcont hρpos x).2.trans ((le_max_left Lam lam).trans (le_max_left _ 1))⟩
    have ht0 : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
    have h00 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
    have hdec := gap_decay_on hd s H.hs0 H.hsd K hK2 V ρ₀ H.hV β hβ0 ρc ht Hon c cU hc hbd hmass
      ρβ hρβ hρcont lam Lam' hlam hρbd hmemβ t ht0
    have hmt : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
    have hm0 : MemHs (K : ℝ) (ρc 0) := hsol.cont.1 0 (Set.mem_Ici.2 le_rfl)
    have hmt0 : MemHs 0 (ρc t) := Aux.memHs_mono (by exact_mod_cast (Nat.zero_le K)) hmt
    have hmβ0 : MemHs 0 (coeffOf ρβ) := Aux.memHs_mono (by exact_mod_cast (Nat.zero_le K)) hmemβ
    have hZmem : MemHs 0 (ρc t - coeffOf ρβ) := Aux.memHs_sub hmt0 hmβ0
    refine ⟨hZmem, ?_⟩
    have hgt := (gap_bounds hd s H.hs0 H.hsd (K : ℝ) hK2 V hV2 β hβ0 (ρc t) hmt (hreal t ht)
      (hmass t ht0) c cU hc (hbd t ht0) ρβ hρβ hρcont lam Lam' hlam hρbd hmemβ)
    have hg0' := (gap_bounds hd s H.hs0 H.hsd (K : ℝ) hK2 V hV2 β hβ0 (ρc 0) hm0 (hreal 0 le_rfl)
      (hmass 0 h00) c cU hc (hbd 0 h00) ρβ hρβ hρcont lam Lam' hlam hρbd hmemβ)
    have hrate := rate_anti (d := d) s c cU lam Lam' β βp hc hlam hM0 hβ0 hβ.2
    -- notation
    set Z := hsNormSq 0 (ρc t - coeffOf ρβ) with hZ
    set S0 := hsNormSq 0 (ρc 0 - coeffOf ρβ) with hS0
    set Gt := freeEnergy' d s V β⁻¹ (ρc t) - freeEnergy' d s V β⁻¹ (coeffOf ρβ) with hGt
    set G0 := freeEnergy' d s V β⁻¹ (ρc 0) - freeEnergy' d s V β⁻¹ (coeffOf ρβ) with hG0
    set E := Real.exp (-(rate d s βp c cU lam Lam') * t) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hS0nn : 0 ≤ S0 := hsNormSq_nonneg' _ _
    have hZnn : 0 ≤ Z := hsNormSq_nonneg' _ _
    have hG0nn : 0 ≤ G0 := by
      have : 0 ≤ β⁻¹ / (2 * M) * S0 := by positivity
      linarith [hg0'.1]
    -- `S0 ≤ B0`
    have hS0le : S0 ≤ B0 := by
      have hinit : ρc 0 = coeffOf ρ₀ := hsol.init
      have h1 : S0 ≤ 2 * A + 2 * hsNormSq 0 (coeffOf ρβ) := by
        rw [hS0, hinit]
        exact hsNormSq_sub_le _ _ hmem0 hmβ0
      have h2 : hsNormSq 0 (coeffOf ρβ) ≤ Lam' ^ 2 :=
        hsNormSq_zero_coeffOf_le ρβ hρcont Lam' fun x => by
          rw [abs_of_pos (hρpos x)]; exact (hρbd x).2
      linarith
    have hβinv : β⁻¹ ≤ βm⁻¹ := inv_anti₀ H.hβm hβ.1
    have hG0le : G0 ≤ P * B0 := by
      have h1 := hg0'.2
      have h2 : β⁻¹ / lam + g / 2 ≤ P := by
        rw [hP]; gcongr
      calc G0 ≤ (β⁻¹ / lam + |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2) * S0 := h1
        _ ≤ P * B0 := by
          rw [← hg]
          exact mul_le_mul h2 hS0le hS0nn hP0.le
    have hGtle : Gt ≤ G0 * E := by
      refine hdec.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hG0nn)
      have := mul_le_mul_of_nonneg_right hrate ht
      linarith
    have step1 : Z ≤ Gt * (2 * M * β) := by
      calc Z = β⁻¹ / (2 * M) * Z * (2 * M * β) := by field_simp
        _ ≤ Gt * (2 * M * β) := mul_le_mul_of_nonneg_right hgt.1 (by positivity)
    have step2 : Gt * (2 * M * β) ≤ (P * B0 * E) * (2 * M * βp) := by
      have h1 : Gt ≤ P * B0 * E := hGtle.trans (mul_le_mul_of_nonneg_right hG0le hE0.le)
      have h2 : 2 * M * β ≤ 2 * M * βp := by gcongr; exact hβ.2
      have h3 : 0 ≤ P * B0 * E := by positivity
      exact mul_le_mul h1 h2 (by positivity) h3
    have : 0 ≤ 2 * M * βp * P * B0 * E := by positivity
    nlinarith

end HRS.PDE.MFDecay
