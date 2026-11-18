import HRS.Sections.Q66AuxJ

/-!
# Packet Q66: Stein identity under `Q_{N,β}(μ)`, part 4 (the raw identity)

`q66_stein_raw`: for smooth components `v_k` with `∑_k ∂_k(ρ v_k) = -ρ r` and a bounded test
functional `Ψ` with bounded line derivatives `dΨ`,
`E_Q[ -(∑_i r(x_i)) Ψ + ∑_{i,k} v_k(x_i) dΨ_{ik} - β ∑_{i,k} v_k(x_i) B_{ik} Ψ ] = 0`,
where `B_{ik} = ∂_{x_i^k}(N F_N)` is the `k`-th component of the drift of the exponent.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q66_stein_raw (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hN : 1 ≤ N)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x))
    {Ψ : Config d N → ℝ} {dΨ : Fin N → Fin d → Config d N → ℝ}
    (hΨm : Measurable Ψ) (hΨb : ∃ M, ∀ X, |Ψ X| ≤ M)
    (hdΨm : ∀ (i : Fin N) (k : Fin d), Measurable (dΨ i k)) (hdΨb : ∃ M, ∀ i k X, |dΨ i k X| ≤ M)
    (hΨline : ∀ (i : Fin N) (k : Fin d) (Y : Config d N), (∀ a b : Fin N, a ≠ b → Y a ≠ Y b) →
      HasDerivAt (fun τ : ℝ => Ψ (lineCfg i k Y τ)) (dΨ i k Y) 0) :
    ∫ X, (-(∑ i, r (X i)) * Ψ X + ∑ i, ∑ k, v k (X i) * dΨ i k X
        - β * ∑ i, ∑ k, v k (X i) * Bik d s (q66_Vrho d s ρ) i k X * Ψ X)
      ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) = 0 := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hs1 : s < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set g : Torus d → ℝ := periodicRiesz d s with hg
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  set Vr : Torus d → ℝ := q66_Vrho d s ρ with hVr
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ.density
  have hgm : Measurable g := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hV1 : Torus.IsCk 1 Vr := q66_Vrho_isCk1 hd hs0 hsd hρ
  have hVc : Continuous Vr := q66_Vrho_continuous hd hs0 hsd hρ
  have hρc : Continuous ρ := q66_cont_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  -- the Hamiltonian
  set H : Config d N → ℝ := canonicalHamiltonian g Vr with hH
  have hHm : Measurable H := q84d_measurable_H hgm hVc.measurable
  obtain ⟨B0, hB00, hB0⟩ := q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ : ∃ Vm : ℝ, ∀ x, |Vr x| ≤ Vm := by
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hVc.continuousOn
    exact ⟨M, fun x => by simpa using hM x (Set.mem_univ _)⟩
  have hHlow : ∀ X : Config d N, -((N : ℝ) * Vm + N * B0) ≤ H X := by
    intro X
    have := q84d_H_lower hB00 hB0 hVm hN (∅ : Finset (Fin N × Fin N)) (Finset.empty_subset _) X
    simpa using this
  set cH : ℝ := (N : ℝ) * Vm + N * B0 with hcH
  have hexp_le : ∀ X, Real.exp (-β * H X) ≤ Real.exp (β * cH) := fun X => by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hHlow X]
  -- the constants
  obtain ⟨Λ, hΛ⟩ := q66_bound_of_smooth hρ.smooth
  have hρΛ : ∀ x, ρ x ≤ Λ := fun x => (le_abs_self _).trans (hΛ x)
  have hΛ0 : 0 ≤ Λ := (hρ.pos 0).le.trans (hρΛ 0)
  obtain ⟨MΨ, hMΨ⟩ := hΨb
  obtain ⟨MdΨ, hMdΨ⟩ := hdΨb
  set J : ℝ := ∫ x, ∫ y, g (x - y) ∂μ ∂μ with hJ
  -- the field `a_k = ρ v_k`
  have haS : ∀ k, Torus.IsSmooth (fun y => ρ y * v k y) := fun k => q66_isSmooth_mul hρ.smooth (hv k)
  have hpdS : ∀ k, Torus.IsSmooth (Torus.partialDeriv k (fun y => ρ y * v k y)) := fun k =>
    q66_isSmooth_partialDeriv (haS k) k
  have hMa : ∀ k, ∃ M : ℝ, ∀ x, |ρ x * v k x| ≤ M := fun k => q66_bound_of_smooth (haS k)
  have hMpd : ∀ k, ∃ M : ℝ, ∀ x, |Torus.partialDeriv k (fun y => ρ y * v k y) x| ≤ M :=
    fun k => q66_bound_of_smooth (hpdS k)
  choose Ma hMa using hMa
  choose Mpd hMpd using hMpd
  -- the building blocks
  set a : Fin d → Torus d → ℝ := fun k y => ρ y * v k y with ha
  set Ci : Fin N → Config d N → ℝ := fun i X => ∏ b ∈ Finset.univ.erase i, ρ (X b) with hCi
  set D : Fin N → Fin d → Config d N → ℝ := fun i k X =>
    Ci i X * Real.exp (-β * H X) * (Torus.partialDeriv k (a k) (X i) * Ψ X + a k (X i) * dΨ i k X
      - β * (a k (X i) * Bik d s Vr i k X * Ψ X)) with hD
  -- pointwise identity
  have hpt : ∀ X : Config d N, (∏ i, ρ (X i)) * (Real.exp (-β * H X) *
      (-(∑ i, r (X i)) * Ψ X + ∑ i, ∑ k, v k (X i) * dΨ i k X
        - β * ∑ i, ∑ k, v k (X i) * Bik d s Vr i k X * Ψ X)) = ∑ i, ∑ k, D i k X := by
    intro X
    have h1 : ∀ i : Fin N, ∑ k, D i k X = (∏ b, ρ (X b)) * (Real.exp (-β * H X) *
        (-(r (X i)) * Ψ X + ∑ k, v k (X i) * dΨ i k X
          - β * ∑ k, v k (X i) * Bik d s Vr i k X * Ψ X)) := by
      intro i
      have hprod : Ci i X * ρ (X i) = ∏ b, ρ (X b) := by
        simp only [hCi]
        rw [mul_comm]
        exact Finset.mul_prod_erase Finset.univ (fun b => ρ (X b)) (Finset.mem_univ i)
      have hsum : ∑ k, Torus.partialDeriv k (a k) (X i) = -(ρ (X i) * r (X i)) := hdiv (X i)
      have e1 : ∑ k, a k (X i) * dΨ i k X = ρ (X i) * ∑ k, v k (X i) * dΨ i k X := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [ha]; ring
      have e2 : ∑ k, β * (a k (X i) * Bik d s Vr i k X * Ψ X) =
          β * (ρ (X i) * ∑ k, v k (X i) * Bik d s Vr i k X * Ψ X) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_; simp only [ha]; ring
      have e3 : ∑ k, Torus.partialDeriv k (a k) (X i) * Ψ X =
          (∑ k, Torus.partialDeriv k (a k) (X i)) * Ψ X := (Finset.sum_mul _ _ _).symm
      have e4 : ∑ k, D i k X = Ci i X * Real.exp (-β * H X) *
          (∑ k, Torus.partialDeriv k (a k) (X i) * Ψ X + ∑ k, a k (X i) * dΨ i k X
            - ∑ k, β * (a k (X i) * Bik d s Vr i k X * Ψ X)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      rw [e4, e1, e2, e3, hsum, ← hprod]
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_mul,
      Finset.mul_sum]
  -- measurability
  have hBm : ∀ (i : Fin N) (k : Fin d), Measurable (Bik d s Vr i k) := fun i k => q66_Bik_measurable hd hs0 hsd hV1 i k
  have hBi : ∀ (i : Fin N) (k : Fin d), Integrable (Bik d s Vr i k) (volume : Measure (Config d N)) :=
    fun i k => q66_Bik_integrable hd hs0 hs1 hV1 i k
  have hCm : ∀ (i : Fin N), Measurable (Ci i) := fun i =>
    Finset.measurable_prod _ fun b _ => hρm.comp (measurable_pi_apply b)
  have hCb : ∀ (i : Fin N) (X : Config d N), |Ci i X| ≤ Λ ^ (N - 1) := by
    intro i X
    simp only [hCi]
    rw [Finset.abs_prod]
    calc ∏ b ∈ Finset.univ.erase i, |ρ (X b)| ≤ ∏ b ∈ Finset.univ.erase i, Λ :=
          Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) (fun b _ => hΛ (X b))
      _ = Λ ^ (N - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hEm : Measurable (fun X : Config d N => Real.exp (-β * H X)) :=
    Real.measurable_exp.comp (hHm.const_mul _)
  have hEb : ∀ X, |Real.exp (-β * H X)| ≤ Real.exp (β * cH) := fun X => by
    rw [abs_of_pos (Real.exp_pos _)]; exact hexp_le X
  have hmm : ∀ (i : Fin N), Measurable (fun X : Config d N => Ci i X * Real.exp (-β * H X)) :=
    fun i => (hCm i).mul hEm
  have hmb : ∀ (i : Fin N) (X : Config d N), |Ci i X * Real.exp (-β * H X)| ≤ Λ ^ (N - 1) * Real.exp (β * cH) := by
    intro i X
    rw [abs_mul]
    exact mul_le_mul (hCb i X) (hEb X) (abs_nonneg _) (pow_nonneg hΛ0 _)
  have hbdd : ∀ {f g : Config d N → ℝ} (C : ℝ), Integrable g (volume : Measure (Config d N)) →
      Measurable f → (∀ x, |f x| ≤ C) → Integrable (fun x => f x * g x) (volume : Measure (Config d N)) :=
    fun C hg hfm hC => hg.bdd_mul hfm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hbnd : ∀ {f : Config d N → ℝ} (C : ℝ), Measurable f → (∀ x, |f x| ≤ C) →
      Integrable f (volume : Measure (Config d N)) :=
    fun C hfm hC => Integrable.of_bound hfm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hapi : ∀ (k : Fin d) (i : Fin N), Measurable (fun X : Config d N => a k (X i)) := fun k i =>
    (q66_cont_of_smooth (haS k)).measurable.comp (measurable_pi_apply i)
  have hpdi : ∀ (k : Fin d) (i : Fin N), Measurable (fun X : Config d N => Torus.partialDeriv k (a k) (X i)) := fun k i =>
    (q66_cont_of_smooth (hpdS k)).measurable.comp (measurable_pi_apply i)
  have hbr_m : ∀ (i : Fin N) (k : Fin d), Measurable (fun X : Config d N => Torus.partialDeriv k (a k) (X i) * Ψ X
      + a k (X i) * dΨ i k X - β * (a k (X i) * Bik d s Vr i k X * Ψ X)) := fun i k =>
    (((hpdi k i).mul hΨm).add ((hapi k i).mul (hdΨm i k))).sub
      (((hapi k i).mul (hBm i k)).mul hΨm |>.const_mul β)
  have hbr_i : ∀ (i : Fin N) (k : Fin d), Integrable (fun X : Config d N => Torus.partialDeriv k (a k) (X i) * Ψ X
      + a k (X i) * dΨ i k X - β * (a k (X i) * Bik d s Vr i k X * Ψ X))
      (volume : Measure (Config d N)) := by
    intro i k
    refine Integrable.sub (Integrable.add ?_ ?_) ?_
    · exact hbnd (Mpd k * MΨ) ((hpdi k i).mul hΨm) (fun X => by
        rw [abs_mul]
        exact mul_le_mul (hMpd k _) (hMΨ X) (abs_nonneg _) ((abs_nonneg _).trans (hMpd k (X i))))
    · exact hbnd (Ma k * MdΨ) ((hapi k i).mul (hdΨm i k)) (fun X => by
        rw [abs_mul]
        exact mul_le_mul (hMa k _) (hMdΨ i k X) (abs_nonneg _) ((abs_nonneg _).trans (hMa k (X i))))
    · refine Integrable.const_mul ?_ β
      have := hbdd (f := fun X : Config d N => a k (X i) * Ψ X) (g := Bik d s Vr i k) (Ma k * MΨ)
        (hBi i k) ((hapi k i).mul hΨm) (fun X => by
          rw [abs_mul]
          exact mul_le_mul (hMa k _) (hMΨ X) (abs_nonneg _) ((abs_nonneg _).trans (hMa k (X i))))
      refine this.congr (Eventually.of_forall fun X => ?_)
      simp only; ring
  have hDm : ∀ (i : Fin N) (k : Fin d), Measurable (D i k) := fun i k => by
    simp only [hD]
    exact (hmm i).mul (hbr_m i k)
  have hDi : ∀ (i : Fin N) (k : Fin d), Integrable (D i k) (volume : Measure (Config d N)) :=
    fun i k => by
      simp only [hD]
      exact hbdd (f := fun X : Config d N => Ci i X * Real.exp (-β * H X))
        (Λ ^ (N - 1) * Real.exp (β * cH)) (hbr_i i k) (hmm i) (hmb i)
  -- the derivative along coordinate lines
  have hbase : ∀ (i : Fin N) (k : Fin d) (Y : Config d N), (∀ a b : Fin N, a ≠ b → Y a ≠ Y b) →
      HasDerivAt (fun τ : ℝ => a k ((lineCfg i k Y τ) i) * Ci i (lineCfg i k Y τ) *
        Ψ (lineCfg i k Y τ) * Real.exp (-β * H (lineCfg i k Y τ))) (D i k Y) 0 := by
    intro i k Y hY
    have hA : HasDerivAt (fun τ : ℝ => a k ((lineCfg i k Y τ) i))
        (Torus.partialDeriv k (a k) (Y i)) 0 := by
      have := q66_scalar_line_deriv (q66_isCk_of_smooth (haS k) 1) (Y i) k
      have e : (fun τ : ℝ => a k ((lineCfg i k Y τ) i)) =
          fun τ => a k (Y i + Torus.mk (τ • ek k)) := by
        funext τ; simp [lineCfg]
      rw [e]; exact this
    have hC : ∀ τ : ℝ, Ci i (lineCfg i k Y τ) = Ci i Y := by
      intro τ
      simp only [hCi]
      refine Finset.prod_congr rfl fun b hb => ?_
      have hbi : b ≠ i := Finset.ne_of_mem_erase hb
      simp [lineCfg, Function.update_of_ne hbi]
    have hP := hΨline i k Y hY
    have hH := q66_H_line_deriv hd hs0 hsd hV1 Y hY i k
    have hE : HasDerivAt (fun τ : ℝ => Real.exp (-β * H (lineCfg i k Y τ)))
        (Real.exp (-β * H Y) * (-β * Bik d s Vr i k Y)) 0 := by
      have := (hH.const_mul (-β)).exp
      simp only [lineCfg_zero] at this
      exact this
    have h1 := (((hA.mul (hasDerivAt_const (0 : ℝ) (Ci i Y))).mul hP).mul hE)
    simp only [lineCfg_zero] at h1
    have e2 : (fun τ : ℝ => a k ((lineCfg i k Y τ) i) * Ci i (lineCfg i k Y τ) *
        Ψ (lineCfg i k Y τ) * Real.exp (-β * H (lineCfg i k Y τ))) =
        fun τ => a k ((lineCfg i k Y τ) i) * Ci i Y * Ψ (lineCfg i k Y τ) *
          Real.exp (-β * H (lineCfg i k Y τ)) := by
      funext τ; rw [hC]
    rw [e2]
    convert h1 using 1
    simp only [hD, Pi.mul_apply, lineCfg_zero]
    ring
  have hibp : ∀ (i : Fin N) (k : Fin d), ∫ X, D i k X = 0 := fun i k =>
    q66_line_ibp hd i k (w := fun X => a k (X i) * Ci i X * Ψ X * Real.exp (-β * H X))
      (hDm i k) (hDi i k) (hbase i k)
  -- assemble
  have hsumD : ∫ X, ∑ i, ∑ k, D i k X = 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ => hDi i k)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hDi i k)]
    exact Finset.sum_eq_zero fun k _ => hibp i k
  rw [q66_integral_Q hρ hgm β]
  have hWen : ∀ X : Config d N, Real.exp (-β * PreparationAux.Wen g N μ X) =
      Real.exp (-β * ((N : ℝ) / 2 * J)) * Real.exp (-β * H X) := by
    intro X
    rw [← Real.exp_add]; congr 1
    rw [hμ, hg, q66_Wen_eq hρ X]; simp only [hH, hVr, hJ, hg, hμ]; ring
  have hint0 : ∫ X, (∏ i, ρ (X i)) * (Real.exp (-β * PreparationAux.Wen g N μ X) *
      (-(∑ i, r (X i)) * Ψ X + ∑ i, ∑ k, v k (X i) * dΨ i k X
        - β * ∑ i, ∑ k, v k (X i) * Bik d s Vr i k X * Ψ X)) = 0 := by
    have : ∀ X : Config d N, (∏ i, ρ (X i)) * (Real.exp (-β * PreparationAux.Wen g N μ X) *
        (-(∑ i, r (X i)) * Ψ X + ∑ i, ∑ k, v k (X i) * dΨ i k X
          - β * ∑ i, ∑ k, v k (X i) * Bik d s Vr i k X * Ψ X)) =
        Real.exp (-β * ((N : ℝ) / 2 * J)) * ∑ i, ∑ k, D i k X := by
      intro X
      rw [hWen X, ← hpt X]; ring
    simp_rw [this]
    rw [integral_const_mul, hsumD, mul_zero]
  rw [hint0, mul_zero]

end HRS.Q66

end
