import HRS.Stochastic.EmpiricalIto
import HRS.Duality.PairingExpansion
import HRS.PDE.MeanFieldPairing
import HRS.PDE.MeanFieldFejer
import HRS.PDE.KernelInputsD1
import HRS.PDE.Convention
import HRS.PDE.Classical

/-!
# HRS.Stochastic.Duality — Proposition 3.7 (`M:B:prop:duality-identity`), Packet 2

New definitions `flucPair`, `flucInteraction` (the bilinear expansion of `B_ψ(ρ_N, ρ_N)`), and the two
analytic ingredients of the duality identity:

* `pairing_expansion_pointwise` and the pairing identities: Lemma 3.1 (`HRS.Duality.pairing_expansion`,
  torus case) in its pointwise form, and the consequences for
  `interactionPairing D ψ μ_N μ`, `interactionPairing D ψ μ μ_N`, `interactionPairing D ψ μ μ`;
* `meanField_pairing_timeDependent`: the time-dependent weak form of the mean-field equation paired
  with an `IsC12Test` test function (telescoping/approximate-FTC argument; the time regularity of
  `r ↦ ρ_r` is *derived* from the integrated weak form and the `C³` bound: the generator is bounded,
  `r ↦ ⟨ψ, μ_r⟩` is measurable by a Lipschitz-or-constant dichotomy, `ρ_r(x)` is measurable and then
  continuous in `r` through Fejér test functions).

Deviation from the spec statement of `meanField_pairing_timeDependent`: the hypothesis `hd : 1 ≤ d` is
added (it is needed for the good-kernel facts of `periodicRieszGrad`); the spec has no `hd`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `⟨ψ, ρ_N⟩ = ⟨ψ, μ_N⟩ − ⟨ψ, μ⟩` (`B:eq:…` L459, `Fluc_N`). -/
def flucPair (x : Fin N → Torus d) (ρ : Torus d → ℝ) (ψ : Torus d → ℝ) : ℝ :=
  pair (empirical x) ψ - pair (withDensityReal ρ) ψ

/-- `B_ψ(ρ_N, ρ_N)` expanded bilinearly, `ρ_N = μ_N − μ`; each of the four symmetrised
pairings is an absolutely convergent integral for `ψ ∈ C²` and bounded `ρ`
(`B:eq:B-symmetrized` L1495, cancellation convention L10087). -/
def flucInteraction (D : DynData d) (ψ : Torus d → ℝ) (x : Fin N → Torus d) (ρ : Torus d → ℝ) : ℝ :=
  interactionPairing D ψ (empirical x) (empirical x)
  - interactionPairing D ψ (empirical x) (withDensityReal ρ)
  - interactionPairing D ψ (withDensityReal ρ) (empirical x)
  + interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ)


theorem isLipschitz_of_lift_lipschitz {ρ : Torus d → ℝ} {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) : KernelGrad.IsLipschitz (Λ' : ℝ) ρ := by
  intro x y
  set r := KernelGrad.centeredRep (x - y) with hr
  have hmk : Torus.mk (Torus.rep y + r) = x := by
    rw [KernelGrad.mk_add, Torus.mk_rep, hr, KernelGrad.mk_centeredRep]; abel
  have := hLip.dist_le_mul (Torus.rep y + r) (Torus.rep y)
  have e1 : Torus.lift ρ (Torus.rep y + r) = ρ x := by simp [Torus.lift, hmk]
  have e2 : Torus.lift ρ (Torus.rep y) = ρ y := by simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
  exact this


theorem matVec_transpose_apply_eq_inner (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (a : Fin d) :
    Torus.matVec M.transpose v a = inner ℝ v (Torus.matVec M (EuclideanSpace.single a (1 : ℝ))) := by
  rw [Duality.inner_matVec_transpose]
  simp [EuclideanSpace.inner_single_right]

theorem lipB_vcomp {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (M : Matrix (Fin d) (Fin d) ℝ) (a : Fin d) :
    PDE.MFPairing.LipB (fun y => Torus.matVec M.transpose (Torus.grad ψ y) a) := by
  have e : (fun y => Torus.matVec M.transpose (Torus.grad ψ y) a) =
      fun y => inner ℝ (Torus.grad ψ y) (Torus.matVec M (EuclideanSpace.single a (1 : ℝ))) :=
    funext fun y => matVec_transpose_apply_eq_inner M _ a
  rw [e]
  exact PDE.MFPairing.LipB.of_isCk (PDE.MFPairing.isCk_one_inner_grad hψ _)


theorem lipB_of_lipschitz {ρ : Torus d → ℝ} {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) : PDE.MFPairing.LipB ρ := by
  have hL := isLipschitz_of_lift_lipschitz hLip
  have hc : Continuous ρ := KernelGrad.IsLipschitz.continuous hL (NNReal.coe_nonneg _)
  obtain ⟨B, hB0, hB⟩ := Duality.bounded_of_continuous hc
  exact ⟨hc, B, Λ', hB0, NNReal.coe_nonneg _, hB, hL⟩

/-- Lemma 3.1 `M:B:lem:pairing-expansion` in its pointwise form (spec §3(b)3). -/
theorem pairing_expansion_pointwise (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) (x : Torus d) :
    ∫ y, (if x = y then 0 else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
            (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))) ∂(withDensityReal ρ)
      = inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x))
        - PDE.nonlocalTerm D ρ ψ x := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd D.hs0 D.hsd
  have hρL := lipB_of_lipschitz hLip
  obtain ⟨hρc, Bρ, Lρ, hBρ0, hLρ0, hBρ, hLρ⟩ := hρL
  have hKρ : Integrable (KernelGrad.kern (periodicRieszGrad d D.s) ρ x) :=
    KernelGrad.integrable_kern hG hρ.measurable hBρ hLρ hLρ0 hBρ0 x
  have hKψ : ∀ a : Fin d, Integrable (KernelGrad.kern (periodicRieszGrad d D.s)
      (fun y => ρ y * Torus.matVec D.M.transpose (Torus.grad ψ y) a) x) := by
    intro a
    obtain ⟨hc, B, L, hB0, hL0, hB, hL⟩ :=
      PDE.MFPairing.LipB.mul (lipB_of_lipschitz hLip) (lipB_vcomp hψ D.M a)
    exact KernelGrad.integrable_kern hG (hc.measurable) hB hL hL0 hB0 x
  have key := Duality.integral_pairKernel_eq (s := D.s) (f := ψ) D.M hρ x hKρ hKψ
  have e : (fun y => if x = y then (0 : ℝ) else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
            (Torus.matVec D.M (periodicRieszGrad d D.s (x - y))))
      = fun y => 2 * Duality.pairKernelB ψ D.M D.s x y := by
    funext y
    unfold Duality.pairKernelB
    split_ifs <;> ring
  rw [e, integral_const_mul, key]
  unfold Duality.divConvB PDE.nonlocalTerm
  ring


theorem interKernel_eq_pairKernelB (D : DynData d) (ψ : Torus d → ℝ) (x y : Torus d) :
    interKernel D ψ x y = 2 * Duality.pairKernelB ψ D.M D.s x y := by
  unfold interKernel Duality.pairKernelB
  split_ifs <;> ring

theorem interKernel_symm (D : DynData d) (ψ : Torus d → ℝ) (x y : Torus d) :
    interKernel D ψ y x = interKernel D ψ x y := by
  rw [interKernel_eq_pairKernelB, interKernel_eq_pairKernelB, Duality.pairKernelB_symm D.M D.hsd]

theorem integrable_interKernel (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} {B : ℝ}
    (hB : ∀ x, ρ x ≤ B) (x : Torus d) :
    Integrable (fun y => interKernel D ψ x y) (withDensityReal ρ) := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd D.hs0 D.hsd
  obtain ⟨KM, hKM0, hKM⟩ := Duality.pairKernelB_bound hψ D.M hG
  have hmeas := Duality.measurable_pairKernelB (s := D.s) hψ D.M hG.hsd
  have hgi : Integrable (fun z : Torus d => KM * (‖z‖ ^ (-D.s) + d)) volume :=
    ((KernelGrad.integrable_norm_rpow_neg hG.pos hG.hsd).add (integrable_const _)).const_mul KM
  have hgx : Integrable (fun y : Torus d => 2 * (KM * (‖x - y‖ ^ (-D.s) + d))) volume :=
    (hgi.comp_sub_left x).const_mul 2
  have := Duality.isFiniteMeasure_withDensityReal hB
  have hm : Measurable (fun y => interKernel D ψ x y) := by
    have e : (fun y => interKernel D ψ x y) = fun y => 2 * Duality.pairKernelB ψ D.M D.s x y :=
      funext fun y => interKernel_eq_pairKernelB D ψ x y
    rw [e]
    exact (hmeas.comp (measurable_const.prodMk measurable_id)).const_mul 2
  refine Integrable.mono' (Duality.integrable_withDensityReal_of hB hgx) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  show ‖interKernel D ψ x y‖ ≤ 2 * (KM * (‖x - y‖ ^ (-D.s) + d))
  rw [interKernel_eq_pairKernelB, Real.norm_eq_abs, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (hKM x y) (by norm_num)


theorem sup_bound_of_lipschitz {ρ : Torus d → ℝ} {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) : ∃ B : ℝ, ∀ x, ρ x ≤ B := by
  obtain ⟨hc, B, L, hB0, hL0, hB, hL⟩ := lipB_of_lipschitz hLip
  exact ⟨B, fun x => (le_abs_self _).trans (hB x)⟩

/-- `interactionPairing D ψ μ_N μ = (2N)⁻¹ ∑_i (⟨∇ψ, M ∇g*ρ⟩ - Div g*(ρ Mᵀ∇ψ))(x_i)`. -/
theorem interactionPairing_empirical_withDensity (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) (hN : 0 < N) (X : Config d N) :
    interactionPairing D ψ (empirical X) (withDensityReal ρ)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (inner ℝ (Torus.grad ψ (X i))
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ (X i)))
          - PDE.nonlocalTerm D ρ ψ (X i))) := by
  unfold interactionPairing
  congr 1
  have h1 : ∀ x, ∫ y, (if x = y then 0 else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
            (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))) ∂(withDensityReal ρ)
      = inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x))
        - PDE.nonlocalTerm D ρ ψ x := fun x => pairing_expansion_pointwise hd hψ hρ hLip x
  simp only [h1]
  exact pair_empirical hN X _

theorem interactionPairing_withDensity_empirical (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ' : ℝ≥0}
    (hLip : LipschitzWith Λ' (Torus.lift ρ)) (hN : 0 < N) (X : Config d N) :
    interactionPairing D ψ (withDensityReal ρ) (empirical X)
      = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (inner ℝ (Torus.grad ψ (X i))
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ (X i)))
          - PDE.nonlocalTerm D ρ ψ (X i))) := by
  obtain ⟨B, hB⟩ := sup_bound_of_lipschitz hLip
  have hint : ∀ j, Integrable (fun x => interKernel D ψ x (X j)) (withDensityReal ρ) := by
    intro j
    have := integrable_interKernel hd hψ (D := D) hB (X j)
    exact this.congr (Filter.Eventually.of_forall fun x => (interKernel_symm D ψ (X j) x).symm)
  unfold interactionPairing
  congr 1
  have h1 : ∀ x, ∫ y, (if x = y then 0 else inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
            (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))) ∂(empirical X)
      = (N : ℝ)⁻¹ * ∑ j, interKernel D ψ x (X j) := fun x => pair_empirical hN X (interKernel D ψ x)
  simp only [h1]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ x, interKernel D ψ x (X j) = interKernel D ψ (X j) x := fun x =>
    interKernel_symm D ψ (X j) x
  simp_rw [e]
  exact pairing_expansion_pointwise hd hψ hρ hLip (X j)

theorem interactionPairing_withDensity_self (hd : 1 ≤ d) (D : DynData d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      ∫ x, ρ x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) :=
  PDE.MFPairing.interactionPairing_eq_of_isCk hd D ρ hρ1 hρ.nonneg ψ hψ



open PDE.MFThermalExist in
theorem fejer_mk (N : ℕ) (w : Euc d) : fejer N (Torus.mk w) = ∏ i : Fin d,
      (((∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (j * w i)))^2 +
        (∑ j ∈ Finset.range N, Real.sin (2 * Real.pi * (j * w i)))^2) / N) := by
  unfold fejer
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have hm : ∀ j : ℕ, Torus.mode (Pi.single i (j : ℤ)) (Torus.mk w)
      = Complex.exp (((2 * Real.pi * (j * w i) : ℝ) : ℂ) * Complex.I) := by
    intro j
    rw [Torus.mode_mk]
    congr 3
    simp [Lattice.dot, Pi.single_apply]
  simp_rw [hm]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

open PDE.MFThermalExist in
theorem contDiff_fejer_lift (n : ℕ) (N : ℕ) (a : Euc d) :
    ContDiff ℝ n (fun u : Euc d => fejer N (Torus.mk (a - u))) := by
  have e : (fun u : Euc d => fejer N (Torus.mk (a - u))) = fun u => ∏ i : Fin d,
      (((∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (j * (a - u) i)))^2 +
        (∑ j ∈ Finset.range N, Real.sin (2 * Real.pi * (j * (a - u) i)))^2) / N) :=
    funext fun u => fejer_mk N (a - u)
  rw [e]
  refine contDiff_prod fun i _ => ?_
  have hc : ContDiff ℝ n (fun u : Euc d => (a - u) i) := by
    have : (fun u : Euc d => (a - u) i) = fun u => a i - u i := rfl
    rw [this]
    exact contDiff_const.sub (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hcos : ∀ j : ℕ, ContDiff ℝ n (fun u : Euc d => Real.cos (2 * Real.pi * (j * (a - u) i))) :=
    fun j => Real.contDiff_cos.comp (contDiff_const.mul (contDiff_const.mul hc))
  have hsin : ∀ j : ℕ, ContDiff ℝ n (fun u : Euc d => Real.sin (2 * Real.pi * (j * (a - u) i))) :=
    fun j => Real.contDiff_sin.comp (contDiff_const.mul (contDiff_const.mul hc))
  have h1 : ContDiff ℝ n (fun u : Euc d => ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (j * (a - u) i))) :=
    ContDiff.sum fun j _ => hcos j
  have h2 : ContDiff ℝ n (fun u : Euc d => ∑ j ∈ Finset.range N, Real.sin (2 * Real.pi * (j * (a - u) i))) :=
    ContDiff.sum fun j _ => hsin j
  exact ((h1.pow 2).add (h2.pow 2)).div_const _

open PDE.MFThermalExist in
theorem fejer_approx_family (M δ ε : ℝ) (hM0 : 0 ≤ M) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ v : Torus d → ℝ, Continuous v → (∀ x, |v x| ≤ M) →
      (∀ x z : Torus d, ‖z‖ < δ → |v x - v (x - z)| ≤ ε / 2) →
      ∀ x, |v x - convFun (fejer N) v x| < ε := by
  obtain ⟨C, hC, hCt⟩ := integral_fej1_tail_le δ hδ
  have hlim : Tendsto (fun N : ℕ => (ε / 2)⁻¹ * (2 * M * d * C) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and (eventually_gt_atTop 0))
  refine ⟨N0, fun N hN v hv hMv hmod x => ?_⟩
  obtain ⟨hNlt, hN⟩ := hN0 N hN
  have hF := fejer_continuous (d := d) N
  have hFnn := fejer_nonneg (d := d) N
  have hFint := integral_fejer (d := d) N hN
  set F := fejer (d := d) N with hFdef
  -- the difference as a single integral
  have hvx : ∫ z, F z * v x = v x := by rw [integral_mul_const, hFint, one_mul]
  have hi1 : Integrable fun z => F z * v (x - z) :=
    integrable_of_continuous' (hF.mul (hv.comp (continuous_const.sub continuous_id)))
  have hi2 : Integrable fun z => F z * v x := integrable_of_continuous' (hF.mul continuous_const)
  have hdiff : ∫ z, F z * (v x - v (x - z)) = v x - convFun F v x := by
    calc ∫ z, F z * (v x - v (x - z)) = ∫ z, (F z * v x - F z * v (x - z)) := by
          simp_rw [mul_sub]
      _ = (∫ z, F z * v x) - ∫ z, F z * v (x - z) := integral_sub hi2 hi1
      _ = v x - convFun F v x := by rw [hvx, convFun_eq]
  -- pointwise bound
  set g : Fin d → Torus d → ℝ := fun i => Set.indicator {z : Torus d | δ ≤ ‖z i‖} F with hg
  have hgint : ∀ i, Integrable (g i) := fun i =>
    (integrable_of_continuous' hF).indicator
      (isClosed_le continuous_const ((continuous_apply i).norm)).measurableSet
  have hpt : ∀ z, F z * |v x - v (x - z)| ≤ F z * (ε / 2) + 2 * M * ∑ i, g i z := by
    intro z
    by_cases hz : ‖z‖ < δ
    · have h1 : |v x - v (x - z)| ≤ ε / 2 := by
        exact hmod x z hz
      have : 0 ≤ ∑ i, g i z := Finset.sum_nonneg fun i _ =>
        Set.indicator_nonneg (fun z _ => hFnn z) z
      nlinarith [hFnn z, mul_le_mul_of_nonneg_left h1 (hFnn z)]
    · have hex : ∃ i, δ ≤ ‖z i‖ := by
        by_contra hcon
        push Not at hcon
        exact hz ((pi_norm_lt_iff hδ).mpr hcon)
      obtain ⟨i0, hi0⟩ := hex
      have h1 : |v x - v (x - z)| ≤ 2 * M := by
        have a1 := hMv x
        have a2 := hMv (x - z)
        calc _ ≤ |v x| + |v (x - z)| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      have h2 : g i0 z = F z := Set.indicator_of_mem (by exact hi0) _
      have h3 : g i0 z ≤ ∑ i, g i z :=
        Finset.single_le_sum (f := fun i => g i z)
          (fun i _ => Set.indicator_nonneg (fun z _ => hFnn z) z) (Finset.mem_univ i0)
      have h4 : F z * |v x - v (x - z)| ≤ F z * (2 * M) :=
        mul_le_mul_of_nonneg_left h1 (hFnn z)
      have h5 := mul_nonneg (hFnn z) (show 0 ≤ ε / 2 by positivity)
      calc F z * |v x - v (x - z)| ≤ F z * (2 * M) := h4
        _ = 2 * M * g i0 z := by rw [h2]; ring
        _ ≤ 2 * M * ∑ i, g i z := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ _ := by linarith
  have hcont : Continuous fun z => F z * |v x - v (x - z)| :=
    hF.mul (continuous_const.sub (hv.comp (continuous_const.sub continuous_id))).abs
  have hrhs : Integrable fun z => F z * (ε / 2) + 2 * M * ∑ i, g i z :=
    (integrable_of_continuous' (hF.mul continuous_const)).add
      ((integrable_finsetSum _ fun i _ => hgint i).const_mul _)
  have hint : ∫ z, F z * (ε / 2) + 2 * M * ∑ i, g i z ≤ ε / 2 + 2 * M * d * (C / N) := by
    have hA : Integrable fun z => F z * (ε / 2) := integrable_of_continuous' (hF.mul continuous_const)
    have hB : Integrable fun z => 2 * M * ∑ i, g i z :=
      (integrable_finsetSum _ fun i _ => hgint i).const_mul _
    rw [integral_add hA hB, integral_mul_const, hFint, integral_const_mul,
      integral_finsetSum _ fun i _ => hgint i]
    have : ∀ i, ∫ z, g i z ≤ C / N := fun i => by
      rw [hg]; simp only; rw [integral_fejer_tail N hN δ i]; exact hCt N hN
    have hsum : ∑ i, ∫ z, g i z ≤ d * (C / N) := by
      calc _ ≤ ∑ _i : Fin d, (C / N) := Finset.sum_le_sum fun i _ => this i
        _ = d * (C / N) := by simp
    have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * M by positivity)
    nlinarith
  have hsmall : 2 * M * d * (C / N) < ε / 2 := by
    have h := hNlt
    rw [mul_div_assoc, inv_mul_lt_iff₀ (by positivity)] at h
    have e : 2 * M * d * (C / N) = 2 * M * d * C / N := by ring
    rw [e]; linarith
  calc |v x - convFun F v x| = |∫ z, F z * (v x - v (x - z))| := by rw [hdiff]
    _ ≤ ∫ z, ‖F z * (v x - v (x - z))‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ z, F z * |v x - v (x - z)| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnn z)]
    _ ≤ ∫ z, F z * (ε / 2) + 2 * M * ∑ i, g i z :=
        integral_mono (integrable_of_continuous' hcont) hrhs hpt
    _ < ε := by linarith

/-! ### Uniform regularity data -/

/-- Uniform regularity data extracted from the mean-field hypotheses. -/
structure MFReg (T : ℝ) (ρ : ℝ → Torus d → ℝ) (B : ℝ) (L : ℝ≥0) : Prop where
  dens : ∀ r ∈ Icc 0 T, IsProbDensity (ρ r)
  c1 : ∀ r ∈ Icc 0 T, Torus.IsCk 1 (ρ r)
  bound : ∀ r ∈ Icc 0 T, ∀ x, |ρ r x| ≤ B
  lip : ∀ r ∈ Icc 0 T, LipschitzWith L (Torus.lift (ρ r))

theorem MFReg.of_regular {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ) :
    MFReg T ρ Λ (Real.toNNReal Λ) := by
  refine ⟨hρ.density, fun r hr => (hreg r hr).1.of_le (by norm_num), fun r hr x => ?_, fun r hr => ?_⟩
  · have h := PDE.ET.norm_iteratedFDeriv_le_cbNorm (j := 0) (k := 3) (by norm_num) (hreg r hr).1
      (Torus.rep x)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have e : Torus.lift (ρ r) (Torus.rep x) = ρ r x := by simp [Torus.lift, Torus.mk_rep]
    rw [e] at h
    exact h.trans (hreg r hr).2
  · have h1 : Torus.IsCk 1 (ρ r) := (hreg r hr).1.of_le (by norm_num)
    refine PDE.R2Aux.lipschitzWith_lift_of_bound (PDE.R2Aux.differentiable_lift_of_isCk h1) Λ
      fun y => ?_
    refine (PDE.R2Aux.norm_fderiv_le_cbNorm h1 y).trans ?_
    exact (PDE.cbNorm_mono' (by norm_num) _).trans (hreg r hr).2


/-! ### The weak-form generator in Lebesgue form -/

/-- `w_ψ = β⁻¹Δψ − ∇V·∇ψ`. -/
def wgen (D : DynData d) (ψ : Torus d → ℝ) (x : Torus d) : ℝ :=
  D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)

/-- The generator of the weak form for a density `h`, in Lebesgue form. -/
def genL (D : DynData d) (ψ : Torus d → ℝ) (h : Torus d → ℝ) : ℝ :=
  (∫ x, h x * wgen D ψ x) + (1 / 2 : ℝ) * ∫ x, h x * ∫ y, h y * interKernel D ψ x y

theorem weak_genL (D : DynData d) (ψ : Torus d → ℝ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    pair (withDensityReal ρ) (fun x => D.invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad D.V x) (Torus.grad ψ x))
      + interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) = genL D ψ ρ := by
  unfold genL pair
  rw [interactionPairing_eq_kernel]
  simp_rw [PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  rfl


/-! ### Explicit kernel domination -/

/-- The gradient of a `C²` function is Lipschitz for the torus distance, with an explicit
constant in terms of `cbNorm 2`. -/
theorem grad_lip_explicit {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x y : Torus d) :
    ‖Torus.grad f x - Torus.grad f y‖ ≤ (Torus.cbNorm 2 f * d) * KernelGrad.tdist x y := by
  have hc : ∀ j, |Torus.partialDeriv j f x - Torus.partialDeriv j f y|
      ≤ Torus.cbNorm 2 f * KernelGrad.tdist x y := fun j =>
    PDE.R2Aux.isLipschitz_partialDeriv hf j x y
  have hv := Duality.norm_euc_le_sum (Torus.grad f x - Torus.grad f y)
  calc ‖Torus.grad f x - Torus.grad f y‖ ≤ ∑ j, |(Torus.grad f x - Torus.grad f y) j| := hv
    _ ≤ ∑ _j : Fin d, Torus.cbNorm 2 f * KernelGrad.tdist x y := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [PiLp.sub_apply, Duality.grad_apply_eq_partialDeriv, Duality.grad_apply_eq_partialDeriv]
        exact hc j
    _ = (Torus.cbNorm 2 f * d) * KernelGrad.tdist x y := by simp; ring

/-- A kernel domination constant depending only on a bound for `cbNorm 2 ψ`. -/
theorem interKernel_dom (hd : 1 ≤ d) (D : DynData d) (Cb : ℝ) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → Torus.cbNorm 2 ψ ≤ Cb →
      ∀ x y : Torus d, |interKernel D ψ x y| ≤ K0 * (‖x - y‖ ^ (-D.s) + d) := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd D.hs0 D.hsd
  obtain ⟨CM, hCM0, hCM⟩ := Duality.exists_matVec_bound D.M
  have hC0 := hG.hC0
  have hCb : 0 ≤ Cb ∨ True := Or.inr trivial
  refine ⟨CM * (max Cb 0 * d) * C, by positivity, fun ψ hψ hcb x y => ?_⟩
  have hK0 : 0 ≤ CM * (max Cb 0 * d) * C := by positivity
  unfold interKernel
  split_ifs with hxy
  · rw [abs_zero]
    exact mul_nonneg hK0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hG' := hG.norm_mul_tdist_le (x - y) hz
    rw [← KernelGrad.tdist_eq_sub_zero] at hG'
    have hL := grad_lip_explicit hψ x y
    have hcb0 : Torus.cbNorm 2 ψ ≤ max Cb 0 := hcb.trans (le_max_left _ _)
    have hL0 : 0 ≤ max Cb 0 * d := by positivity
    have hL' : ‖Torus.grad ψ x - Torus.grad ψ y‖ ≤ (max Cb 0 * d) * KernelGrad.tdist x y :=
      hL.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcb0 (Nat.cast_nonneg _))
        (KernelGrad.tdist_nonneg x y))
    have e1 : ‖Torus.grad ψ x - Torus.grad ψ y‖ * ‖Torus.matVec D.M (periodicRieszGrad d D.s (x - y))‖
        ≤ ((max Cb 0 * d) * KernelGrad.tdist x y) * (CM * ‖periodicRieszGrad d D.s (x - y)‖) :=
      mul_le_mul hL' (hCM _) (norm_nonneg _) (mul_nonneg hL0 (KernelGrad.tdist_nonneg x y))
    calc |inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
          (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))|
        ≤ ‖Torus.grad ψ x - Torus.grad ψ y‖ * ‖Torus.matVec D.M (periodicRieszGrad d D.s (x - y))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ((max Cb 0 * d) * KernelGrad.tdist x y) * (CM * ‖periodicRieszGrad d D.s (x - y)‖) := e1
      _ = CM * (max Cb 0 * d) * (KernelGrad.tdist x y * ‖periodicRieszGrad d D.s (x - y)‖) := by ring
      _ ≤ CM * (max Cb 0 * d) * (C * (‖x - y‖ ^ (-D.s) + d)) :=
          mul_le_mul_of_nonneg_left hG' (mul_nonneg hCM0 hL0)
      _ = _ := by ring


theorem IsProbDensity.integrable' {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  norm_num at this

theorem integrable_kdom (hd : 1 ≤ d) (D : DynData d) (K0 : ℝ) :
    Integrable (fun z : Torus d => K0 * (‖z‖ ^ (-D.s) + d)) :=
  ((KernelGrad.integrable_norm_rpow_neg (by omega) D.hsd).add (integrable_const _)).const_mul K0

theorem continuous_wgen (D : DynData d) (hV : Torus.IsCk 2 D.V) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) : Continuous (wgen D ψ) := by
  unfold wgen
  exact (continuous_const.mul (PDE.ClassicalAux.continuous_laplacian hψ)).sub
    ((Duality.grad_continuous hV).inner (Duality.grad_continuous hψ))

/-- `∫ h(y) K(x,y) dy` is bounded when `K` is dominated by `K0 (‖x-y‖^{-s}+d)`. -/
theorem abs_integral_mul_kernel_le (hd : 1 ≤ d) (D : DynData d) {K0 : ℝ}
    {h : Torus d → ℝ} {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    {K : Torus d → Torus d → ℝ}
    (hK : ∀ x y, |K x y| ≤ K0 * (‖x - y‖ ^ (-D.s) + d)) (x : Torus d) :
    |∫ y, h y * K x y| ≤ B * ∫ z : Torus d, K0 * (‖z‖ ^ (-D.s) + d) := by
  have hg := (integrable_kdom hd D K0).comp_sub_left x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  have hint : Integrable (fun y => B * (K0 * (‖x - y‖ ^ (-D.s) + d))) := hg.const_mul B
  have h1 : ‖∫ y, h y * K x y‖ ≤ ∫ y, B * (K0 * (‖x - y‖ ^ (-D.s) + d)) := by
    refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB y) (hK x y) (abs_nonneg _) hB0
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_sub_left_eq_self (fun z : Torus d => K0 * (‖z‖ ^ (-D.s) + d)) volume x

theorem abs_integral_density_mul_le {h : Torus d → ℝ} (hh : IsProbDensity h) {g : Torus d → ℝ} {W : ℝ}
    (hg : ∀ x, |g x| ≤ W) : |∫ x, h x * g x| ≤ W := by
  have hint : Integrable (fun x => h x * W) := hh.integrable'.mul_const W
  have h1 : ‖∫ x, h x * g x‖ ≤ ∫ x, h x * W := by
    refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh.nonneg x)]
    exact mul_le_mul_of_nonneg_left (hg x) (hh.nonneg x)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [integral_mul_const, hh.integral_one, one_mul]

theorem genL_bound (hd : 1 ≤ d) (D : DynData d) (hV : Torus.IsCk 2 D.V) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) (B : ℝ) :
    ∃ K : ℝ, ∀ h : Torus d → ℝ, IsProbDensity h → (∀ x, h x ≤ B) → |genL D ψ h| ≤ K := by
  obtain ⟨W, hW0, hW⟩ := Duality.bounded_of_continuous (continuous_wgen D hV hψ)
  obtain ⟨K0, hK00, hK0⟩ := interKernel_dom hd D (Torus.cbNorm 2 ψ)
  set cK : ℝ := ∫ z : Torus d, K0 * (‖z‖ ^ (-D.s) + d) with hcK
  refine ⟨W + (1 / 2 : ℝ) * (B * cK), fun h hh hB => ?_⟩
  unfold genL
  have h1 := abs_integral_density_mul_le hh hW
  have h2 : ∀ x, |∫ y, h y * interKernel D ψ x y| ≤ B * cK := fun x =>
    abs_integral_mul_kernel_le hd D (fun y => by rw [abs_of_nonneg (hh.nonneg y)]; exact hB y)
      (fun x y => hK0 ψ hψ le_rfl x y) x
  have h3 := abs_integral_density_mul_le hh h2
  calc |(∫ x, h x * wgen D ψ x) + (1 / 2 : ℝ) * ∫ x, h x * ∫ y, h y * interKernel D ψ x y|
      ≤ |∫ x, h x * wgen D ψ x| + |(1 / 2 : ℝ) * ∫ x, h x * ∫ y, h y * interKernel D ψ x y| :=
        abs_add_le _ _
    _ ≤ W + (1 / 2 : ℝ) * (B * cK) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h3 (by norm_num))


/-! ### The weak form with the Lebesgue-form generator -/

/-- The weak formulation together with uniform regularity. -/
structure MFWeak (D : DynData d) (T : ℝ) (ρ : ℝ → Torus d → ℝ) (B : ℝ) (L : ℝ≥0) : Prop where
  reg : MFReg T ρ B L
  weak : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ t ∈ Icc 0 T,
    pair (withDensityReal (ρ t)) ψ - pair (withDensityReal (ρ 0)) ψ =
      ∫ r in Icc 0 t, genL D ψ (ρ r)

theorem MFWeak.of_regular {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ) :
    MFWeak D T ρ Λ (Real.toNNReal Λ) := by
  refine ⟨MFReg.of_regular hρ hreg, fun ψ hψ t ht => ?_⟩
  rw [hρ.weak ψ hψ t ht]
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  exact weak_genL D ψ (hρ.density r ⟨hr.1, hr.2.trans ht.2⟩)

theorem MFReg.le_bound {T : ℝ} {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (h : MFReg T ρ B L)
    {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) : ρ r x ≤ B :=
  (le_abs_self _).trans (h.bound r hr x)

/-- Measurability of `r ↦ ⟨ψ, μ_r⟩`: it is Lipschitz where the generator is integrable and
constant afterwards. -/
theorem measurable_pair_clamp (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Measurable (fun r => pair (withDensityReal (ρ (clampTI T r))) ψ) := by
  obtain ⟨K, hK⟩ := genL_bound hd D hV hψ B
  have hKr : ∀ r ∈ Icc 0 T, |genL D ψ (ρ r)| ≤ K := fun r hr =>
    hK _ (W.reg.dens r hr) (fun x => W.reg.le_bound hr x)
  set g : ℝ → ℝ := fun r => genL D ψ (ρ r) with hg
  set E : Set ℝ := {t | t ∈ Icc 0 T ∧ IntegrableOn g (Icc 0 t)} with hE
  set Λ' : ℝ → ℝ := fun t => ∫ r in Icc 0 t, g r with hΛ
  classical
  have hEconn : E.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩
    exact hy.2.mono_set (Icc_subset_Icc_right hz.2)
  have hEm : MeasurableSet E := hEconn.measurableSet
  have hLip : ∀ s ∈ E, ∀ t ∈ E, s ≤ t → |Λ' t - Λ' s| ≤ K * (t - s) := by
    intro s hs t ht hst
    have hs0 : 0 ≤ s := hs.1.1
    have hsplit : Icc 0 t = Icc 0 s ∪ Ioc s t := (Set.Icc_union_Ioc_eq_Icc hs0 hst).symm
    have hdisj : Disjoint (Icc 0 s) (Ioc s t) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.2 hx'.1)
    have hi2 : IntegrableOn g (Ioc s t) := ht.2.mono_set (by rw [hsplit]; exact subset_union_right)
    have hsum : Λ' t = Λ' s + ∫ r in Ioc s t, g r := by
      simp only [hΛ]
      rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hs.2 hi2]
    have hb : ‖∫ r in Ioc s t, g r‖ ≤ K * volume.real (Ioc s t) := by
      refine norm_setIntegral_le_of_norm_le_const (by simp) fun r hr => ?_
      rw [Real.norm_eq_abs]
      exact hKr r ⟨hs0.trans hr.1.le, hr.2.trans ht.1.2⟩
    rw [Real.volume_real_Ioc_of_le hst] at hb
    rw [hsum, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact hb
  have hcontE : ContinuousOn Λ' E := by
    have hK0 : 0 ≤ K := by
      have := hKr 0 ⟨le_rfl, hT⟩
      exact (abs_nonneg _).trans this
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal K) ?_
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total s t with hst | hst
    · rw [abs_sub_comm, abs_of_nonpos (by linarith : s - t ≤ 0)]
      have := hLip s hs t ht hst
      linarith [this]
    · rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      have := hLip t ht s hs hst
      linarith [this]
  have hpw : Measurable (E.piecewise Λ' (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hcontE continuousOn_const hEm
  have hfun : (fun r => pair (withDensityReal (ρ (clampTI T r))) ψ) =
      fun r => pair (withDensityReal (ρ 0)) ψ + E.piecewise Λ' (fun _ => 0) (clampTI T r) := by
    funext r
    have hr : clampTI T r ∈ Icc 0 T := clampTI_mem hT r
    have hw := W.weak ψ hψ _ hr
    by_cases hmem : clampTI T r ∈ E
    · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
      linarith [hw]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
      have : ¬ IntegrableOn g (Icc 0 (clampTI T r)) := fun hi => hmem ⟨hr, hi⟩
      rw [integral_undef this] at hw
      linarith [hw]
  rw [hfun]
  exact measurable_const.add (hpw.comp (continuous_clampTI T).measurable)


/-! ### Fejér test functions -/

open PDE.MFThermalExist in
/-- The Fejér test function `y ↦ F_N(x - y)`. -/
def fejerTest (N : ℕ) (x : Torus d) : Torus d → ℝ := fun y => fejer N (x - y)

theorem fejerTest_isCk (n : ℕ) (N : ℕ) (x : Torus d) :
    Torus.IsCk n (fejerTest N x) := by
  unfold Torus.IsCk
  have e : Torus.lift (fejerTest N x) = fun u : Euc d => PDE.MFThermalExist.fejer N (Torus.mk (Torus.rep x - u)) := by
    funext u
    unfold Torus.lift fejerTest
    simp only [Function.comp]
    rw [KernelGrad.mk_sub, Torus.mk_rep]
  rw [e]
  exact contDiff_fejer_lift n N (Torus.rep x)

theorem pair_fejerTest {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (N : ℕ) (x : Torus d) :
    pair (withDensityReal ρ) (fejerTest N x) = convFun (PDE.MFThermalExist.fejer N) ρ x := by
  unfold pair
  rw [PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  unfold convFun fejerTest
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

theorem measurable_rho_clamp (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) (x : Torus d) :
    Measurable (fun r => ρ (clampTI T r) x) := by
  have hm : ∀ N : ℕ, Measurable (fun r => convFun (PDE.MFThermalExist.fejer N) (ρ (clampTI T r)) x) := by
    intro N
    have h := measurable_pair_clamp hd hV hT W (fejerTest_isCk 2 N x)
    have e : (fun r => convFun (PDE.MFThermalExist.fejer N) (ρ (clampTI T r)) x) =
        fun r => pair (withDensityReal (ρ (clampTI T r))) (fejerTest N x) :=
      funext fun r => (pair_fejerTest (W.reg.dens _ (clampTI_mem hT r)) N x).symm
    rw [e]
    exact h
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 fun r => ?_)
  have hc : Continuous (ρ (clampTI T r)) :=
    KernelGrad.isCk_continuous (W.reg.c1 _ (clampTI_mem hT r))
  exact (PDE.MFThermalExist.fejer_tendsto_uniformly _ hc).tendsto_at x


theorem measurable_interKernel {D : DynData d} {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Measurable (fun p : Torus d × Torus d => interKernel D ψ p.1 p.2) := by
  have e : (fun p : Torus d × Torus d => interKernel D ψ p.1 p.2) =
      fun p => 2 * Duality.pairKernelB ψ D.M D.s p.1 p.2 :=
    funext fun p => interKernel_eq_pairKernelB D ψ p.1 p.2
  rw [e]
  exact (Duality.measurable_pairKernelB hψ D.M D.hsd).const_mul 2

theorem measurable_rho_joint (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) :
    Measurable (fun p : ℝ × Torus d => ρ (clampTI T p.1) p.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Torus d) (r : ℝ) => ρ (clampTI T r) x)
    (fun r => KernelGrad.isCk_continuous (W.reg.c1 _ (clampTI_mem hT r)))
    (fun x => measurable_rho_clamp hd hV hT W x)
  exact h.comp measurable_swap

theorem measurable_genL_clamp (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Measurable (fun r => genL D ψ (ρ (clampTI T r))) := by
  have hρj := measurable_rho_joint hd hV hT W
  have hw : Measurable (wgen D ψ) := (continuous_wgen D hV hψ).measurable
  have hK := measurable_interKernel (D := D) hψ
  have h1 : Measurable (fun r => ∫ x, ρ (clampTI T r) x * wgen D ψ x) := by
    have hF : Measurable (fun p : ℝ × Torus d => ρ (clampTI T p.1) p.2 * wgen D ψ p.2) :=
      hρj.mul (hw.comp measurable_snd)
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  have hG : Measurable (fun q : ℝ × Torus d => ∫ y, ρ (clampTI T q.1) y * interKernel D ψ q.2 y) := by
    have hF : Measurable (fun p : (ℝ × Torus d) × Torus d =>
        ρ (clampTI T p.1.1) p.2 * interKernel D ψ p.1.2 p.2) := by
      refine (hρj.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)).mul ?_
      exact hK.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  have h2 : Measurable (fun r => ∫ x, ρ (clampTI T r) x * ∫ y, ρ (clampTI T r) y * interKernel D ψ x y) := by
    have hF : Measurable (fun p : ℝ × Torus d =>
        ρ (clampTI T p.1) p.2 * ∫ y, ρ (clampTI T p.1) y * interKernel D ψ p.2 y) :=
      hρj.mul hG
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  unfold genL
  exact h1.add (h2.const_mul _)


theorem integrableOn_genL (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {b : ℝ} (hb : b ∈ Icc 0 T) :
    IntegrableOn (fun r => genL D ψ (ρ r)) (Icc 0 b) := by
  obtain ⟨K, hK⟩ := genL_bound hd D hV hψ B
  have hm := measurable_genL_clamp hd hV hT W hψ
  have hcl : ∀ r ∈ Icc 0 b, clampTI T r = r := fun r hr =>
    clampTI_of_mem ⟨hr.1, hr.2.trans hb.2⟩
  refine Integrable.of_bound (μ := volume.restrict (Icc 0 b)) (C := K) ?_ ?_
  · refine (hm.aestronglyMeasurable (μ := volume.restrict (Icc 0 b))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hcl r hr]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs]
    exact hK _ (W.reg.dens r ⟨hr.1, hr.2.trans hb.2⟩) (fun x => W.reg.le_bound ⟨hr.1, hr.2.trans hb.2⟩ x)

theorem weak_interval (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    pair (withDensityReal (ρ b)) ψ - pair (withDensityReal (ρ a)) ψ
      = ∫ r in a..b, genL D ψ (ρ r) := by
  have hbT : b ∈ Icc 0 T := ⟨ha.trans hab, hb⟩
  have haT : a ∈ Icc 0 T := ⟨ha, hab.trans hb⟩
  have hsplit : Icc 0 b = Icc 0 a ∪ Ioc a b := (Set.Icc_union_Ioc_eq_Icc ha hab).symm
  have hdisj : Disjoint (Icc 0 a) (Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx'.1)
  have hi1 := integrableOn_genL hd hV hT W hψ haT
  have hi2 : IntegrableOn (fun r => genL D ψ (ρ r)) (Ioc a b) :=
    (integrableOn_genL hd hV hT W hψ hbT).mono_set (by rw [hsplit]; exact subset_union_right)
  have h1 := W.weak ψ hψ b hbT
  have h2 := W.weak ψ hψ a haT
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hi1 hi2] at h1
  rw [intervalIntegral.integral_of_le hab]
  linarith

theorem pair_lipschitz_time (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T,
      |pair (withDensityReal (ρ b)) ψ - pair (withDensityReal (ρ a)) ψ| ≤ K * |b - a| := by
  obtain ⟨K, hK⟩ := genL_bound hd D hV hψ B
  have hK0 : 0 ≤ K := (abs_nonneg _).trans
    (hK _ (W.reg.dens 0 ⟨le_rfl, hT⟩) (fun x => W.reg.le_bound ⟨le_rfl, hT⟩ x))
  have key : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b →
      |pair (withDensityReal (ρ b)) ψ - pair (withDensityReal (ρ a)) ψ| ≤ K * |b - a| := by
    intro a ha b hb hab
    rw [weak_interval hd hV hT W hψ ha.1 hab hb.2, abs_of_nonneg (sub_nonneg.2 hab)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun r => genL D ψ (ρ r)) (C := K) (fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        rw [Real.norm_eq_abs]
        exact hK _ (W.reg.dens r ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩)
          (fun x => W.reg.le_bound ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩ x))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
    linarith
  refine ⟨K, hK0, fun a ha b hb => ?_⟩
  rcases le_total a b with hab | hab
  · exact key a ha b hb hab
  · rw [abs_sub_comm, abs_sub_comm b a]
    exact key b hb a ha hab


theorem abs_rho_sub_le {T : ℝ} {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFReg T ρ B L)
    {r : ℝ} (hr : r ∈ Icc 0 T) (x z : Torus d) :
    |ρ r x - ρ r (x - z)| ≤ L * d * ‖z‖ := by
  have hL := isLipschitz_of_lift_lipschitz (W.lip r hr) x (x - z)
  have h2 := Duality.tdist_le_norm_mul x (x - z)
  rw [sub_sub_cancel] at h2
  calc |ρ r x - ρ r (x - z)| ≤ L * KernelGrad.tdist x (x - z) := hL
    _ ≤ L * (d * ‖z‖) := mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg _)
    _ = L * d * ‖z‖ := by ring

theorem continuousOn_rho (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) (x : Torus d) :
    ContinuousOn (fun r => ρ r x) (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro r0 hr0 ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (W.reg.bound 0 ⟨le_rfl, hT⟩ x)
  have hLd : 0 < (L : ℝ) * d + 1 := by positivity
  set δF : ℝ := (ε / 3) / 2 / ((L : ℝ) * d + 1) with hδF
  have hδF0 : 0 < δF := by positivity
  obtain ⟨N0, hN0⟩ := fejer_approx_family B δF (ε / 3) hB0 hδF0 hε3
  obtain ⟨K, hK0, hK⟩ := pair_lipschitz_time hd hV hT W (fejerTest_isCk 2 N0 x)
  refine ⟨ε / 3 / (K + 1), by positivity, fun r hr hrr => ?_⟩
  have happ : ∀ r' ∈ Icc 0 T, |ρ r' x - convFun (PDE.MFThermalExist.fejer N0) (ρ r') x| < ε / 3 := by
    intro r' hr'
    refine hN0 N0 le_rfl (ρ r') (KernelGrad.isCk_continuous (W.reg.c1 r' hr')) (W.reg.bound r' hr')
      (fun a z hz => ?_) x
    have h1 := abs_rho_sub_le W.reg hr' a z
    refine h1.trans ?_
    have : (L : ℝ) * d * ‖z‖ ≤ (L * d + 1) * δF := by
      have : ‖z‖ ≤ δF := hz.le
      nlinarith [mul_nonneg (NNReal.coe_nonneg L) (Nat.cast_nonneg d : (0:ℝ) ≤ d), norm_nonneg z]
    refine this.trans ?_
    rw [hδF]
    field_simp
    exact le_rfl
  have hmid := hK r0 hr0 r hr
  rw [pair_fejerTest (W.reg.dens r hr), pair_fejerTest (W.reg.dens r0 hr0)] at hmid
  have hd1 := happ r hr
  have hd2 := happ r0 hr0
  rw [Real.dist_eq] at hrr ⊢
  have hKt : K * |r - r0| < ε / 3 := by
    have : |r - r0| < ε / 3 / (K + 1) := hrr
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg (r - r0)]
  have hd3 : |convFun (PDE.MFThermalExist.fejer N0) (ρ r0) x - ρ r0 x| < ε / 3 := by
    rw [abs_sub_comm]; exact hd2
  calc |ρ r x - ρ r0 x|
      = |(ρ r x - convFun (PDE.MFThermalExist.fejer N0) (ρ r) x)
        + (convFun (PDE.MFThermalExist.fejer N0) (ρ r) x - convFun (PDE.MFThermalExist.fejer N0) (ρ r0) x)
        + (convFun (PDE.MFThermalExist.fejer N0) (ρ r0) x - ρ r0 x)| := by ring_nf
    _ ≤ |ρ r x - convFun (PDE.MFThermalExist.fejer N0) (ρ r) x|
        + |convFun (PDE.MFThermalExist.fejer N0) (ρ r) x - convFun (PDE.MFThermalExist.fejer N0) (ρ r0) x|
        + |convFun (PDE.MFThermalExist.fejer N0) (ρ r0) x - ρ r0 x| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith


theorem norm_grad_le_cbNorm_two {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (x : Torus d) :
    ‖Torus.grad φ x‖ ≤ Torus.cbNorm 2 φ := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  unfold Torus.grad gradient
  rw [LinearIsometryEquiv.norm_map]
  exact (PDE.R2Aux.norm_fderiv_le_cbNorm h1 _).trans (PDE.cbNorm_mono' (by norm_num) _)

theorem abs_laplacian_le_cbNorm {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (x : Torus d) :
    |Torus.laplacian φ x| ≤ d * Torus.cbNorm 2 φ := by
  have hx : Torus.laplacian φ x = Torus.laplacian φ (Torus.mk (Torus.rep x)) := by rw [Torus.mk_rep]
  rw [hx, ← sum_lap_eq]
  set H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x) with hH
  have hb : ∀ j : Fin d, |H (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)|
      ≤ Torus.cbNorm 2 φ := by
    intro j
    have h2 := PDE.ET.norm_iteratedFDeriv_le_cbNorm (j := 2) (k := 2) le_rfl hφ (Torus.rep x)
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h2
    have he : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
    have h3 : ‖H (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)‖ ≤ ‖H‖ := by
      calc _ ≤ ‖H (EuclideanSpace.single j 1)‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
            (H (EuclideanSpace.single j 1)).le_opNorm _
        _ ≤ (‖H‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖) * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
            mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
        _ = ‖H‖ := by rw [he]; ring
    rw [← Real.norm_eq_abs]
    exact h3.trans h2
  calc _ ≤ ∑ j : Fin d, |H (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, Torus.cbNorm 2 φ := Finset.sum_le_sum fun j _ => hb j
    _ = _ := by simp

theorem iter_bound {t : ℝ} (_ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) {j : ℕ}
    (hj : j ≤ 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc 0 t, ∀ y : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (f r)) y‖ ≤ C := by
  have hK : IsCompact (Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun p : ℝ × Euc d => ‖iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2‖)
      (Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d)) :=
    ((hf.contOn_iter hj).mono (Set.prod_mono subset_rfl (Set.subset_univ _))).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun r hr y => ?_⟩
  have hper : iteratedFDeriv ℝ j (Torus.lift (f r)) (Torus.rep (Torus.mk y))
      = iteratedFDeriv ℝ j (Torus.lift (f r)) y :=
    periodic_rep_mk (fun y => iteratedFDeriv ℝ j (Torus.lift (f r)) y)
      (fun x n => Torus.iteratedFDeriv_lift_periodic (f r) j x n) y
  have hmem : (r, Torus.rep (Torus.mk y)) ∈ Icc 0 t ×ˢ Metric.closedBall (0 : Euc d) (Real.sqrt d) :=
    ⟨hr, mem_closedBall_zero_iff.2 (rep_norm_le _)⟩
  have := hC _ hmem
  rw [norm_norm] at this
  rw [← hper]
  exact this.trans (le_max_left _ _)

theorem cbNorm2_bound {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc 0 t, Torus.cbNorm 2 (f r) ≤ C := by
  obtain ⟨C0, hC00, hC0⟩ := iter_bound ht hf (j := 0) (by norm_num)
  obtain ⟨C1, hC10, hC1⟩ := iter_bound ht hf (j := 1) (by norm_num)
  obtain ⟨C2, hC20, hC2⟩ := iter_bound ht hf (j := 2) (by norm_num)
  refine ⟨C0 + C1 + C2, by positivity, fun r hr => ?_⟩
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h : ∀ (j : ℕ) (C : ℝ), 0 ≤ C → (∀ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (f r)) y‖ ≤ C) →
      ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (f r)) y‖ ≤ C :=
    fun j C hC h => Real.iSup_le h hC
  have e0 := h 0 C0 hC00 (hC0 r hr)
  have e1 := h 1 C1 hC10 (hC1 r hr)
  have e2 := h 2 C2 hC20 (hC2 r hr)
  linarith


/-! ### Continuity of the test function along the clamped time -/

theorem continuous_iter_clamp {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft)
    {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (Torus.lift (f (clampTI t p.1))) p.2) := by
  have hq : Continuous fun p : ℝ × Euc d => (clampTI t p.1, p.2) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  exact ContinuousOn.comp_continuous
    (g := fun p : ℝ × Euc d => iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2)
    (f := fun p : ℝ × Euc d => (clampTI t p.1, p.2)) (hf.contOn_iter hj) hq
    (fun p => (⟨clampTI_mem ht p.1, Set.mem_univ _⟩ : (clampTI t p.1, p.2) ∈ Set.Icc 0 t ×ˢ Set.univ))

theorem continuous_grad_clamp_at {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (x : Torus d) :
    Continuous (fun a => Torus.grad (f (clampTI t a)) x) :=
  (continuous_gradient_clamp ht hf).comp (continuous_id.prodMk continuous_const)

theorem continuous_lap_clamp_at {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (x : Torus d) :
    Continuous (fun a => Torus.laplacian (f (clampTI t a)) x) := by
  have e : (fun a => Torus.laplacian (f (clampTI t a)) x) = fun a => ∑ i : Fin d,
      iteratedFDeriv ℝ 2 (Torus.lift (f (clampTI t a))) (Torus.rep x)
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    funext a
    unfold Torus.laplacian
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp [EuclideanSpace.basisFun_apply]
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 := (continuous_iter_clamp ht hf (j := 2) le_rfl).comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => Torus.rep x))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]).continuous.comp h1


/-! ### Continuity of nested parameter integrals -/

theorem continuous_nested (hd : 1 ≤ d) (D : DynData d) {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (R : X → Torus d → ℝ) (K : X → Torus d → Torus d → ℝ) {B K0 : ℝ}
    (hR : ∀ p x, |R p x| ≤ B) (hRc : ∀ x, Continuous fun p => R p x)
    (hRm : ∀ p, Measurable (R p))
    (hKc : ∀ x y, Continuous fun p => K p x y)
    (hKm : ∀ p, Measurable (fun q : Torus d × Torus d => K p q.1 q.2))
    (hK : ∀ p x y, |K p x y| ≤ K0 * (‖x - y‖ ^ (-D.s) + d)) :
    Continuous fun p => ∫ x, R p x * ∫ y, R p y * K p x y := by
  set cK : ℝ := ∫ z : Torus d, K0 * (‖z‖ ^ (-D.s) + d) with hcK
  have hI : ∀ x, Continuous fun p => ∫ y, R p y * K p x y := by
    intro x
    refine continuous_of_dominated (bound := fun y => B * (K0 * (‖x - y‖ ^ (-D.s) + d))) ?_ ?_ ?_ ?_
    · intro p
      exact ((hRm p).mul ((hKm p).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    · intro p
      refine Filter.Eventually.of_forall fun y => ?_
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hR p y)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hR p y) (hK p x y) (abs_nonneg _) hB0
    · exact ((integrable_kdom hd D K0).comp_sub_left x).const_mul B
    · exact Filter.Eventually.of_forall fun y => (hRc y).mul (hKc x y)
  have hIb : ∀ p x, |∫ y, R p y * K p x y| ≤ B * cK := fun p x =>
    abs_integral_mul_kernel_le hd D (hR p) (hK p) x
  refine continuous_of_dominated (bound := fun _ => B * (B * cK)) ?_ ?_ (integrable_const _) ?_
  · intro p
    have hF : Measurable (fun q : Torus d × Torus d => R p q.2 * K p q.1 q.2) :=
      ((hRm p).comp measurable_snd).mul (hKm p)
    have hI' : Measurable (fun x => ∫ y, R p y * K p x y) :=
      (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
    exact ((hRm p).mul hI').aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun x => ?_
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hR p x)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hR p x) (hIb p x) (abs_nonneg _) hB0
  · exact Filter.Eventually.of_forall fun x => (hRc x).mul (hI x)


/-! ### Joint continuity of the two time-slice functionals -/

theorem rho_clamp_mem {T t : ℝ} (ht : t ∈ Icc 0 T) (b : ℝ) : clampTI t b ∈ Icc 0 T :=
  ⟨(clampTI_mem ht.1 b).1, (clampTI_mem ht.1 b).2.trans ht.2⟩

theorem continuous_rho_clamp_at (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) (y : Torus d) : Continuous fun b => ρ (clampTI t b) y :=
  (continuousOn_rho hd hV hT W y).comp_continuous (continuous_clampTI t) (rho_clamp_mem ht)

theorem continuous_ft_clamp_y {t : ℝ} (ht0 : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (u : ℝ) : Continuous fun y => ft (clampTI t u) y :=
  hf.cont_time_deriv.comp (continuous_const.prodMk continuous_id : Continuous fun y : Torus d =>
    ((⟨clampTI t u, clampTI_mem ht0 u⟩ : Icc (0 : ℝ) t), y))

theorem continuous_ft_clamp_u {t : ℝ} (ht0 : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (y : Torus d) : Continuous fun u => ft (clampTI t u) y :=
  hf.cont_time_deriv.comp ((Continuous.subtype_mk (continuous_clampTI t) (clampTI_mem ht0)).prodMk
    continuous_const)

theorem continuous_G1 (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    Continuous (fun p : ℝ × ℝ =>
      pair (withDensityReal (ρ (clampTI t p.2))) (ft (clampTI t p.1))) := by
  obtain ⟨Fm, hFm⟩ := isCompact_univ.exists_bound_of_continuousOn hf.cont_time_deriv.continuousOn
  have e : (fun p : ℝ × ℝ => pair (withDensityReal (ρ (clampTI t p.2))) (ft (clampTI t p.1))) =
      fun p => ∫ y, ρ (clampTI t p.2) y * ft (clampTI t p.1) y := by
    funext p
    unfold pair
    exact PDE.MFPairing.integral_withDensityReal (W.reg.dens _ (rho_clamp_mem ht _)).measurable
      (W.reg.dens _ (rho_clamp_mem ht _)).nonneg _
  rw [e]
  refine continuous_of_dominated (bound := fun _ => B * Fm) ?_ ?_ (integrable_const _) ?_
  · intro p
    have h1 : Continuous (ρ (clampTI t p.2)) :=
      KernelGrad.isCk_continuous (W.reg.c1 _ (rho_clamp_mem ht _))
    exact (h1.mul (continuous_ft_clamp_y ht.1 hf p.1)).aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun y => ?_
    have h1 := W.reg.bound _ (rho_clamp_mem ht p.2) y
    have h2 := hFm (⟨clampTI t p.1, clampTI_mem ht.1 p.1⟩, y) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at h2 ⊢
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  · exact Filter.Eventually.of_forall fun y =>
      ((continuous_rho_clamp_at hd hV hT W ht y).comp continuous_snd).mul
        ((continuous_ft_clamp_u ht.1 hf y).comp continuous_fst)


theorem continuous_interKernel_clamp {D : DynData d} {t : ℝ} (ht0 : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (x y : Torus d) :
    Continuous fun a => interKernel D (f (clampTI t a)) x y := by
  unfold interKernel
  by_cases hxy : x = y
  · simp only [hxy, ite_true]
    exact continuous_const
  · simp only [hxy, ite_false]
    exact ((continuous_grad_clamp_at ht0 hf x).sub (continuous_grad_clamp_at ht0 hf y)).inner
      continuous_const

theorem continuous_G2 (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    Continuous (fun p : ℝ × ℝ => genL D (f (clampTI t p.2)) (ρ (clampTI t p.1))) := by
  obtain ⟨Cb, hCb0, hCb⟩ := cbNorm2_bound ht.1 hf
  obtain ⟨GV, hGV0, hGV⟩ := Duality.bounded_of_continuous (Duality.grad_continuous hV).norm
  have hc2 : ∀ a, Torus.IsCk 2 (f (clampTI t a)) := fun a => hf.c2 _ (clampTI_mem ht.1 a)
  have hcb : ∀ a, Torus.cbNorm 2 (f (clampTI t a)) ≤ Cb := fun a => hCb _ (clampTI_mem ht.1 a)
  have hρc : ∀ u, Continuous (ρ (clampTI t u)) := fun u =>
    KernelGrad.isCk_continuous (W.reg.c1 _ (rho_clamp_mem ht u))
  unfold genL
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · -- first part
    refine continuous_of_dominated
      (bound := fun _ => B * (|D.invβ| * (d * Cb) + GV * Cb)) ?_ ?_ (integrable_const _) ?_
    · intro p
      exact ((hρc p.1).mul (continuous_wgen D hV (hc2 p.2))).aestronglyMeasurable
    · intro p
      refine Filter.Eventually.of_forall fun x => ?_
      have h1 := W.reg.bound _ (rho_clamp_mem ht p.1) x
      have h2 : |wgen D (f (clampTI t p.2)) x| ≤ |D.invβ| * (d * Cb) + GV * Cb := by
        unfold wgen
        calc |D.invβ * Torus.laplacian (f (clampTI t p.2)) x
              - inner ℝ (Torus.grad D.V x) (Torus.grad (f (clampTI t p.2)) x)|
            ≤ |D.invβ * Torus.laplacian (f (clampTI t p.2)) x|
              + |inner ℝ (Torus.grad D.V x) (Torus.grad (f (clampTI t p.2)) x)| := abs_sub _ _
          _ ≤ |D.invβ| * (d * Cb) + GV * Cb := by
              refine add_le_add ?_ ?_
              · rw [abs_mul]
                refine mul_le_mul_of_nonneg_left ((abs_laplacian_le_cbNorm (hc2 p.2) x).trans ?_)
                  (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left (hcb p.2) (Nat.cast_nonneg _)
              · refine (abs_real_inner_le_norm _ _).trans ?_
                have h3 := hGV x
                rw [abs_norm] at h3
                exact mul_le_mul h3 ((norm_grad_le_cbNorm_two (hc2 p.2) x).trans (hcb p.2))
                  (norm_nonneg _) hGV0
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine ((continuous_rho_clamp_at hd hV hT W ht x).comp continuous_fst).mul ?_
      unfold wgen
      exact (continuous_const.mul ((continuous_lap_clamp_at ht.1 hf x).comp continuous_snd)).sub
        (continuous_const.inner ((continuous_grad_clamp_at ht.1 hf x).comp continuous_snd))
  · -- second part
    obtain ⟨K0, hK00, hK0⟩ := interKernel_dom hd D Cb
    refine continuous_nested hd D (fun p : ℝ × ℝ => ρ (clampTI t p.1))
      (fun p x y => interKernel D (f (clampTI t p.2)) x y) (B := B) (K0 := K0)
      (fun p x => W.reg.bound _ (rho_clamp_mem ht p.1) x)
      (fun x => (continuous_rho_clamp_at hd hV hT W ht x).comp continuous_fst)
      (fun p => (hρc p.1).measurable)
      (fun x y => (continuous_interKernel_clamp ht.1 hf x y).comp continuous_snd)
      (fun p => measurable_interKernel (hc2 p.2))
      (fun p x y => hK0 _ (hc2 p.2) (hcb p.2) x y)


/-! ### One time step -/

theorem ftc_time {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr' : r ≤ r') (hr't : r' ≤ t) (y : Torus d) :
    f r' y - f r y = ∫ u in r..r', ft u y := by
  have hcl : ∀ u ∈ Icc r r', clampTI t u = u := fun u hu =>
    clampTI_of_mem ⟨hr.trans hu.1, hu.2.trans hr't⟩
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun u => f u y)
    (f' := fun u => ft u y) hrr' ?_ ?_ ?_
  · -- continuity of u ↦ f u y on [r, r']
    have hmaps : MapsTo (fun u : ℝ => (u, Torus.rep y)) (Icc r r') (Icc 0 t ×ˢ (univ : Set (Euc d))) :=
      fun u hu => ⟨⟨hr.trans hu.1, hu.2.trans hr't⟩, Set.mem_univ _⟩
    have h1 : ContinuousOn (fun u : ℝ => Torus.lift (f u) (Torus.rep y)) (Icc r r') :=
      hf.contOn_lift.comp (continuous_id.prodMk
        (continuous_const : Continuous fun _ : ℝ => Torus.rep y)).continuousOn hmaps
    refine h1.congr fun u _ => ?_
    simp [Torus.lift, Torus.mk_rep]
  · intro u hu
    exact hf.time_deriv y u ⟨hr.trans_lt hu.1, hu.2.trans_le hr't⟩
  · have hc : ContinuousOn (fun u => ft u y) (Icc r r') := by
      refine (continuous_ft_clamp_u (hr.trans (hrr'.trans hr't)) hf y).continuousOn.congr fun u hu => ?_
      simp only [hcl u hu]
    exact (hc.mono (by rw [Set.uIcc_of_le hrr'])).intervalIntegrable


theorem continuous_ft_joint {t : ℝ} (ht0 : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    Continuous fun q : Torus d × ℝ => ft (clampTI t q.2) q.1 :=
  hf.cont_time_deriv.comp ((Continuous.subtype_mk ((continuous_clampTI t).comp continuous_snd)
    (fun q => clampTI_mem ht0 q.2)).prodMk continuous_fst)

theorem step_pair_time {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0}
    (W : MFWeak D T ρ B L) {t : ℝ} (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {r r' : ℝ} (hr : 0 ≤ r) (hrr' : r ≤ r') (hr't : r' ≤ t) :
    pair (withDensityReal (ρ r')) (f r') - pair (withDensityReal (ρ r')) (f r)
      = ∫ u in r..r', pair (withDensityReal (ρ r')) (ft u) := by
  have hr'T : r' ∈ Icc 0 T := ⟨hr.trans hrr', hr't.trans ht.2⟩
  have hρd := W.reg.dens r' hr'T
  have hρc : Continuous (ρ r') := KernelGrad.isCk_continuous (W.reg.c1 r' hr'T)
  have hcl : ∀ u ∈ Icc r r', clampTI t u = u := fun u hu =>
    clampTI_of_mem ⟨hr.trans hu.1, hu.2.trans hr't⟩
  have hp : ∀ g : Torus d → ℝ, pair (withDensityReal (ρ r')) g = ∫ y, ρ r' y * g y := fun g =>
    PDE.MFPairing.integral_withDensityReal hρd.measurable hρd.nonneg g
  have hfc : ∀ a ∈ Icc 0 t, Continuous (f a) := fun a ha =>
    KernelGrad.isCk_continuous ((hf.c2 a ha).of_le (by norm_num))
  have hint : ∀ g : Torus d → ℝ, Continuous g → Integrable (fun y => ρ r' y * g y) :=
    fun g hg => PDE.MFThermalExist.integrable_of_continuous' (hρc.mul hg)
  have hr0 : r ∈ Icc 0 t := ⟨hr, hrr'.trans hr't⟩
  have hr1 : r' ∈ Icc 0 t := ⟨hr.trans hrr', hr't⟩
  have hLHS : pair (withDensityReal (ρ r')) (f r') - pair (withDensityReal (ρ r')) (f r)
      = ∫ y, ρ r' y * ∫ u in Ioc r r', ft (clampTI t u) y := by
    rw [hp, hp, ← integral_sub (hint _ (hfc _ hr1)) (hint _ (hfc _ hr0))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [← mul_sub, ftc_time hf hr hrr' hr't y, intervalIntegral.integral_of_le hrr']
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc fun u hu => by
      simp only [hcl u ⟨hu.1.le, hu.2⟩]
  have hRHS : ∫ u in r..r', pair (withDensityReal (ρ r')) (ft u)
      = ∫ u in Ioc r r', ∫ y, ρ r' y * ft (clampTI t u) y := by
    rw [intervalIntegral.integral_of_le hrr']
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [hp, hcl u ⟨hu.1.le, hu.2⟩]
  rw [hLHS, hRHS]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap]
  have hbd : Continuous (fun q : Torus d × ℝ => ρ r' q.1 * ft (clampTI t q.2) q.1) :=
    (hρc.comp continuous_fst).mul (continuous_ft_joint ht.1 hf)
  obtain ⟨Fm, hFm⟩ := isCompact_univ.exists_bound_of_continuousOn hf.cont_time_deriv.continuousOn
  obtain ⟨Bρ, hBρ0, hBρ⟩ := Duality.bounded_of_continuous hρc
  refine Integrable.of_bound (C := Bρ * Fm) hbd.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun q => ?_
  have h2 := hFm (⟨clampTI t q.2, clampTI_mem ht.1 q.2⟩, q.1) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h2 ⊢
  simp only [Function.uncurry]
  rw [abs_mul]
  exact mul_le_mul (hBρ _) h2 (abs_nonneg _) hBρ0


/-! ### Approximate fundamental theorem of calculus -/

/-- The (clamped) integrand of the time-dependent weak form. -/
def Hf (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (f ft : ℝ → Torus d → ℝ) (u : ℝ) : ℝ :=
  pair (withDensityReal (ρ (clampTI t u))) (ft (clampTI t u))
    + genL D (f (clampTI t u)) (ρ (clampTI t u))

theorem continuous_Hf (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    Continuous (Hf D ρ t f ft) := by
  have h1 := (continuous_G1 hd hV hT W ht hf).comp (continuous_id.prodMk continuous_id)
  have h2 := (continuous_G2 hd hV hT W ht hf).comp (continuous_id.prodMk continuous_id)
  exact h1.add h2

theorem step_identity (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr' : r ≤ r') (hr't : r' ≤ t) :
    pair (withDensityReal (ρ r')) (f r') - pair (withDensityReal (ρ r)) (f r)
      = ∫ u in r..r', (pair (withDensityReal (ρ (clampTI t r'))) (ft (clampTI t u))
          + genL D (f (clampTI t r)) (ρ (clampTI t u))) := by
  have hcl : ∀ u ∈ Icc r r', clampTI t u = u := fun u hu =>
    clampTI_of_mem ⟨hr.trans hu.1, hu.2.trans hr't⟩
  have hr0 : r ∈ Icc 0 t := ⟨hr, hrr'.trans hr't⟩
  have hr1 : r' ∈ Icc 0 t := ⟨hr.trans hrr', hr't⟩
  have hrT : r ∈ Icc 0 T := ⟨hr, hrr'.trans (hr't.trans ht.2)⟩
  have hr'T : r' ∈ Icc 0 T := ⟨hr.trans hrr', hr't.trans ht.2⟩
  have hA := step_pair_time W ht hf hr hrr' hr't
  have hB := weak_interval hd hV hT W (hf.c2 r hr0) hr hrr' (hr't.trans ht.2)
  have e1 : ∫ u in r..r', pair (withDensityReal (ρ r')) (ft u)
      = ∫ u in r..r', pair (withDensityReal (ρ (clampTI t r'))) (ft (clampTI t u)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hrr'] at hu
    simp only [hcl u hu, clampTI_of_mem hr1]
  have i1 : IntervalIntegrable (fun u => pair (withDensityReal (ρ (clampTI t r'))) (ft (clampTI t u)))
      volume r r' := by
    have := (continuous_G1 hd hV hT W ht hf).comp
      ((continuous_id.prodMk continuous_const) : Continuous fun u : ℝ => (u, r'))
    exact this.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => genL D (f (clampTI t r)) (ρ (clampTI t u))) volume r r' := by
    have := (continuous_G2 hd hV hT W ht hf).comp
      ((continuous_id.prodMk continuous_const) : Continuous fun u : ℝ => (u, r))
    exact this.intervalIntegrable _ _
  have e2 : ∫ u in r..r', genL D (f r) (ρ u)
      = ∫ u in r..r', genL D (f (clampTI t r)) (ρ (clampTI t u)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hrr'] at hu
    simp only [hcl u hu, clampTI_of_mem hr0]
  rw [intervalIntegral.integral_add i1 i2, ← e1, ← e2, ← hA, ← hB]
  ring


theorem approx_ftc (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r r' : ℝ, 0 ≤ r → r ≤ r' → r' ≤ t → r' - r < δ →
      |(pair (withDensityReal (ρ r')) (f r') - pair (withDensityReal (ρ r)) (f r))
        - ∫ u in r..r', Hf D ρ t f ft u| ≤ ε * (r' - r) := by
  have hK : IsCompact (Icc 0 t ×ˢ Icc 0 t : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hG1 := continuous_G1 hd hV hT W ht hf
  have hG2 := continuous_G2 hd hV hT W ht hf
  obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hG1.continuousOn) (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hG2.continuousOn) (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun r r' hr hrr' hr't hlt => ?_⟩
  have hcl : ∀ u ∈ Icc r r', clampTI t u = u := fun u hu =>
    clampTI_of_mem ⟨hr.trans hu.1, hu.2.trans hr't⟩
  have hr1 : r' ∈ Icc 0 t := ⟨hr.trans hrr', hr't⟩
  have hr0 : r ∈ Icc 0 t := ⟨hr, hrr'.trans hr't⟩
  rw [step_identity hd hV hT W ht hf hr hrr' hr't]
  have hi1 : IntervalIntegrable (fun u => pair (withDensityReal (ρ (clampTI t r'))) (ft (clampTI t u))
          + genL D (f (clampTI t r)) (ρ (clampTI t u))) volume r r' := by
    refine IntervalIntegrable.add ?_ ?_
    · exact ((hG1.comp ((continuous_id.prodMk continuous_const) : Continuous fun u : ℝ => (u, r'))
        ).intervalIntegrable _ _)
    · exact ((hG2.comp ((continuous_id.prodMk continuous_const) : Continuous fun u : ℝ => (u, r))
        ).intervalIntegrable _ _)
  have hi2 : IntervalIntegrable (Hf D ρ t f ft) volume r r' :=
    (continuous_Hf hd hV hT W ht hf).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hi1 hi2]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := r')
    (f := fun u => (pair (withDensityReal (ρ (clampTI t r'))) (ft (clampTI t u))
          + genL D (f (clampTI t r)) (ρ (clampTI t u))) - Hf D ρ t f ft u) (C := ε) (fun u hu => by
      rw [Set.uIoc_of_le hrr'] at hu
      have hu' : u ∈ Icc r r' := ⟨hu.1.le, hu.2⟩
      have hu0 : u ∈ Icc 0 t := ⟨hr.trans hu.1.le, hu.2.trans hr't⟩
      have hd1 : dist ((u, r') : ℝ × ℝ) (u, u) < δ1 := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonneg (by linarith [hu.2])]
        exact max_lt hδ1 (by linarith [lt_min_iff.1 hlt, hu.1, min_le_left δ1 δ2])
      have hd2 : dist ((u, r) : ℝ × ℝ) (u, u) < δ2 := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonpos (by linarith [hu.1])]
        exact max_lt hδ2 (by linarith [hu.2, min_le_right δ1 δ2])
      have e1 := h1 (u, r') ⟨hu0, hr1⟩ (u, u) ⟨hu0, hu0⟩ hd1
      have e2 := h2 (u, r) ⟨hu0, hr0⟩ (u, u) ⟨hu0, hu0⟩ hd2
      rw [Real.dist_eq] at e1 e2
      have hHf : Hf D ρ t f ft u = (pair (withDensityReal (ρ (clampTI t u))) (ft (clampTI t u))
          + genL D (f (clampTI t u)) (ρ (clampTI t u))) := rfl
      simp only [Real.norm_eq_abs, hHf]
      rw [abs_lt] at e1 e2
      rw [abs_le]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hrr')] at hb
  exact hb


theorem timeDep_core (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {B : ℝ} {L : ℝ≥0} (W : MFWeak D T ρ B L) {t : ℝ}
    (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    pair (withDensityReal (ρ t)) (f t) - pair (withDensityReal (ρ 0)) (f 0)
      = ∫ u in (0 : ℝ)..t, Hf D ρ t f ft u := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    simp
  set Φ : ℝ → ℝ := fun r => pair (withDensityReal (ρ r)) (f r) with hΦ
  have hHc := continuous_Hf hd hV hT W ht hf
  -- the error is smaller than every `ε t`
  have key : ∀ ε : ℝ, 0 < ε → |(Φ t - Φ 0) - ∫ u in (0 : ℝ)..t, Hf D ρ t f ft u| ≤ ε * t := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := approx_ftc hd hV hT W ht hf hε
    obtain ⟨n, hn⟩ := exists_nat_gt (t / δ)
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_trans (by positivity) hn
      exact_mod_cast this
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    set a : ℕ → ℝ := fun k => k * (t / n) with ha
    have hstep : t / n < δ := by
      rw [div_lt_iff₀ hnR]
      rw [div_lt_iff₀ hδ] at hn
      linarith
    have ha0 : a 0 = 0 := by simp [ha]
    have han : a n = t := by simp [ha]; field_simp
    have hmono : ∀ k, a k ≤ a (k + 1) := fun k => by
      simp only [ha]; push_cast
      nlinarith [div_pos hpos hnR]
    have hdiff : ∀ k, a (k + 1) - a k = t / n := fun k => by simp only [ha]; push_cast; ring
    have hnonneg : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; positivity
    have hle : ∀ k ≤ n, a k ≤ t := fun k hk => by
      simp only [ha]
      have : (k : ℝ) ≤ n := by exact_mod_cast hk
      calc (k : ℝ) * (t / n) ≤ n * (t / n) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = t := by field_simp
    have hsum1 : ∑ k ∈ Finset.range n, (Φ (a (k + 1)) - Φ (a k)) = Φ t - Φ 0 := by
      rw [Finset.sum_range_sub (fun k => Φ (a k)) n, han, ha0]
    have hsum2 : ∑ k ∈ Finset.range n, ∫ u in a k..a (k + 1), Hf D ρ t f ft u
        = ∫ u in (0 : ℝ)..t, Hf D ρ t f ft u := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hHc.intervalIntegrable _ _),
        ha0, han]
    rw [← hsum1, ← hsum2, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range n, ((Φ (a (k + 1)) - Φ (a k)) - ∫ u in a k..a (k + 1), Hf D ρ t f ft u)|
        ≤ ∑ k ∈ Finset.range n, |(Φ (a (k + 1)) - Φ (a k)) - ∫ u in a k..a (k + 1), Hf D ρ t f ft u| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, ε * (t / n) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
          have := hδ' (a k) (a (k + 1)) (hnonneg k) (hmono k) (hle (k + 1) hk')
            (by rw [hdiff]; exact hstep)
          rw [hdiff] at this
          exact this
      _ = ε * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  by_contra hne
  set E := (Φ t - Φ 0) - ∫ u in (0 : ℝ)..t, Hf D ρ t f ft u with hE
  have hE0 : E ≠ 0 := fun h => hne (by rw [hE] at h; linarith)
  have hpos' : 0 < |E| := abs_pos.2 hE0
  have := key (|E| / (2 * t)) (by positivity)
  have e : |E| / (2 * t) * t = |E| / 2 := by field_simp
  rw [e] at this
  linarith


/-! ### Conversion to the mean-field drift form -/

theorem pair_target_eq (hd : 1 ≤ d) (D : DynData d) (hV : Torus.IsCk 2 D.V) {h : Torus d → ℝ}
    (hh : IsProbDensity h) (hh1 : Torus.IsCk 1 h) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ)
    {g : Torus d → ℝ} (hg : Continuous g) :
    pair (withDensityReal h) (fun x => g x + D.invβ * Torus.laplacian ψ x
        + inner ℝ (meanFieldDrift D h x) (Torus.grad ψ x))
      = pair (withDensityReal h) g + genL D ψ h := by
  have hconv : Continuous (convGradConv (periodicRieszGrad d D.s) h) :=
    PDE.convGradConv_continuous_of_one_le hd D.hs0 D.hsd h hh1
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M))
  have hcg := Duality.grad_continuous hψ
  have hcV := Duality.grad_continuous hV
  have hhc : Continuous h := KernelGrad.isCk_continuous hh1
  have hw := continuous_wgen D hV hψ
  have hI : Continuous (fun x => inner ℝ (Torus.grad ψ x)
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) h x))) :=
    hcg.inner (hmat.comp hconv)
  have hp : ∀ k : Torus d → ℝ, pair (withDensityReal h) k = ∫ y, h y * k y := fun k =>
    PDE.MFPairing.integral_withDensityReal hh.measurable hh.nonneg k
  have hgen : genL D ψ h = (∫ x, h x * wgen D ψ x) +
      ∫ x, h x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) h x)) := by
    have h1 := weak_genL D ψ hh
    rw [interactionPairing_withDensity_self hd D hh hh1 hψ, hp] at h1
    rw [← h1]
    rfl
  have hint : ∀ k : Torus d → ℝ, Continuous k → Integrable (fun x => h x * k x) :=
    fun k hk => PDE.MFThermalExist.integrable_of_continuous' (hhc.mul hk)
  rw [hgen, hp, hp]
  have e : (fun x => h x * (g x + D.invβ * Torus.laplacian ψ x
        + inner ℝ (meanFieldDrift D h x) (Torus.grad ψ x))) = fun x =>
      h x * g x + (h x * wgen D ψ x + h x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) h x))) := by
    funext x
    unfold wgen meanFieldDrift
    rw [inner_sub_left, real_inner_comm (Torus.grad ψ x)]
    ring
  have i23 : Integrable (fun x => h x * wgen D ψ x + h x * inner ℝ (Torus.grad ψ x)
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) h x))) :=
    (hint _ hw).add (hint _ hI)
  rw [e, integral_add (hint g hg) i23, integral_add (hint _ hw) (hint _ hI)]

theorem meanField_pairing_timeDependent (hd : 1 ≤ d) {D : DynData d} (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    IntegrableOn (fun r => pair (withDensityReal (ρ r))
        (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
          + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))) (Icc 0 t) ∧
      pair (withDensityReal (ρ t)) (f t) = pair (withDensityReal (ρ 0)) (f 0)
        + ∫ r in (0 : ℝ)..t, pair (withDensityReal (ρ r))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have W := MFWeak.of_regular hρ hreg
  have heq : ∀ r ∈ Icc 0 t, pair (withDensityReal (ρ r))
        (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
          + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x)) = Hf D ρ t f ft r := by
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    have hftc : Continuous (ft r) :=
      hf.cont_time_deriv.comp (continuous_const.prodMk continuous_id :
        Continuous fun y : Torus d => ((⟨r, hr⟩ : Icc (0 : ℝ) t), y))
    rw [pair_target_eq hd D hV (W.reg.dens r hrT) (W.reg.c1 r hrT) (hf.c2 r hr) hftc]
    unfold Hf
    rw [clampTI_of_mem hr]
  have hHc := continuous_Hf hd hV hT W ht hf
  refine ⟨?_, ?_⟩
  · exact (hHc.continuousOn.integrableOn_Icc).congr_fun (fun r hr => (heq r hr).symm) measurableSet_Icc
  · have := timeDep_core hd hV hT W ht hf
    have e : ∫ r in (0 : ℝ)..t, pair (withDensityReal (ρ r))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))
        = ∫ r in (0 : ℝ)..t, Hf D ρ t f ft r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le ht.1] at hr
      exact heq r hr
    rw [e]
    linarith

/-! ### The four pairings of `flucInteraction` -/

/-- Expansion of `flucInteraction` through the pointwise form of Lemma 3.1: the cross pairings are
`N⁻¹ ∑_i (⟨∇ψ, M ∇g*ρ⟩ - Div g*(ρ Mᵀ∇ψ))(x_i)` and the mean-field pairing is `∫ ρ ⟨∇ψ, M ∇g*ρ⟩`. -/
theorem flucInteraction_eq (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ)
    {Λ' : ℝ≥0} (hLip : LipschitzWith Λ' (Torus.lift ρ)) (hN : 0 < N) (X : Config d N) :
    flucInteraction D ψ X ρ
      = interactionPairing D ψ (empirical X) (empirical X)
        - (N : ℝ)⁻¹ * ∑ i, (inner ℝ (Torus.grad ψ (X i))
            (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ (X i)))
            - PDE.nonlocalTerm D ρ ψ (X i))
        + ∫ x, ρ x * inner ℝ (Torus.grad ψ x)
            (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) := by
  unfold flucInteraction
  rw [interactionPairing_empirical_withDensity hd hψ hρ hLip hN X,
    interactionPairing_withDensity_empirical hd hψ hρ hLip hN X,
    interactionPairing_withDensity_self hd D hρ hρ1 hψ]
  ring

/-! ### The nonlocal term and the symmetric identity `∫ ρ 𝒢ψ = - ∫ ρ ⟨∇ψ, M ∇g*ρ⟩` -/

theorem isCk_one_vcomp {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (M : Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d) : Torus.IsCk 1 (fun y => Torus.matVec M.transpose (Torus.grad ψ y) a) := by
  have e : (fun y => Torus.matVec M.transpose (Torus.grad ψ y) a) =
      fun y => inner ℝ (Torus.grad ψ y) (Torus.matVec M (EuclideanSpace.single a (1 : ℝ))) :=
    funext fun y => matVec_transpose_apply_eq_inner M _ a
  rw [e]
  exact PDE.MFPairing.isCk_one_inner_grad hψ _

theorem continuous_nonlocalTerm (hd : 1 ≤ d) (D : DynData d) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ) :
    Continuous (PDE.nonlocalTerm D ρ ψ) := by
  unfold PDE.nonlocalTerm
  refine continuous_finsetSum _ fun j _ => ?_
  have hw := isCk_one_vcomp hψ D.M j
  have hprod : Torus.IsCk 1 (fun y => ρ y * Torus.matVec D.M.transpose (Torus.grad ψ y) j) := by
    unfold Torus.IsCk at hρ1 hw ⊢
    exact hρ1.mul hw
  have hc := PDE.convGradConv_continuous_of_one_le hd D.hs0 D.hsd _ hprod
  exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hc

/-- The symmetric form of the self-pairing: `B_ψ(μ,μ) = ½ (∫ρ⟨∇ψ, M ∇g*ρ⟩ - ∫ρ 𝒢ψ)`
(Lemma 3.1 with `ν = μ`). -/
theorem interactionPairing_withDensity_self_symm (hd : 1 ≤ d) (D : DynData d) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ)
    {Λ' : ℝ≥0} (hLip : LipschitzWith Λ' (Torus.lift ρ)) :
    interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      (1 / 2 : ℝ) * ((∫ x, ρ x * inner ℝ (Torus.grad ψ x)
          (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)))
        - ∫ x, ρ x * PDE.nonlocalTerm D ρ ψ x) := by
  have hconv : Continuous (convGradConv (periodicRieszGrad d D.s) ρ) :=
    PDE.convGradConv_continuous_of_one_le hd D.hs0 D.hsd ρ hρ1
  have hmat : Continuous (fun v : Euc d => Torus.matVec D.M v) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M))
  have hcg := Duality.grad_continuous hψ
  have ha : Continuous (fun x => inner ℝ (Torus.grad ψ x)
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x))) := hcg.inner (hmat.comp hconv)
  have hn := continuous_nonlocalTerm hd D hψ hρ1
  have hρc : Continuous ρ := KernelGrad.isCk_continuous hρ1
  have hint : ∀ k : Torus d → ℝ, Continuous k → Integrable (fun x => ρ x * k x) :=
    fun k hk => PDE.MFThermalExist.integrable_of_continuous' (hρc.mul hk)
  rw [interactionPairing_eq_kernel]
  congr 1
  have h1 : ∀ x, ∫ y, interKernel D ψ x y ∂(withDensityReal ρ)
      = inner ℝ (Torus.grad ψ x) (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x))
        - PDE.nonlocalTerm D ρ ψ x := fun x => pairing_expansion_pointwise hd hψ hρ hLip x
  simp_rw [h1]
  rw [PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  simp_rw [mul_sub]
  exact integral_sub (hint _ ha) (hint _ hn)

theorem integral_nonlocalTerm_eq_neg (hd : 1 ≤ d) (D : DynData d) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ)
    {Λ' : ℝ≥0} (hLip : LipschitzWith Λ' (Torus.lift ρ)) :
    ∫ x, ρ x * PDE.nonlocalTerm D ρ ψ x = -∫ x, ρ x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) := by
  have h1 := interactionPairing_withDensity_self_symm hd D hψ hρ hρ1 hLip
  rw [interactionPairing_withDensity_self hd D hρ hρ1 hψ] at h1
  linarith

end HRS
