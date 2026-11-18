import HRS.MS.WsStatAux13
import HRS.MS.GenPathTie

/-!
# S21 packet F3a: expectation facts for the centred mild identity

* `s21_integral_meanEmpirical`: `pair (meanEmpirical nu) f = N^{-1} sum_i E_nu f(X_i)` for bounded measurable `f`.
* `s21_E_pair_emp`: if `P.map Y = nu` then `E pair(empirical (Y zeta)) f = pair (meanEmpirical nu) f`.
* `s21_k0_eval_gen`: the coordinate formula of `s56_k0_eval` for the state `s56k0 C m T sigma nu mu_rho` with an arbitrary
  probability measure `nu` of finite first moment in place of an empirical measure:
  `coord (evalA (s56k0 ..)) t alpha = sigma (pair nu (U^{0,t} phi_alpha) - pair mu_rho (U^{0,t} phi_alpha))`.
  (Hence the deterministic centring `kappa = s56k0 .. (meanEmpirical nu) ..` of the initial `K`-state needs no Bochner expectation.)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

theorem s21_meanEmpirical_eq_sum {N : ℕ} (P : Measure (EucConfig d N)) :
    HRS.Whole.meanEmpirical P = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, P.map (fun X : EucConfig d N => X i) := by
  ext A hA
  rw [HRS.Whole.meanEmpirical_apply P hA, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (measurable_pi_apply i) hA]; rfl

theorem s21_integral_meanEmpirical {N : ℕ} (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν]
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ∫ x, f x ∂(HRS.Whole.meanEmpirical ν) = (N : ℝ)⁻¹ * ∑ i, ∫ X, f (X i) ∂ν := by
  rw [s21_meanEmpirical_eq_sum, integral_smul_measure, integral_finsetSum_measure]
  · have : ∀ i : Fin N, ∫ x, f x ∂(ν.map (fun X : EucConfig d N => X i)) = ∫ X, f (X i) ∂ν := by
      intro i
      exact integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    simp [this]
  · intro i _
    have : IsProbabilityMeasure (ν.map (fun X : EucConfig d N => X i)) :=
      ⟨by rw [Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]; simp⟩
    exact Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hB x)

theorem s21_E_pair_emp {N : ℕ} (hN : 1 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → EucConfig d N) (hY : Measurable Y)
    (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν] (hν : P.map Y = ν) {f : Euc d → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ∫ ζ, HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) f ∂P = HRS.Whole.pair (HRS.Whole.meanEmpirical ν) f := by
  have e1 : ∀ ζ, HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) f = (N : ℝ)⁻¹ * ∑ i, f (Y ζ i) :=
    fun ζ => HRS.Whole.pair_empirical (by omega) _ _
  simp_rw [e1]
  have hint : ∀ i : Fin N, Integrable (fun ζ => f (Y ζ i)) P := fun i =>
    Integrable.of_bound (hf.comp ((measurable_pi_apply i).comp hY)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ζ => by rw [Real.norm_eq_abs]; exact hB _)
  rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
  unfold HRS.Whole.pair
  rw [s21_integral_meanEmpirical ν hf hB, ← hν]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_map hY.aemeasurable (by exact hf.comp (measurable_pi_apply i) |>.aestronglyMeasurable)]

theorem s21_k0_eval_gen (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (σ : ℝ) (ν : Measure (Euc d)) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 (S.coeff N) b.m b.T σ ν (HRS.Whole.withDensityReal (S.ρ N 0))).evalA t) α =
      σ * (HRS.Whole.pair ν (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b.T := ⟨le_rfl, hT⟩
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  have hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature (S.coeff N) b.m b.T a 0 z‖ ≤ |Cf| := fun a z => by
    have := (hCf S N a 0 h0).2 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_abs_self _)
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature (S.coeff N) b.m b.T a 0 z := by
    intro a
    have := (s56_feat_meas b hbv S N hC a).comp (measurable_const (a := (0 : ℝ)).prodMk measurable_id)
    have e := mrrClamp_of_mem h0
    simp only [Function.comp_def, e] at this
    exact this
  have hρ := (S.mf N).density 0 h0
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hμint := s56_integrable_norm_withDensity hρ ((S.mf N).second_moment 0 h0)
  have hcl := s56_osc_classical b hbv S N ht α
  obtain ⟨B, hB⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) :=
    (hcl.c2 0 ⟨le_rfl, ht.1⟩).of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner (S.coeff N) b.m b.T σ |Cf| (abs_nonneg _) hmeas hbd ν
    (HRS.Whole.withDensityReal (S.ρ N 0)) hν hμint (HRS.MS.S52.s52y1 b.m b.T t α)
    (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) hh B
    (fun z => by
      have := hB 0 ⟨le_rfl, ht.1⟩ z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

/-- The reconstructed path of the particle martingale has mean zero in every coordinate: by `s56_ident` its `alpha`-th
coordinate at time `t` is a.s. the (truncated, scaled) real Ito integral, whose mean is `0` (`integral_itoIntegral`). -/
theorem s21_E_recon (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → KSpace d b.m b.T)
    (hM : IsHilbertItoIntegral P ℱ W' (s56Phi (S.coeff N) b.m b.T (S.q N) X) M)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    ∫ ζ, OscDual.coord (reconstructPath b.m b.T M ζ t) α ∂P = 0 := by
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hid := s56_ident (S.coeff N) b.m b.T (S.q N) N P ℱ W' X M hN hW
    (fun τ => s56_phi_isHS b hbv S N hC (S.q N) P ℱ X hF.progressive τ) hM hC t ht α
  have hcl := s56_osc_classical b hbv S N ht α
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) ht.1 hcl.isC12TestRd hF.progressive
  have hsm := HRS.itoIntegral_smul hF.brownian hprog (Real.sqrt (2 * S.q N / N))
  have hψ : (fun (r : ℝ) (ζ' : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) t then
      Real.sqrt (2 * S.q N / N) * gradComp ia.2 (propagatorW (S.coeff N) r t (oscTestFun b.m α))
        (X (Real.toNNReal r) ζ' ia.1) else 0) =
      fun s z => Real.sqrt (2 * S.q N / N) • HRS.MH.DualityRd.truncGradIntegrand t
        (fun r => propagatorW (S.coeff N) r t (oscTestFun b.m α)) X s z := by
    funext r ζ' ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  rw [hψ] at hid
  have h1 : ∫ ζ, OscDual.coord (reconstructPath b.m b.T M ζ t) α ∂P =
      ∫ ζ, Real.sqrt (2 * S.q N / N) * itoIntegral P ℱ W' (HRS.MH.DualityRd.truncGradIntegrand t
        (fun r => propagatorW (S.coeff N) r t (oscTestFun b.m α)) X) t ζ ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hid, hsm] with ζ h1 h2
    rw [h1, h2 t]
  rw [h1, integral_const_mul, integral_itoIntegral hF.brownian hprog t, mul_zero]

end HRS.MS.S21
