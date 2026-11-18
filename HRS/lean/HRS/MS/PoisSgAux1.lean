import HRS.MS.PoisFlowAux2
import HRS.Stochastic.Brownian

/-!
# POIS-SG, part 1: joint measurability of the pathwise flow and of its `x`-derivatives

Setting.  `Ω` with a measurable space, `W : ℝ≥0 → Ω → Fin d → ℝ` with `W s` measurable, every path
continuous and `W 0 = 0` (this is what `IsBrownianFiltration` provides; see `SgNoise`).  The
pathwise flow is `flowMap q B (fun s => W s ω) t x` (`PoisFlowAux1`).

Main results (helper lemmas carry the prefix `sg_`):
* `sg_measurable_flowMap`: for `q ≥ 0`, `HasCbBound m Mb B` (`1 ≤ m`) and `t ≥ 0`, the map
  `(ω, x) ↦ flowMap q B (W · ω) t x` is jointly measurable.  Proof: the flow `Z_t(x)` of the random
  ODE is the pointwise limit of the Picard iterates (`sg_picard`), each of which is jointly
  measurable by the Caratheodory lemma (continuous in time, measurable in `(ω, x)`) and
  measurability of parametric integrals.
* `sg_measurable_iteratedFDeriv`: if `G : Ω → E → H` is jointly strongly measurable and each `G ω`
  is `C^j`, then `(ω, x) ↦ iteratedFDeriv ℝ j (G ω) x` is jointly strongly measurable
  (difference quotients along the basis vectors, induction on `j`).

The measurability statements are for `t ≥ 0` only: `pfZ` is defined by choice and carries no
information at negative times.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow

noncomputable section

namespace HRS.MS.PoisSg

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-! ### Measurability of derivatives with respect to a parameter -/

theorem sg_stronglyMeasurable_fderiv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (G : Ω → Euc d → H) (hG : StronglyMeasurable (fun p : Ω × Euc d => G p.1 p.2))
    (hd : ∀ ω, Differentiable ℝ (G ω)) :
    StronglyMeasurable (fun p : Ω × Euc d => fderiv ℝ (G p.1) p.2) := by
  set e : Fin d → Euc d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hD : ∀ i, StronglyMeasurable (fun p : Ω × Euc d => fderiv ℝ (G p.1) p.2 (e i)) := by
    intro i
    refine stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
      (f := fun n (p : Ω × Euc d) =>
        (1 / ((n : ℝ) + 1))⁻¹ • (G p.1 (p.2 + (1 / ((n : ℝ) + 1)) • e i) - G p.1 p.2)) ?_ ?_
    · intro n
      have hm : Measurable (fun p : Ω × Euc d => (p.1, p.2 + (1 / ((n : ℝ) + 1)) • e i)) :=
        measurable_fst.prodMk (measurable_snd.add_const _)
      exact (hG.comp_measurable hm |>.sub hG).const_smul _
    · rw [tendsto_pi_nhds]
      intro p
      have hda : DifferentiableAt ℝ (G p.1) p.2 := hd p.1 p.2
      have h1 := (hda.hasFDerivAt.hasLineDerivAt (e i)).tendsto_slope_zero_right
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun n => by simp; positivity⟩
      exact h1.comp h2
  have hsum : ∀ p : Ω × Euc d, fderiv ℝ (G p.1) p.2 =
      ∑ i, (ContinuousLinearMap.smulRightL ℝ (Euc d) H (EuclideanSpace.proj i))
        (fderiv ℝ (G p.1) p.2 (e i)) := by
    intro p
    refine ContinuousLinearMap.coe_injective ?_
    refine (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun i => ?_
    simp [he, ContinuousLinearMap.smulRightL, EuclideanSpace.proj]
  have hfun : (fun p : Ω × Euc d => fderiv ℝ (G p.1) p.2) = fun p : Ω × Euc d => ∑ i,
      (ContinuousLinearMap.smulRightL ℝ (Euc d) H (EuclideanSpace.proj i))
        (fderiv ℝ (G p.1) p.2 (e i)) := funext hsum
  rw [hfun]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ (Euc d) H (EuclideanSpace.proj i)).continuous.comp_stronglyMeasurable (hD i)

theorem sg_stronglyMeasurable_iteratedFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Ω → Euc d → F) (hG : StronglyMeasurable (fun p : Ω × Euc d => G p.1 p.2)) (j : ℕ)
    (hd : ∀ ω, ContDiff ℝ (j : WithTop ℕ∞) (G ω)) :
    StronglyMeasurable (fun p : Ω × Euc d => iteratedFDeriv ℝ j (G p.1) p.2) := by
  induction j with
  | zero =>
    have : (fun p : Ω × Euc d => iteratedFDeriv ℝ 0 (G p.1) p.2) =
        fun p => (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm (G p.1 p.2) := by
      funext p; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm.continuous.comp_stronglyMeasurable hG
  | succ j ih =>
    have hd' : ∀ ω, ContDiff ℝ (j : WithTop ℕ∞) (G ω) := fun ω =>
      (hd ω).of_le (by exact_mod_cast Nat.le_succ j)
    have h1 := sg_stronglyMeasurable_fderiv (fun ω => iteratedFDeriv ℝ j (G ω)) (ih hd')
      (fun ω => (hd ω).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j))
    have : (fun p : Ω × Euc d => iteratedFDeriv ℝ (j + 1) (G p.1) p.2) =
        fun p => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) F).symm
          (fderiv ℝ (iteratedFDeriv ℝ j (G p.1)) p.2) := by
      funext p; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [this]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) F).symm.continuous.comp_stronglyMeasurable h1

/-! ### Measurability of the noise functionals -/

/-- The noise: measurable in `ω` for each time, everywhere continuous paths started at `0`. -/
structure SgNoise (W : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  meas : ∀ s, Measurable (W s)
  cont : ∀ ω, Continuous fun s => W s ω
  zero : ∀ ω, W 0 ω = 0

theorem sg_meas_pfPath {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) :
    Measurable (fun p : ℝ × Ω => pfPath (fun s => W s p.2) p.1) := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (s : ℝ) (ω : Ω) => pfPath (fun r => W r ω) s)
    (fun ω => pf_continuous_path (hW.cont ω)) fun s => ?_
  exact (PiLp.continuous_toLp 2 _).measurable.comp (hW.meas _)

theorem sg_meas_intervalIntegral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → α → E} (hf : StronglyMeasurable (fun p : ℝ × α => f p.1 p.2))
    (a b : ℝ) : StronglyMeasurable fun x => ∫ s in a..b, f s x := by
  have key : ∀ c e : ℝ, StronglyMeasurable fun x => ∫ s in Ioc c e, f s x := fun c e =>
    (hf.comp_measurable measurable_swap : StronglyMeasurable fun p : α × ℝ => f p.2 p.1
      ).integral_prod_right' (ν := volume.restrict (Ioc c e))
  simp only [intervalIntegral]
  exact (key a b).sub (key b a)

theorem sg_meas_ouShift {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) (q t : ℝ) :
    Measurable (fun ω => ouShift q (fun s => W s ω) t) := by
  unfold ouShift
  have h1 : Measurable fun ω => pfPath (fun s => W s ω) t :=
    (sg_meas_pfPath hW).comp (measurable_const.prodMk measurable_id)
  have h2 : StronglyMeasurable fun ω =>
      ∫ s in (0 : ℝ)..t, Real.exp (-q * (t - s)) • pfPath (fun r => W r ω) s := by
    refine sg_meas_intervalIntegral (f := fun s ω => Real.exp (-q * (t - s)) •
      pfPath (fun r => W r ω) s) ?_ 0 t
    exact ((Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.sub measurable_fst))).smul (sg_meas_pfPath hW)).stronglyMeasurable
  exact h1.sub (h2.measurable.const_smul q)

theorem sg_meas_ouShift_joint {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) (q : ℝ) :
    Measurable (fun p : ℝ × Ω => ouShift q (fun s => W s p.2) p.1) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : Ω) => ouShift q (fun s => W s ω) t)
    (fun ω => pf_continuous_ou (hW.cont ω)) (sg_meas_ouShift hW q)

/-! ### Picard iterates -/

/-- Picard iterates of the random ODE `Z' = pfDrift`, `Z_0 = x`. -/
def sgPicard (q : ℝ) (B : Euc d → Euc d) (W : ℝ≥0 → Ω → Fin d → ℝ) :
    ℕ → ℝ → Ω → Euc d → Euc d
  | 0, _, _, x => x
  | n + 1, s, ω, x =>
      x + ∫ r in (0 : ℝ)..s, pfDrift q B (fun u => W u ω) r (sgPicard q B W n r ω x)

theorem sg_picard_cont {q : ℝ} {B : Euc d → Euc d} {W : ℝ≥0 → Ω → Fin d → ℝ} (hBc : Continuous B)
    (ω : Ω) (hω : Continuous fun s => W s ω) (n : ℕ) (x : Euc d) :
    Continuous fun s => sgPicard q B W n s ω x := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous fun r => pfDrift q B (fun u => W u ω) r (sgPicard q B W n r ω x) :=
      (pf_continuous_drift hBc hω).comp (continuous_id.prodMk ih)
    exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hc.intervalIntegrable a b) 0)

theorem sg_picard_meas {q : ℝ} {B : Euc d → Euc d} {W : ℝ≥0 → Ω → Fin d → ℝ} (hBc : Continuous B)
    (hW : SgNoise W) (n : ℕ) (s : ℝ) :
    Measurable (fun p : Ω × Euc d => sgPicard q B W n s p.1 p.2) := by
  induction n generalizing s with
  | zero => exact measurable_snd
  | succ n ih =>
    have hj : Measurable (fun p : ℝ × (Ω × Euc d) => sgPicard q B W n p.1 p.2.1 p.2.2) :=
      measurable_uncurry_of_continuous_of_measurable
        (u := fun (r : ℝ) (p : Ω × Euc d) => sgPicard q B W n r p.1 p.2)
        (fun p => sg_picard_cont hBc p.1 (hW.cont p.1) n p.2) ih
    have hU : Measurable (fun p : ℝ × (Ω × Euc d) =>
        ouShift q (fun u => W u p.2.1) p.1) :=
      (sg_meas_ouShift_joint hW q).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hg : Measurable (fun p : ℝ × (Ω × Euc d) =>
        pfDrift q B (fun u => W u p.2.1) p.1 (sgPicard q B W n p.1 p.2.1 p.2.2)) := by
      unfold pfDrift
      exact (hj.const_smul (-q)).add (hBc.measurable.comp (hj.add (hU.const_smul (Real.sqrt 2) : Measurable fun p : ℝ × (Ω × Euc d) => Real.sqrt 2 • ouShift q (fun u => W u p.2.1) p.1)))
    have hI := sg_meas_intervalIntegral (f := fun r (p : Ω × Euc d) =>
      pfDrift q B (fun u => W u p.1) r (sgPicard q B W n r p.1 p.2)) hg.stronglyMeasurable 0 s
    exact measurable_snd.add hI.measurable

/-- Pointwise convergence of the Picard iterates to the chosen solution `pfZ` (`t ≥ 0`). -/
theorem sg_picard_tendsto {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d}
    {W : ℝ≥0 → Ω → Fin d → ℝ} (ω : Ω) (H : PfHyp q Mb m B (fun s => W s ω)) (x : Euc d)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => sgPicard q B W n t ω x) atTop (𝓝 (pfZ q B (fun s => W s ω) x t)) := by
  set Z := pfZ q B (fun s => W s ω) x with hZdef
  have hZc : ContinuousOn Z (Icc 0 t) := pf_Z_cont H x ht
  obtain ⟨L, hL⟩ := (pf_isLipschitzDrift H).lip t
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    ((continuousOn_const (c := x)).sub hZc)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hZeq : ∀ r ∈ Icc (0 : ℝ) t, Z r = x + ∫ s in (0 : ℝ)..r,
      pfDrift q B (fun u => W u ω) s (Z s) := by
    intro r hr
    have := pf_Z_eq H x hr.1
    rw [setIntegral_Icc_eq_interval hr.1] at this
    exact this
  have hYc : ∀ n : ℕ, Continuous fun s => sgPicard q B W n s ω x :=
    fun n => sg_picard_cont H.hB.1.continuous ω H.hw n x
  have hbd : ∀ n : ℕ, ∀ r ∈ Icc (0 : ℝ) t,
      ‖sgPicard q B W n r ω x - Z r‖ ≤ K * (L * r) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro r hr
      simpa [sgPicard] using hK r hr
    | succ n ih =>
      intro r hr
      have hr0 : 0 ≤ r := hr.1
      have hsub : Icc (0 : ℝ) r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
      have h1 : Continuous fun s => pfDrift q B (fun u => W u ω) s (sgPicard q B W n s ω x) :=
        (pf_continuous_drift H.hB.1.continuous H.hw).comp (continuous_id.prodMk (hYc n))
      have h2 : ContinuousOn (fun s => pfDrift q B (fun u => W u ω) s (Z s)) (Icc 0 t) :=
        pf_continuousOn_drift H x ht
      have h2i : IntervalIntegrable (fun s => pfDrift q B (fun u => W u ω) s (Z s)) volume 0 r :=
        (h2.mono hsub).intervalIntegrable_of_Icc hr0
      have h1i := h1.intervalIntegrable (μ := volume) 0 r
      have e : sgPicard q B W (n + 1) r ω x - Z r = ∫ s in (0 : ℝ)..r,
          (pfDrift q B (fun u => W u ω) s (sgPicard q B W n s ω x) -
            pfDrift q B (fun u => W u ω) s (Z s)) := by
        rw [intervalIntegral.integral_sub h1i h2i, hZeq r hr]
        simp only [sgPicard]
        abel
      rw [e]
      have hg : Continuous fun s : ℝ => (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) := by
        fun_prop
      refine (intervalIntegral.norm_integral_le_of_norm_le hr0 (g := fun s : ℝ =>
        (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ))) (Eventually.of_forall fun s hs => ?_)
        (hg.intervalIntegrable 0 r)).trans ?_
      · have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.trans hr.2⟩
        have := (hL s hs').dist_le_mul (sgPicard q B W n s ω x) (Z s)
        rw [dist_eq_norm, dist_eq_norm] at this
        exact this.trans (mul_le_mul_of_nonneg_left (ih s hs') (NNReal.coe_nonneg _))
      · have hint : ∫ s in (0 : ℝ)..r, (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) =
            (L : ℝ) * (K * L ^ n / (n.factorial : ℝ)) * (r ^ (n + 1) / (n + 1)) := by
          have : ∀ s : ℝ, (L : ℝ) * (K * (L * s) ^ n / (n.factorial : ℝ)) =
              ((L : ℝ) * (K * L ^ n / (n.factorial : ℝ))) * s ^ n := fun s => by
            rw [mul_pow]; ring
          simp_rw [this]
          rw [intervalIntegral.integral_const_mul, integral_pow]
          simp
        rw [hint, Nat.factorial_succ]
        have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
        push_cast
        apply le_of_eq
        field_simp
        ring
  have hlim : Tendsto (fun n : ℕ => K * ((L * t) ^ n / (n.factorial : ℝ))) atTop (𝓝 (K * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ((L : ℝ) * t)).const_mul K
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have := hbd n t ⟨ht, le_rfl⟩
  rwa [mul_div_assoc] at this

theorem sg_measurable_Z {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : SgNoise W) (hq : 0 ≤ q) (hm : 1 ≤ m) (hB : HasCbBound m Mb B) {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fun p : Ω × Euc d => pfZ q B (fun s => W s p.1) p.2 t) := by
  refine measurable_of_tendsto_metrizable (f := fun n (p : Ω × Euc d) => sgPicard q B W n t p.1 p.2)
    (fun n => sg_picard_meas hB.1.continuous hW n t) (tendsto_pi_nhds.2 fun p => ?_)
  exact sg_picard_tendsto p.1 ⟨hq, hm, hB, hW.cont p.1, hW.zero p.1⟩ p.2 ht

/-- Joint measurability of the pathwise flow in `(ω, x)` (for `t ≥ 0`). -/
theorem sg_measurable_flowMap {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : SgNoise W) (hq : 0 ≤ q) (hm : 1 ≤ m) (hB : HasCbBound m Mb B) {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) := by
  unfold flowMap
  exact (sg_measurable_Z hW hq hm hB ht).add
    (((sg_meas_ouShift hW q t).comp measurable_fst).const_smul (Real.sqrt 2))

end HRS.MS.PoisSg
