import HRS.MS.SharpInsAux4

/-!
# HRS.MS.SharpIns -- S7.6 `sharp_insertion_radius` and `sharp_insertion_rate`

Packet S76, namespace `HRS.MS.S76`, helper prefix `s76_`.  The statements proved are exactly
`HRS.Whole.sharp_insertion_radius` and `HRS.Whole.sharp_insertion_rate` (`SharpInsTie.lean` restates
them with `type_of%`); no frozen file is edited and no statement is weakened.

Route (TeX S L5738-5890).  `N = m + 3`-type thresholds are not needed: the proof is uniform in `L ≥ 1`,
and only `N ≥ 3` is used (second marginal of the pole law), so the frozen quantifier order
"`N₀` before `L`" holds with `N₀ = 3`.  The pole exponent `X_x = -λ Σ g(x - y_i)` is `≤ 0` and integrable
under the cavity law `P_n^0`, so `F_{N,x}(t) = cgf X_x P_n^0 (t)` and, by `s76_defect_eq`,
`D_N(x) = ∫_0^1 (1-t) Var_{P_n^{x,t}}(X_x) dt`.  For each `t ∈ (0,1]` the variance is compared with
`n m₀(t)`, `m₀(t) = ∫ ψ² e^{-tλ g} dμ` (`s76_pointwise`: in/out split at `r = λ^{1/s} L`,
exchangeability, static-input density bounds, pole variance, prefactor `|A-1| ≤ C N^{-τ}`);
`∫_0^1 (1-t) m₀ = λ^p I_L(x)` (`s76_diag_lintegral`) and `|I_L - 2A ρ(x)|` is bounded by the Lipschitz
constant and the kernel tail (`s76_IL_approx`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.S76

open HRS.Whole (rieszKernel EucConfig)
open HRS.MS.Wr (wr13c2_X)

variable {d : ℕ} {s : ℝ}

/-- `m₀(t) = ∫ ψ(y)² e^{-tλ g(x-y)} dμ(y)`. -/
def s76_m0 (d : ℕ) (s : ℝ) (μ : Measure (Euc d)) (lam r : ℝ) (x : Euc d) (t : ℝ) : ℝ :=
  ∫ y, s76_psi d s lam r x y ^ 2 * Real.exp (-(t * lam) * rieszKernel d s (x - y)) ∂μ

theorem s76_psi_sq_w_le (hs0 : 0 < s) {lam : ℝ} (hlam : 0 ≤ lam) (r u : ℝ) (x y : Euc d) :
    s76_psi d s lam r x y ^ 2 * Real.exp (-u * rieszKernel d s (x - y)) ≤
      lam ^ 2 * (rieszKernel d s (x - y) ^ 2 * Real.exp (-(u * rieszKernel d s (x - y)))) := by
  have hg : rieszKernel d s (x - y) = ‖x - y‖ ^ (-s) := HRS.Whole.Q34.rieszKernel_eq hs0.ne' _
  have h1 : s76_psi d s lam r x y ^ 2 ≤ (lam * ‖x - y‖ ^ (-s)) ^ 2 :=
    pow_le_pow_left₀ (s76_psi_nonneg hlam r x y) (s76_psi_le hlam r x y) 2
  rw [neg_mul, hg]
  calc s76_psi d s lam r x y ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s)))
      ≤ (lam * ‖x - y‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = lam ^ 2 * ((‖x - y‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖x - y‖ ^ (-s)))) := by ring

/-! ### The pointwise estimate -/

theorem s76_pointwise (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (hβ : 0 < β)
    (hM0 : 0 ≤ M) :
    ∃ K1 K2 K3 CA : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ K3 ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ N : ℕ, 3 ≤ N →
        ∀ x : Euc d, ∀ L : ℝ, 1 ≤ L → ∀ t ∈ Ioc (0 : ℝ) 1,
          |Var[wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
              (fun Y => t * wr13c2_X d s N β x Y)] -
            ((N - 1 : ℕ) : ℝ) * s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / N)
              ((β / N) ^ (1 / s) * L) x t| ≤
          K1 * (((N - 1 : ℕ) : ℝ) ^ 2 * (((β / N) ^ ((d : ℝ) / s)) ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) +
            K2 * (((N - 1 : ℕ) : ℝ) * (β / N) ^ ((d : ℝ) / s) * L ^ ((d : ℝ) - 2 * s)) +
            K3 * (((N - 1 : ℕ) : ℝ) * (β / N) ^ ((d : ℝ) / s) * L ^ (((d : ℝ) - 2 * s) / 2) *
              t ^ (((d : ℝ) / s - 2) / 2)) +
            ((N - 1 : ℕ) : ℝ) * (CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) *
              s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / N) ((β / N) ^ (1 / s) * L) x t := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd1
  have h2m : 0 < 2 * s - (d : ℝ) := by linarith
  obtain ⟨C0', hSI⟩ := HRS.MS.Wr.static_input_proof hd hs hsd β M hβ
  obtain ⟨CA, hCA⟩ := HRS.MS.Wr.conditional_density_proof hd hs hsd β M hβ
  obtain ⟨Cv, hCvpos, hvar⟩ := HRS.MS.Wr.wr13b_pole_variance hd hs0 hsd β M
  obtain ⟨Cr, hCr0, hradJ⟩ := HRS.MS.Wr.wr13c_radial_J hd1 hs0 hsd M
  obtain ⟨Cri, hCri0, hradI⟩ := HRS.MS.Wr.wr13c_radial_J_integral hd1 hs0 hsd M
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = max C0' 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C0 := by rw [hC0def]; exact le_max_right _ _
  have hC0' : C0' ≤ C0 := by rw [hC0def]; exact le_max_left _ _
  refine ⟨s76_K1 d s C0 M, s76_K2 d s Cv M, s76_K3 d s β M Cv Cr, CA, ?_, ?_, ?_, ?_⟩
  · unfold s76_K1; positivity
  · unfold s76_K2
    exact mul_nonneg hCvpos.le (div_nonneg (mul_nonneg hM0 hsA) h2m.le)
  · unfold s76_K3; positivity
  intro ρ hρ hM N hN x L hL t ht
  haveI hμprob := HRS.MS.Wr.wr13a_isProb_density hρ
  have hconv := HRS.MS.Wr.wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlam0 : 0 < β / (N : ℝ) := by positivity
  have hlamβ : β / (N : ℝ) ≤ β := div_le_self hβ.le hN1
  have hL0 : 0 < L := by linarith
  have hc : 0 < (β / (N : ℝ)) ^ (1 / s) := Real.rpow_pos_of_pos hlam0 _
  have hr : 0 < (β / (N : ℝ)) ^ (1 / s) * L := mul_pos hc hL0
  have hN2 : 2 ≤ N - 1 := by omega
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := ht.2
  have hu0 : 0 < t * (β / (N : ℝ)) := mul_pos ht.1 hlam0
  haveI hQp := HRS.MS.Wr.wr13c2_poleLaw_isProb hs0 hconv hβ.le ht0 N x
  have hex := HRS.MS.Wr.wr13b_poleLaw_exchangeable hs0 hconv hβ.le ht0 N x
  obtain ⟨-, -, -, hpole, -⟩ := hSI ρ hρ hM N (by omega)
  obtain ⟨-, hfirst0, hsec0, -⟩ := hpole x t ⟨ht0, ht1⟩
  have hgnn : ∀ y : Euc d, 0 ≤ rieszKernel d s (x - y) := fun y => by
    rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  have hexp1 : ∀ y : Euc d,
      Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)) ≤ 1 := by
    intro y
    refine Real.exp_le_one_iff.2 ?_
    nlinarith [mul_nonneg hu0.le (hgnn y)]
  have hexp2 : ∀ yz : Euc d × Euc d,
      Real.exp (-(t * (β / (N : ℝ))) * (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2))) ≤ 1 := by
    intro yz
    refine Real.exp_le_one_iff.2 ?_
    nlinarith [mul_nonneg hu0.le (add_nonneg (hgnn yz.1) (hgnn yz.2))]
  have hfirst : HRS.Whole.firstMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal C0 • HRS.Whole.withDensityReal ρ := by
    refine hfirst0.trans ?_
    rw [← withDensity_const]
    refine withDensity_mono (Filter.Eventually.of_forall fun y => ENNReal.ofReal_le_ofReal ?_)
    calc C0' * Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))
        ≤ C0 * Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)) :=
          mul_le_mul_of_nonneg_right hC0' (Real.exp_pos _).le
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (hexp1 y) hC0
      _ = C0 := mul_one _
  have hsec : HRS.Whole.secondMarginal (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal C0 • (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) := by
    refine (hsec0 hN).trans ?_
    rw [← withDensity_const]
    refine withDensity_mono (Filter.Eventually.of_forall fun yz => ENNReal.ofReal_le_ofReal ?_)
    calc C0' * Real.exp (-(t * (β / (N : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))
        ≤ C0 * Real.exp (-(t * (β / (N : ℝ))) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2))) :=
          mul_le_mul_of_nonneg_right hC0' (Real.exp_pos _).le
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (hexp2 yz) hC0
      _ = C0 := mul_one _
  have hvar_t : ∀ f : Euc d → ℝ, Measurable f →
      evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
        (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal (Cv * ((N - 1 : ℕ) : ℝ)) * ∫⁻ y, ‖f y‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y)))
          ∂(HRS.Whole.withDensityReal ρ) :=
    fun f hf => hvar ρ hρ hM β hβ le_rfl N (by omega) x t ⟨ht0, ht1⟩ f hf
  have hrad_t := hradJ ρ hρ hM (t * (β / (N : ℝ))) hu0 x
  have hJ0 : 0 ≤ HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))) :=
    zero_le_one.trans (HRS.MS.Wr.wr13c_one_le_J _ hu0)
  have hCore := s76_core hd1 hs0 hsd hds (n := N - 1) hN2
    (Q := HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) hex hρ hM
    (C0 := C0) (Cv := Cv) (Cr := Cr) (J := HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))))
    hC0 hCvpos.le hCr0 hJ0 (lam := β / (N : ℝ)) (r := (β / (N : ℝ)) ^ (1 / s) * L)
    (u := t * (β / (N : ℝ))) hlam0.le hr hu0.le x hfirst hsec hvar_t hrad_t
  -- `J` for `2s > d`
  have hJ : HRS.MS.Wr.wr13c_J d s (t * (β / (N : ℝ))) =
      1 + (t * (β / (N : ℝ))) ^ ((d : ℝ) / s - 2) := by
    unfold HRS.MS.Wr.wr13c_J
    rw [if_neg (not_lt.2 hds.le), if_neg (ne_of_gt hds)]
  have hArith := s76_arith hd1 hs0 hsd hds hβ hM0 hC0 hCvpos.le hCr0 hlam0 hlamβ hL ht.1 ht1
    (Nat.cast_nonneg (N - 1)) (n := ((N - 1 : ℕ) : ℝ)) hJ
  -- the variance of the exponent
  have hXeq : wr13c2_X d s N β x = fun Y : EucConfig d (N - 1) =>
      -(∑ i, (s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i) +
        s76_chi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i))) := by
    funext Y
    unfold wr13c2_X
    calc -(β / (N : ℝ)) * ∑ i, rieszKernel d s (x - Y i)
        = -((β / (N : ℝ)) * ∑ i, rieszKernel d s (x - Y i)) := neg_mul _ _
      _ = -(∑ i, (β / (N : ℝ)) * rieszKernel d s (x - Y i)) := by rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => (s76_psi_add_chi hs0 _ _ x _).symm
  have hVar : Var[wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
        (fun Y => t * wr13c2_X d s N β x Y)] =
      Var[fun Y : EucConfig d (N - 1) => ∑ i, (s76_psi d s (β / (N : ℝ))
          ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i) +
        s76_chi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x (Y i));
        HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t] := by
    rw [← HRS.MS.Wr.wr13c2_poleLaw_eq_tilted hs0 hconv hβ.le ht0 N x, hXeq]
    exact variance_fun_neg
  -- the prefactor
  obtain ⟨A, hAm, hAeq, hA0, hA1⟩ := (hCA ρ hρ hM N (by omega)).2 x t ⟨ht0, ht1⟩
  have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hwm : Measurable (fun y : Euc d => Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) :=
    Real.measurable_exp.comp (measurable_const.mul hgm)
  have hfpsi : Measurable (fun y : Euc d =>
      s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x y ^ 2) :=
    (s76_psi_meas _ _ x).pow_const 2
  have hint : Integrable (fun y : Euc d =>
      s76_psi d s (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x y ^ 2 *
        Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) (HRS.Whole.withDensityReal ρ) := by
    obtain ⟨hi, -⟩ := hradI ρ hρ hM (t * (β / (N : ℝ))) hu0 x
    refine Integrable.mono' (hi.const_mul ((β / (N : ℝ)) ^ 2)) (hfpsi.mul hwm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact s76_psi_sq_w_le hs0 hlam0.le _ _ x y
  have hB := s76_lemmaB (n := N - 1) (by omega)
    (Q := HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t)
    (μ := HRS.Whole.withDensityReal ρ)
    (w := fun y => Real.exp (-(t * (β / (N : ℝ))) * rieszKernel d s (x - y))) hwm
    (fun y => (Real.exp_pos _).le) hAm hAeq hA0
    (ε := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) hA1 hfpsi (fun y => sq_nonneg _) hint
  -- combine
  rw [hVar]
  have key : ∀ (Vv mm m0 n R ε : ℝ), |Vv - n * mm| ≤ R → |mm - m0| ≤ ε * m0 → 0 ≤ n →
      |Vv - n * m0| ≤ R + n * (ε * m0) := by
    intro Vv mm m0 n R ε h1 h2 hn
    have e : Vv - n * m0 = (Vv - n * mm) + n * (mm - m0) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left h2 hn
  have hn0 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfin := key _ _ _ _ _ _ (hCore.trans hArith) hB hn0
  refine hfin.trans (le_of_eq ?_)
  unfold s76_m0
  ring

/-! ### `∫_0^1 (1-t) m₀(t) dt = λ^p I_L` -/

theorem s76_m0_int (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {lam L : ℝ} (hlam : 0 < lam)
    (hL : 0 < L) (x : Euc d)
    (hI : ∀ u : ℝ, 0 < u → Integrable (fun y : Euc d => rieszKernel d s (x - y) ^ 2 *
        Real.exp (-(u * rieszKernel d s (x - y)))) (HRS.Whole.withDensityReal ρ)) :
    IntegrableOn (fun t => (1 - t) * s76_m0 d s (HRS.Whole.withDensityReal ρ) lam
        (lam ^ (1 / s) * L) x t) (Ioc (0 : ℝ) 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, (1 - t) * s76_m0 d s (HRS.Whole.withDensityReal ρ) lam
        (lam ^ (1 / s) * L) x t = lam ^ ((d : ℝ) / s) * s76_IL d s ρ (lam ^ (1 / s)) L x := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : SFinite μ := by rw [hμ]; unfold HRS.Whole.withDensityReal; infer_instance
  obtain ⟨hIL0, -⟩ := s76_IL_bounds hd hs hsd hρ hM (lam ^ (1 / s)) L x
  have hc : 0 < lam ^ (1 / s) := Real.rpow_pos_of_pos hlam _
  set r : ℝ := lam ^ (1 / s) * L with hrdef
  have hr : 0 < r := mul_pos hc hL
  have hpsim := s76_psi_meas (d := d) (s := s) lam r x
  have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hnn : ∀ (t : ℝ) (y : Euc d),
      0 ≤ s76_psi d s lam r x y ^ 2 * Real.exp (-(t * lam) * rieszKernel d s (x - y)) :=
    fun t y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun y : Euc d =>
      s76_psi d s lam r x y ^ 2 * Real.exp (-(t * lam) * rieszKernel d s (x - y))) μ := by
    intro t ht
    have hwm : Measurable (fun y : Euc d => Real.exp (-(t * lam) * rieszKernel d s (x - y))) :=
      Real.measurable_exp.comp (measurable_const.mul hgm)
    refine Integrable.mono' ((hI (t * lam) (mul_pos ht hlam)).const_mul (lam ^ 2))
      (((hpsim.pow_const 2).mul hwm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t y)]
    exact s76_psi_sq_w_le hs0 hlam.le r (t * lam) x y
  have hofReal : ∀ t : ℝ, 0 < t → ENNReal.ofReal (s76_m0 d s μ lam r x t) =
      ∫⁻ y, ENNReal.ofReal (s76_psi d s lam r x y ^ 2 *
        Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂μ := fun t ht =>
    ofReal_integral_eq_lintegral_ofReal (hint t ht) (Filter.Eventually.of_forall (hnn t))
  have hm0nn : ∀ t : ℝ, 0 ≤ s76_m0 d s μ lam r x t := fun t => integral_nonneg (hnn t)
  have hFm : Measurable (fun p : ℝ × Euc d =>
      s76_psi d s lam r x p.2 ^ 2 * Real.exp (-(p.1 * lam) * rieszKernel d s (x - p.2))) :=
    ((hpsim.comp measurable_snd).pow_const 2).mul
      (Real.measurable_exp.comp (((measurable_fst.mul measurable_const).neg).mul
        (hgm.comp measurable_snd)))
  have hm0meas : Measurable (fun t : ℝ => s76_m0 d s μ lam r x t) :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hmeas : Measurable (fun t : ℝ => (1 - t) * s76_m0 d s μ lam r x t) :=
    (measurable_const.sub measurable_id).mul hm0meas
  have hlint : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * s76_m0 d s μ lam r x t) =
      ENNReal.ofReal (lam ^ ((d : ℝ) / s) * s76_IL d s ρ (lam ^ (1 / s)) L x) := by
    calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * s76_m0 d s μ lam r x t)
        = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - t) * ∫⁻ y, ENNReal.ofReal
            (s76_psi d s lam r x y ^ 2 * Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂μ := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [ENNReal.ofReal_mul (by linarith [ht.2]), hofReal t ht.1]
      _ = ENNReal.ofReal (lam ^ ((d : ℝ) / s)) * ∫⁻ u in ball (0 : Euc d) L,
            ENNReal.ofReal (ρ (x - (lam ^ (1 / s)) • u)) *
              ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s))) :=
          s76_diag_lintegral hd1 hs0 hρ hlam hL x
      _ = ENNReal.ofReal (lam ^ ((d : ℝ) / s)) *
            ENNReal.ofReal (s76_IL d s ρ (lam ^ (1 / s)) L x) := by
          rw [s76_IL_ofReal hd hs hsd hρ hM]
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)).symm
  have hnnI : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (1 - t) * s76_m0 d s μ lam r x t := fun t ht =>
    mul_nonneg (by linarith [ht.2]) (hm0nn t)
  have hae : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t => (1 - t) * s76_m0 d s μ lam r x t :=
    ae_restrict_of_forall_mem measurableSet_Ioc hnnI
  refine ⟨⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hae).2 ?_⟩, ?_⟩
  · rw [hlint]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hae hmeas.aestronglyMeasurable, hlint,
      ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hlam.le _) hIL0)]

/-! ### Integrating the pointwise estimate -/

theorem s76_integrate {V m : ℝ → ℝ} {E0 E3 q n ε : ℝ} (hE0 : 0 ≤ E0) (hE3 : 0 ≤ E3)
    (hq : -1 < q) (hV : IntegrableOn (fun t => (1 - t) * V t) (Ioc (0 : ℝ) 1))
    (hm : IntegrableOn (fun t => (1 - t) * m t) (Ioc (0 : ℝ) 1))
    (hpt : ∀ t ∈ Ioc (0 : ℝ) 1, |V t - n * m t| ≤ E0 + E3 * t ^ q + n * ε * m t) :
    |(∫ t in Ioc (0 : ℝ) 1, (1 - t) * V t) - n * ∫ t in Ioc (0 : ℝ) 1, (1 - t) * m t| ≤
      E0 + E3 * (1 / (q + 1)) + n * ε * ∫ t in Ioc (0 : ℝ) 1, (1 - t) * m t := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ q) (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' hq)
  have hpowint : ∫ t in Ioc (0 : ℝ) 1, t ^ q = 1 / (q + 1) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hq)]
    have : (0 : ℝ) ^ (q + 1) = 0 := Real.zero_rpow (by linarith)
    rw [this]; simp
  have hconst : ∀ C : ℝ, IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) 1) := fun C =>
    integrableOn_const (by simp)
  set G : ℝ → ℝ := fun t => E0 + E3 * t ^ q + n * ε * ((1 - t) * m t) with hG
  have hGint : IntegrableOn G (Ioc (0 : ℝ) 1) :=
    ((hconst E0).add (hpow.const_mul E3)).add (hm.const_mul (n * ε))
  have hbd : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(1 - t) * V t - n * ((1 - t) * m t)‖ ≤ G t := by
    intro t ht
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    have h2 : 0 ≤ E3 * t ^ q := mul_nonneg hE3 (Real.rpow_nonneg ht.1.le _)
    have e : (1 - t) * V t - n * ((1 - t) * m t) = (1 - t) * (V t - n * m t) := by ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    calc (1 - t) * |V t - n * m t| ≤ (1 - t) * (E0 + E3 * t ^ q + n * ε * m t) :=
          mul_le_mul_of_nonneg_left (hpt t ht) h1
      _ = (1 - t) * (E0 + E3 * t ^ q) + n * ε * ((1 - t) * m t) := by ring
      _ ≤ (E0 + E3 * t ^ q) + n * ε * ((1 - t) * m t) := by
          have : (1 - t) * (E0 + E3 * t ^ q) ≤ E0 + E3 * t ^ q := by
            have h3 : 0 ≤ E0 + E3 * t ^ q := add_nonneg hE0 h2
            nlinarith [ht.1]
          linarith
      _ = G t := by simp only [hG]
  have hsub : ∫ t in Ioc (0 : ℝ) 1, ((1 - t) * V t - n * ((1 - t) * m t)) =
      (∫ t in Ioc (0 : ℝ) 1, (1 - t) * V t) - n * ∫ t in Ioc (0 : ℝ) 1, (1 - t) * m t := by
    rw [integral_sub hV (hm.const_mul n), integral_const_mul]
  rw [← hsub, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hGint (ae_restrict_of_forall_mem measurableSet_Ioc hbd)).trans ?_
  have hGval : ∫ t in Ioc (0 : ℝ) 1, G t =
      E0 + E3 * (1 / (q + 1)) + n * ε * ∫ t in Ioc (0 : ℝ) 1, (1 - t) * m t := by
    have h1 : IntegrableOn (fun t : ℝ => E0 + E3 * t ^ q) (Ioc (0 : ℝ) 1) :=
      (hconst E0).add (hpow.const_mul E3)
    have h2 : IntegrableOn (fun t : ℝ => n * ε * ((1 - t) * m t)) (Ioc (0 : ℝ) 1) :=
      hm.const_mul (n * ε)
    have h3 : IntegrableOn (fun t : ℝ => E3 * t ^ q) (Ioc (0 : ℝ) 1) := hpow.const_mul E3
    simp only [hG]
    rw [integral_add h1 h2, integral_add (hconst E0) h3, integral_const_mul, integral_const_mul,
      hpowint]
    simp
  exact le_of_eq hGval

/-! ### The main estimate -/

set_option maxHeartbeats 1600000 in
theorem s76_main (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (hβ : 0 < β)
    (hM0 : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ Λ : ℝ≥0, LipschitzWith Λ ρ → ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, 3 ≤ N → ∀ x : Euc d,
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          HRS.Whole.CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t) ∧
        DifferentiableWithinAt ℝ
          (HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x) (Set.Ici 0) 0 ∧
        |HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x /
              ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) -
            2 * HRS.Whole.biasConst d s * ρ x| ≤
          K * ((N : ℝ) ^ (-HRS.Whole.biasTau d s) + Λ * (β / N) ^ (1 / s) * L +
            L ^ (-((2 * s - d) / 2)) +
            (N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s * L ^ (2 * ((d : ℝ) - s))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  obtain ⟨K1, K2, K3, CA, hK1, hK2, hK3, hpt⟩ := s76_pointwise hd hs hsd β M hβ hM0
  obtain ⟨C0', hSI⟩ := HRS.MS.Wr.static_input_proof hd hs hsd β M hβ
  obtain ⟨Ck, hCk0, hCk⟩ := s76_kk_tail_le hd1 hs0 hds
  obtain ⟨Cri, hCri0, hradI⟩ := HRS.MS.Wr.wr13c_radial_J_integral hd1 hs0 hsd M
  obtain ⟨hk0, hkint, hK⟩ := s76_kk_facts hd hs hsd
  have hb0 : 0 ≤ HRS.Whole.biasConst d s := by
    have := integral_nonneg (μ := (volume : Measure (Euc d)))
      (f := fun u : Euc d => HRS.Whole.Q34.kk (‖u‖ ^ (-s))) (fun u => hk0 u)
    rw [hK] at this; linarith
  set b : ℝ := HRS.Whole.biasConst d s with hb
  refine ⟨K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b, by positivity, ?_⟩
  intro ρ hρ hM Λ hΛ L hL N hN x
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  haveI hμprob := HRS.MS.Wr.wr13a_isProb_density hρ
  have hconv := HRS.MS.Wr.wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hlam0 : 0 < β / (N : ℝ) := by positivity
  have hc : 0 < (β / (N : ℝ)) ^ (1 / s) := Real.rpow_pos_of_pos hlam0 _
  -- the first two conclusions
  have hCWD : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HRS.Whole.CavityWellDefined d s N β (HRS.Whole.withDensityReal ρ) x t :=
    fun t ht => ((hSI ρ hρ hM N (by omega)).2.2.2.1 x t ht).1
  obtain ⟨hder, hdef⟩ := HRS.MS.Wr.wr13c2_insertionDefect_eq hd hs0 hsd hρ hM hβ.le
    (by omega : 2 ≤ N) x
  refine ⟨hCWD, hder.differentiableWithinAt, ?_⟩
  -- the defect as a weighted integral of the variance
  haveI hP0 := HRS.MS.Wr.wr13a_cavityLaw_isProb hs0 hconv hβ.le N
  obtain ⟨hVint, hDid⟩ := s76_defect_eq
    (P := HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ))
    (HRS.MS.Wr.wr13c2_X_meas hs0 N β x) (HRS.MS.Wr.wr13c2_X_le_zero hs0 hβ.le N x)
    (HRS.MS.Wr.wr13c2_integrable_X hd hs0 hsd hρ hM hβ.le (by omega) x)
  have hD : HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x =
      ∫ t in Ioc (0 : ℝ) 1, (1 - t) * Var[HRS.MS.Wr.wr13c2_X d s N β x;
        (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
          (fun Y => t * HRS.MS.Wr.wr13c2_X d s N β x Y)] := hdef.trans hDid
  -- the diagonal integral
  obtain ⟨hm0int, hm0val⟩ := s76_m0_int hd hs hsd hρ hM hlam0 hL0 x
    (fun u hu => (hradI ρ hρ hM u hu x).1)
  have hcN : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
  have hn2 : (2 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N - 1)
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by linarith
  obtain ⟨hIL0, hIL1⟩ := s76_IL_bounds hd hs hsd hρ hM ((β / (N : ℝ)) ^ (1 / s)) L x
  have hILapp := s76_IL_approx hd hs hsd hρ hM hΛ hc hL0 hCk x
  set IL : ℝ := s76_IL d s ρ ((β / (N : ℝ)) ^ (1 / s)) L x with hIL
  set P : ℝ := (β / (N : ℝ)) ^ ((d : ℝ) / s) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hlam0 _
  set q : ℝ := ((d : ℝ) / s - 2) / 2 with hq
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
  have hqm : -1 < q := by rw [hq]; linarith
  have hq1 : 1 / (q + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; rw [hq]; linarith
  set E0 : ℝ := K1 * (n ^ 2 * (P ^ 2 * (L ^ ((d : ℝ) - s)) ^ 2)) +
    K2 * (n * P * L ^ ((d : ℝ) - 2 * s)) with hE0
  set E3 : ℝ := K3 * (n * P * L ^ (((d : ℝ) - 2 * s) / 2)) with hE3
  have hLs : 0 ≤ L ^ ((d : ℝ) - s) := Real.rpow_nonneg hL0.le _
  have hLs2 : 0 ≤ L ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hL0.le _
  have hLh : 0 ≤ L ^ (((d : ℝ) - 2 * s) / 2) := Real.rpow_nonneg hL0.le _
  have hE0n : 0 ≤ E0 := by rw [hE0]; positivity
  have hE3n : 0 ≤ E3 := by rw [hE3]; positivity
  have hptt : ∀ t ∈ Ioc (0 : ℝ) 1,
      |Var[HRS.MS.Wr.wr13c2_X d s N β x; (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).tilted
          (fun Y => t * HRS.MS.Wr.wr13c2_X d s N β x Y)] -
        n * s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x t| ≤
      E0 + E3 * t ^ q + n * (CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) *
        s76_m0 d s (HRS.Whole.withDensityReal ρ) (β / (N : ℝ)) ((β / (N : ℝ)) ^ (1 / s) * L) x t := by
    intro t ht
    refine (hpt ρ hρ hM N hN x L hL t ht).trans (le_of_eq ?_)
    rw [hE0, hE3]; ring
  have hint := s76_integrate (E0 := E0) (E3 := E3) (q := q) (n := n)
    (ε := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) hE0n hE3n hqm hVint hm0int hptt
  rw [hm0val, ← hD] at hint
  -- division by `n P`
  have hA : 0 < n * P := mul_pos hn0 hP0
  set D : ℝ := HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x with hDdef
  set eps : ℝ := CA * (N : ℝ) ^ (-HRS.Whole.biasTau d s) with hepsdef
  have hbiasP : HRS.Whole.biasP d s = (d : ℝ) / s := rfl
  have hdiv : |D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) - IL| ≤
      K1 * (n * P * (L ^ ((d : ℝ) - s)) ^ 2) + K2 * L ^ ((d : ℝ) - 2 * s) +
        K3 * L ^ (((d : ℝ) - 2 * s) / 2) * (1 / (q + 1)) + eps * IL := by
    rw [hbiasP, ← hcN, ← hP]
    have e1 : D / (n * P) - IL = (D - n * (P * IL)) / (n * P) := by
      field_simp
    rw [e1, abs_div, abs_of_pos hA, div_le_iff₀ hA]
    refine hint.trans (le_of_eq ?_)
    rw [hE0, hE3]
    field_simp
  -- the Lipschitz and tail estimates
  have hLpow : L ^ ((d : ℝ) - 2 * s) ≤ L ^ (-((2 * s - d) / 2)) := by
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    linarith
  have hLeq : L ^ (((d : ℝ) - 2 * s) / 2) = L ^ (-((2 * s - d) / 2)) := by
    congr 1; ring
  have hLsq : (L ^ ((d : ℝ) - s)) ^ 2 = L ^ (2 * ((d : ℝ) - s)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have hT1 : 0 ≤ (N : ℝ) ^ (-HRS.Whole.biasTau d s) := Real.rpow_nonneg hNpos.le _
  have hT2 : 0 ≤ (Λ : ℝ) * (β / (N : ℝ)) ^ (1 / s) * L := by positivity
  have hT3 : 0 ≤ L ^ (-((2 * s - d) / 2)) := Real.rpow_nonneg hL0.le _
  have hT4 : 0 ≤ n * P * L ^ (2 * ((d : ℝ) - s)) := by positivity
  have hεIL : eps * IL ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) * (M * (2 * b)) := by
    have h1 : eps ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hT1
    calc eps * IL ≤ (|CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) * IL :=
          mul_le_mul_of_nonneg_right h1 hIL0
      _ ≤ (|CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s)) * (M * (2 * b)) :=
          mul_le_mul_of_nonneg_left hIL1 (mul_nonneg (abs_nonneg _) hT1)
  have hmain : |D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) - 2 * b * ρ x| ≤
      K1 * (n * P * (L ^ ((d : ℝ) - s)) ^ 2) + K2 * L ^ ((d : ℝ) - 2 * s) +
        K3 * L ^ (((d : ℝ) - 2 * s) / 2) * (1 / (q + 1)) + eps * IL +
      (2 * b * (Λ * (β / (N : ℝ)) ^ (1 / s) * L) + M * (Ck * L ^ ((d : ℝ) - 2 * s))) := by
    have := abs_sub_le (D / ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s)) IL (2 * b * ρ x)
    linarith
  refine hmain.trans ?_
  -- compare with the right-hand side
  rw [hbiasP, ← hcN, ← hP, hLsq, hLeq]
  have hnn : 0 ≤ M * Ck := mul_nonneg hM0 hCk0
  have hnb : 0 ≤ 2 * b * M * |CA| := by positivity
  have f1 : K2 * L ^ ((d : ℝ) - 2 * s) ≤ K2 * L ^ (-((2 * s - d) / 2)) :=
    mul_le_mul_of_nonneg_left hLpow hK2
  have f2 : K3 * L ^ (-((2 * s - d) / 2)) * (1 / (q + 1)) ≤ 2 * K3 * L ^ (-((2 * s - d) / 2)) := by
    have h0 : 0 ≤ K3 * L ^ (-((2 * s - d) / 2)) := mul_nonneg hK3 hT3
    calc K3 * L ^ (-((2 * s - d) / 2)) * (1 / (q + 1)) ≤ K3 * L ^ (-((2 * s - d) / 2)) * 2 :=
          mul_le_mul_of_nonneg_left hq1 h0
      _ = 2 * K3 * L ^ (-((2 * s - d) / 2)) := by ring
  have f3 : M * (Ck * L ^ ((d : ℝ) - 2 * s)) ≤ M * Ck * L ^ (-((2 * s - d) / 2)) := by
    calc M * (Ck * L ^ ((d : ℝ) - 2 * s)) = (M * Ck) * L ^ ((d : ℝ) - 2 * s) := by ring
      _ ≤ (M * Ck) * L ^ (-((2 * s - d) / 2)) := mul_le_mul_of_nonneg_left hLpow hnn
  have f4 : eps * IL ≤ (2 * b * M * |CA|) * (N : ℝ) ^ (-HRS.Whole.biasTau d s) := by
    calc eps * IL ≤ |CA| * (N : ℝ) ^ (-HRS.Whole.biasTau d s) * (M * (2 * b)) := hεIL
      _ = (2 * b * M * |CA|) * (N : ℝ) ^ (-HRS.Whole.biasTau d s) := by ring
  have hKa : K1 ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have hKb : K2 + 2 * K3 + M * Ck ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by
    linarith
  have hKc : 2 * b * M * |CA| ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have hKd : 2 * b ≤ K1 + K2 + M * Ck + 2 * K3 + 2 * b * M * |CA| + 2 * b := by linarith
  have g1 := mul_le_mul_of_nonneg_right hKa hT4
  have g3 := mul_le_mul_of_nonneg_right hKb hT3
  have g2 := mul_le_mul_of_nonneg_right hKc hT1
  have g4 := mul_le_mul_of_nonneg_right hKd hT2
  nlinarith [f1, f2, f3, f4, g1, g2, g3, g4]

/-! ### The rate -/

set_option maxHeartbeats 800000 in
theorem s76_rate_main (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (Λ : ℝ≥0)
    (hβ : 0 < β) (hM0 : 0 ≤ M) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      LipschitzWith Λ ρ → ∀ N : ℕ, 3 ≤ N → ∀ x : Euc d,
        |HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x /
              ((N - 1 : ℝ) * (β / N) ^ HRS.Whole.biasP d s) -
            2 * HRS.Whole.biasConst d s * ρ x| ≤ C * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨K, hK0, hmain⟩ := s76_main hd hs hsd β M hβ hM0
  refine ⟨K * (1 + (Λ : ℝ) * β ^ (1 / s) + 1 + β ^ ((d : ℝ) / s)), fun ρ hρ hM hΛ N hN x => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  set Nr : ℝ := (N : ℝ) with hNr
  set p : ℝ := (d : ℝ) / s with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
  have hp0 : 0 < p := by linarith
  set θ : ℝ := HRS.Whole.biasTheta d s with hθ
  have hθτ : θ ≤ (p - 1) ^ 2 / p := by
    rw [hθ]; exact min_le_left _ _
  have hθ2 : θ ≤ (2 - p) / 8 := by
    rw [hθ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ 3 / (4 * s) := by
    rw [hθ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hτ : HRS.Whole.biasTau d s = (p - 1) ^ 2 / p := rfl
  have hmono : ∀ a : ℝ, θ ≤ a → Nr ^ (-a) ≤ Nr ^ (-θ) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hL1 : 1 ≤ Nr ^ (1 / (4 * s)) := Real.one_le_rpow hN1 (by positivity)
  obtain ⟨-, -, hb⟩ := hmain ρ hρ hM Λ hΛ (Nr ^ (1 / (4 * s))) hL1 N hN x
  refine hb.trans ?_
  have hNθ : 0 ≤ Nr ^ (-θ) := Real.rpow_nonneg hNpos.le _
  -- the four terms
  have t1 : Nr ^ (-HRS.Whole.biasTau d s) ≤ Nr ^ (-θ) := hmono _ (by rw [hτ]; exact hθτ)
  have e2 : (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) = β ^ (1 / s) * Nr ^ (-(3 / (4 * s))) := by
    rw [Real.div_rpow hβ.le hNpos.le, div_eq_mul_inv, ← Real.rpow_neg hNpos.le, mul_assoc,
      ← Real.rpow_add hNpos]
    congr 2
    field_simp
    ring
  have t2 : (Λ : ℝ) * (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) ≤ (Λ : ℝ) * β ^ (1 / s) * Nr ^ (-θ) := by
    rw [mul_assoc, e2, ← mul_assoc]
    have := hmono _ hθ3
    have h0 : 0 ≤ (Λ : ℝ) * β ^ (1 / s) := mul_nonneg (NNReal.coe_nonneg Λ) (Real.rpow_nonneg hβ.le _)
    exact mul_le_mul_of_nonneg_left this h0
  have e3 : (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) = Nr ^ (-((2 - p) / 8)) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    rw [hp]
    field_simp
    ring
  have t3 : (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) ≤ Nr ^ (-θ) := by
    rw [e3]; exact hmono _ hθ2
  have e4 : (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)) = Nr ^ ((p - 1) / 2) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    rw [hp]
    field_simp
    ring
  have hθ4 : θ ≤ (p - 1) / 2 := by
    refine hθτ.trans ?_
    rw [div_le_iff₀ hp0]
    nlinarith
  have t4 : (Nr - 1) * (β / Nr) ^ p * (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)) ≤
      β ^ p * Nr ^ (-θ) := by
    rw [e4, Real.div_rpow hβ.le hNpos.le, div_eq_mul_inv, ← Real.rpow_neg hNpos.le]
    have h1 : (Nr - 1) * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) ≤
        Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) := by
      have : 0 ≤ β ^ p * Nr ^ (-p) := mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hNpos.le _)
      have h2 : 0 ≤ Nr ^ ((p - 1) / 2) := Real.rpow_nonneg hNpos.le _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) this) h2
    have h3 : Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) = β ^ p * Nr ^ (-((p - 1) / 2)) := by
      have : Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2) = Nr ^ (-((p - 1) / 2)) := by
        calc Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2) = Nr ^ (1 : ℝ) * Nr ^ (-p) * Nr ^ ((p - 1) / 2) := by
              rw [Real.rpow_one]
          _ = Nr ^ (1 + -p + (p - 1) / 2) := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          _ = Nr ^ (-((p - 1) / 2)) := by congr 1; ring
      calc Nr * (β ^ p * Nr ^ (-p)) * Nr ^ ((p - 1) / 2) = β ^ p * (Nr * Nr ^ (-p) * Nr ^ ((p - 1) / 2)) := by
            ring
        _ = _ := by rw [this]
    refine h1.trans (le_of_eq h3 |>.trans ?_)
    exact mul_le_mul_of_nonneg_left (hmono _ hθ4) (Real.rpow_nonneg hβ.le _)
  have hbp : HRS.Whole.biasP d s = p := rfl
  rw [hbp] at hb ⊢
  calc K * (Nr ^ (-HRS.Whole.biasTau d s) + (Λ : ℝ) * (β / Nr) ^ (1 / s) * Nr ^ (1 / (4 * s)) +
        (Nr ^ (1 / (4 * s))) ^ (-((2 * s - d) / 2)) +
        (Nr - 1) * (β / Nr) ^ p * (Nr ^ (1 / (4 * s))) ^ (2 * ((d : ℝ) - s)))
      ≤ K * (Nr ^ (-θ) + (Λ : ℝ) * β ^ (1 / s) * Nr ^ (-θ) + Nr ^ (-θ) + β ^ p * Nr ^ (-θ)) :=
        mul_le_mul_of_nonneg_left (by linarith [t1, t2, t3, t4]) hK0
    _ = K * (1 + (Λ : ℝ) * β ^ (1 / s) + 1 + β ^ p) * Nr ^ (-θ) := by ring

/-! ### The frozen statements -/

/-- **Proposition S7.6** (`HRS.Whole.sharp_insertion_radius`): the threshold `N₀` can be taken
before `L` (it is `3`, independent of `L`: the proof is uniform in `L ≥ 1`). -/
theorem sharp_insertion_radius_proof : type_of% @HRS.Whole.sharp_insertion_radius := by
  intro d s hd hs hsd β M hβ
  by_cases hM0 : 0 ≤ M
  · obtain ⟨K, -, hmain⟩ := s76_main hd hs hsd β M hβ hM0
    exact ⟨K, 3, fun L hL N hN ρ hρ hM Λ hΛ x => hmain ρ hρ hM Λ hΛ L hL N hN x⟩
  · exact ⟨0, 0, fun L hL N hN ρ hρ hM Λ hΛ x => absurd ((hρ.nonneg 0).trans (hM 0)) hM0⟩

/-- **Proposition S7.6, rate** (`HRS.Whole.sharp_insertion_rate`), `L = N^{1/(4s)}`. -/
theorem sharp_insertion_rate_proof : type_of% @HRS.Whole.sharp_insertion_rate := by
  intro d s hd hs hsd β M Λ hβ
  by_cases hM0 : 0 ≤ M
  · obtain ⟨C, hC⟩ := s76_rate_main hd hs hsd β M Λ hβ hM0
    exact ⟨C, 3, fun N hN ρ hρ hM hΛ x => hC ρ hρ hM hΛ N hN x⟩
  · exact ⟨0, 0, fun N hN ρ hρ hM hΛ x => absurd ((hρ.nonneg 0).trans (hM 0)) hM0⟩

end HRS.MS.S76
