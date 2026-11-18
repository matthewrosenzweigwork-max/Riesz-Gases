import HRS.MS.UlNlAux3

/-!
# UL-1 (S5.1 nonlocal term as a map `H^m_ul → H^{m-2+(d-s)} + C_b^{m-1}`)

Files: `UlNlAux1` (`ulNL`, `generatorW_fixed`, cutoff, far kernel), `UlNlAux2` (cancellation integration by
parts `ul1_ibp`, decomposition `ul1_nl_decomp`), `UlNlAux3` (Sobolev norms from pointwise envelopes, weights,
weighted mass), `UlNl` (this file).  Helper lemmas carry the prefix `ul1_`; namespace `HRS.MS.Ul`.

Main results (statements in terms of `ulocNormE m χ`, constants uniform in `u`):

* `ulNL`, `generatorW_fixed` (`UlNlAux1`): the nonlocal term and the unfolding of the generator of
  `fixedViscosityCoeff` at time `0`;
* `ul_nl_bound`: for `0 ≤ s < d`, `ρ` Schwartz, `2 ≤ m`, every `u ∈ C^m` with `‖u‖_{H^m_uloc} < ∞` satisfies
  `ulNL u = n + f` with `‖n‖_{H^{m-2+(d-s)}} ≤ C ‖u‖_{H^m_uloc}` and `‖f‖_{C_b^{m-1}} ≤ C ‖u‖_{H^m_uloc}`;
* `ul_nl_cont`, `ul_nl_sub`, `ul_nl_lip`: for `u ∈ C_b^m`, `3 ≤ m`, `ulNL u ∈ C_b^{m-2}` with
  `‖ulNL u‖_{C_b^{m-2}} ≤ C ‖u‖_{C_b^m}`, linearity, and the Lipschitz estimate for differences
  (`m = 4` gives `C_b^2`, the form needed for `cont_time_deriv`).

Adjustments of the sketch of `docs/UL_PLAN.md` (all harmless, none weakens the mathematical content):
the cutoff hypothesis `IsUlocCutoff χ` is explicit; `ρ` Schwartz is `∃ ψ : SchwartzMap, ⇑ψ = ρ`; the
weighted bounds are packaged as `‖div F‖_{H^{m-2}(ℝ^d)} ≤ C ‖u‖_{H^m_uloc}` (`ul1_sobolev_G`) and
`‖F_j‖_{L¹} ≤ C ‖u‖_{H^m_uloc}` (`ul1_L1_F`), which is what the near and far parts use (the far kernel is
differentiated, not `F`); the continuity statement loses exactly two derivatives (`C_b^m → C_b^{m-2}`),
proved directly (no Sobolev embedding).  Route: `convGradConvW (∇g) F_j = (θ'g) * div F + ∑_j K_j * F_j`
(`ul1_ulNL_eq`; cancellation integration by parts `ul1_ibp` with boundary term `O(ε^{d-s'})`,
`s' = (s+d)/2`), TC-3 (`tc3_riesz_loc_sobolevNormE_gain`) for the near part, and the bounded smooth far
kernel `K_j = ∂_j((1-θ')g)` against `F_j ∈ L¹`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.MP.RdInit HRS.PDE.ToolboxRd HRS.Whole.AppendixA

variable {d : ℕ}

/-- Cauchy-Schwarz for nonnegative continuous functions with integrable squares. -/
theorem ul1_holder_L1 {a b : Euc d → ℝ} (ha0 : ∀ y, 0 ≤ a y) (hb0 : ∀ y, 0 ≤ b y)
    (hac : Continuous a) (hbc : Continuous b)
    (ha2 : Integrable (fun y => a y ^ 2)) (hb2 : Integrable (fun y => b y ^ 2)) :
    Integrable (fun y => a y * b y) ∧
      ∫ y, a y * b y ≤ Real.sqrt (∫ y, a y ^ 2) * Real.sqrt (∫ y, b y ^ 2) := by
  refine ⟨?_, ?_⟩
  · refine ((ha2.add hb2).div_const 2).mono' (hac.mul hbc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 y) (hb0 y))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (a y - b y)]
  · have h2a : MemLp a (ENNReal.ofReal 2) volume := by
      rw [show ENNReal.ofReal 2 = 2 by simp]
      exact (memLp_two_iff_integrable_sq hac.aestronglyMeasurable).2 ha2
    have h2b : MemLp b (ENNReal.ofReal 2) volume := by
      rw [show ENNReal.ofReal 2 = 2 by simp]
      exact (memLp_two_iff_integrable_sq hbc.aestronglyMeasurable).2 hb2
    have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall ha0) (Filter.Eventually.of_forall hb0) h2a h2b
    simp only [Real.rpow_two, one_div] at this
    simpa [Real.sqrt_eq_rpow, one_div] using this

/-- the basic integrals: `q = ⟨y⟩^{-(d+1)}`, `b = ϖ^{1/2} (∑_{b ≤ m} |D^b u|²)^{1/2}` -/
theorem ul1_qb {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m : ℕ) (hd : 0 < d) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ →
      Integrable (fun y => ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y))) ∧
      Integrable (fun y => (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2) ∧
      ∫ y, (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2 ≤ C0 * (ulocNormE m χ u).toReal ^ 2 ∧
      ∫ y, ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y)) ≤ C1 * (ulocNormE m χ u).toReal := by
  obtain ⟨C0, hC00, hC0⟩ := ul1_weighted_mass hχ m hd
  set Q : ℝ := ∫ y : Euc d, ul1q d y ^ 2 with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun y => sq_nonneg _
  refine ⟨C0, Real.sqrt Q * Real.sqrt C0, hC00, by positivity, fun u hu hU => ?_⟩
  obtain ⟨hI, hIb⟩ := hC0 u hu hU
  have hb2 : ∀ y, (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2 =
      jbracket y ^ (-((d : ℝ) + 3)) * mriG m u y := by
    intro y
    rw [mul_pow, Real.sq_sqrt (mriG_nonneg _ _ _), show ul1wt d y ^ 2 = _ from ul1_jb_sq y]
  have hbc : Continuous (fun y => ul1wt d y * Real.sqrt (mriG m u y)) :=
    (ul1_jb_rpow_cont _).mul (mriG_continuous hu).sqrt
  have hqc : Continuous (ul1q d : Euc d → ℝ) := ul1_jb_rpow_cont _
  have hI2 : Integrable (fun y => (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2) := by
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (hb2 y).symm
  have hIb2 : ∫ y, (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2 ≤ C0 * (ulocNormE m χ u).toReal ^ 2 := by
    simp_rw [hb2]; exact hIb
  obtain ⟨hint, hcs⟩ := ul1_holder_L1 (a := ul1q d) (b := fun y => ul1wt d y * Real.sqrt (mriG m u y))
    (fun y => ul1_q_nonneg y) (fun y => mul_nonneg (ul1_wt_nonneg y) (Real.sqrt_nonneg _)) hqc hbc
    ul1_q_sq_integrable hI2
  refine ⟨hint, hI2, hIb2, hcs.trans ?_⟩
  rw [mul_assoc]
  have h1 : Real.sqrt (∫ y, (ul1wt d y * Real.sqrt (mriG m u y)) ^ 2) ≤
      Real.sqrt C0 * (ulocNormE m χ u).toReal := by
    calc _ ≤ Real.sqrt (C0 * (ulocNormE m χ u).toReal ^ 2) := Real.sqrt_le_sqrt hIb2
      _ = _ := by rw [Real.sqrt_mul hC00, Real.sqrt_sq ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

theorem ul1_F_contDiff (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (hm : 1 ≤ m) {u : Euc d → ℝ} (hu : ContDiff ℝ m u) (j : Fin d) :
    ContDiff ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := by
  have hd : ContDiff ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (by
      have : m - 1 + 1 = m := by omega
      exact_mod_cast this.le)
  exact (ψ.smooth _).mul (hd.clm_apply contDiff_const)

/-- `div F` for `F_j = ρ ∂_{w_j} u` -/
def ul1G (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (u : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∑ j, fderiv ℝ (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y (EuclideanSpace.single j 1)

theorem ul1_env_G (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ∀ k : ℕ, k + 2 ≤ m → ∀ y,
      ‖iteratedFDeriv ℝ k (ul1G ψ M u) y‖ ≤ A * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y) := by
  obtain ⟨A, hA0, hA⟩ := ul1_env_F ψ M m
  refine ⟨d * A, by positivity, fun u hu k hk y => ?_⟩
  have hFj : ∀ j : Fin d, ContDiff ℝ ((m - 1 : ℕ) : WithTop ℕ∞)
      (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := fun j => ul1_F_contDiff ψ M (by omega) hu j
  have hfj : ∀ j : Fin d, ContDiff ℝ (k : WithTop ℕ∞)
      (fun y => fderiv ℝ (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y (EuclideanSpace.single j 1)) := by
    intro j
    exact ((hFj j).fderiv_right (m := (k : WithTop ℕ∞)) (by
      have : k + 1 ≤ m - 1 := by omega
      exact_mod_cast this)).clm_apply contDiff_const
  have hsum : ul1G ψ M u = ∑ j : Fin d, fun y =>
      fderiv ℝ (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y (EuclideanSpace.single j 1) := by
    funext z; simp [ul1G, Finset.sum_apply]
  rw [hsum, iteratedFDeriv_sum_apply (fun j _ => (hfj j).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      ‖iteratedFDeriv ℝ k (fun y =>
        fderiv ℝ (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y (EuclideanSpace.single j 1)) y‖ ≤
      A * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y) := by
    intro j _
    have hd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ (fun y => ψ y * fderiv ℝ u y (ul1w M j))) :=
      (hFj j).fderiv_right (by
        have : k + 1 ≤ m - 1 := by omega
        exact_mod_cast this)
    refine (norm_iteratedFDeriv_clm_apply_const (N := (k : WithTop ℕ∞))
      (c := (EuclideanSpace.single j (1 : ℝ) : Euc d)) (n := k) hd.contDiffAt le_rfl).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    simp only [EuclideanSpace.norm_single, norm_one, one_mul]
    exact hA u hu j (k + 1) (by omega) y
  calc _ ≤ ∑ _j : Fin d, A * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y) :=
        Finset.sum_le_sum hj
    _ = _ := by simp [Finset.sum_const]; ring

theorem ul1_G_contDiff (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (hm : 2 ≤ m) {u : Euc d → ℝ} (hu : ContDiff ℝ m u) :
    ContDiff ℝ ((m - 2 : ℕ) : WithTop ℕ∞) (ul1G ψ M u) := by
  refine ContDiff.sum fun j _ => ?_
  exact ((ul1_F_contDiff ψ M (by omega) hu j).fderiv_right (m := ((m - 2 : ℕ) : WithTop ℕ∞)) (by
    have : m - 2 + 1 ≤ m - 1 := by omega
    exact_mod_cast this)).clm_apply contDiff_const

/-- Sobolev bound for `div F`. -/
theorem ul1_sobolev_G {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (ψ : SchwartzMap (Euc d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (hm : 2 ≤ m) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ →
      HRS.PDE.ToolboxRd.MemSobolev (((m - 2 : ℕ) : ℝ)) (ul1G ψ M u) ∧
      sobolevNormE (((m - 2 : ℕ) : ℝ)) (ul1G ψ M u) ≤ ENNReal.ofReal C * ulocNormE m χ u := by
  obtain ⟨A, hA0, hA⟩ := ul1_env_G ψ M m
  obtain ⟨C0, C1, hC00, hC10, hqb⟩ := ul1_qb hχ m hd
  set Cs : ℝ := ∑ j ∈ Finset.range (m - 2 + 1), ((m - 2).choose j : ℝ) * (d : ℝ) ^ j with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨Real.sqrt (Cs * (A ^ 2 * C0)), by positivity, fun u hu hU => ?_⟩
  obtain ⟨hint, hI2, hIb2, -⟩ := hqb u hu hU
  set b : Euc d → ℝ := fun y => ul1wt d y * Real.sqrt (mriG m u y) with hb
  set w : Euc d → ℝ := fun y => A * (ul1q d y * b y) with hw
  have hGu := ul1_G_contDiff ψ M hm hu
  have hbc : Continuous b := (ul1_jb_rpow_cont _).mul (mriG_continuous hu).sqrt
  have hqc : Continuous (ul1q d : Euc d → ℝ) := ul1_jb_rpow_cont _
  have hwc : Continuous w := continuous_const.mul (hqc.mul hbc)
  have hw1 : Integrable w := hint.const_mul A
  have hwsq : ∀ y, w y ^ 2 ≤ A ^ 2 * b y ^ 2 := fun y => by
    simp only [hw]
    have hq0 := ul1_q_nonneg (d := d) y
    have hq1 : ul1q d y ^ 2 ≤ 1 := by
      calc ul1q d y ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hq0 (ul1_q_le_one y) 2
        _ = 1 := one_pow 2
    calc (A * (ul1q d y * b y)) ^ 2 = A ^ 2 * (ul1q d y ^ 2 * b y ^ 2) := by ring
      _ ≤ A ^ 2 * (1 * b y ^ 2) := by gcongr
      _ = _ := by ring
  have hw2 : Integrable (fun y => w y ^ 2) :=
    (hI2.const_mul (A ^ 2)).mono' (hwc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hwsq y)
  have henv : ∀ j ≤ m - 2, ∀ y, ‖iteratedFDeriv ℝ j (ul1G ψ M u) y‖ ≤ w y := by
    intro j hj y
    have := hA u hu j (by omega) y
    simp only [hw, hb]
    calc _ ≤ _ := this
      _ = _ := by ring
  obtain ⟨hmem, hsq⟩ := ul1_sobolev_env hGu hw1 hw2 henv
  have hint2 : ∫ y, w y ^ 2 ≤ A ^ 2 * (C0 * (ulocNormE m χ u).toReal ^ 2) := by
    calc ∫ y, w y ^ 2 ≤ ∫ y, A ^ 2 * b y ^ 2 := integral_mono hw2 (hI2.const_mul _) hwsq
      _ = A ^ 2 * ∫ y, b y ^ 2 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hIb2 (sq_nonneg _)
  refine ⟨hmem, ?_⟩
  unfold sobolevNormE
  rw [if_pos hmem]
  have hsq2 : HRS.PDE.ToolboxRd.sobolevNormSq ((m - 2 : ℕ) : ℝ) (ul1G ψ M u) ≤
      (Real.sqrt (Cs * (A ^ 2 * C0)) * (ulocNormE m χ u).toReal) ^ 2 := by
    calc _ ≤ Cs * ∫ y, w y ^ 2 := hsq
      _ ≤ Cs * (A ^ 2 * (C0 * (ulocNormE m χ u).toReal ^ 2)) := mul_le_mul_of_nonneg_left hint2 hCs0
      _ = _ := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hfin : (ulocNormE m χ u).toReal = (ulocNormE m χ u).toReal := rfl
  calc ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((m - 2 : ℕ) : ℝ) (ul1G ψ M u)))
      ≤ ENNReal.ofReal (Real.sqrt (Cs * (A ^ 2 * C0)) * (ulocNormE m χ u).toReal) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ Real.sqrt ((Real.sqrt (Cs * (A ^ 2 * C0)) * (ulocNormE m χ u).toReal) ^ 2) :=
              Real.sqrt_le_sqrt hsq2
          _ = _ := Real.sqrt_sq (by positivity)
    _ = ENNReal.ofReal (Real.sqrt (Cs * (A ^ 2 * C0))) * ulocNormE m χ u := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hU.ne]

theorem ul1_le_top (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top

/-- convolution of a `C^N` kernel with bounded derivatives of order `≤ N` and an `L¹` function -/
theorem ul1_conv_smooth {K : Euc d → ℝ} {N : ℕ} (hK : ContDiff ℝ N K) {Bn : ℕ → ℝ}
    (hB : ∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n K z‖ ≤ Bn n) {F : Euc d → ℝ} (hF : Integrable F)
    (hN : 1 ≤ N) :
    ContDiff ℝ N (fun x => ∫ y, F y * K (x - y)) ∧
      ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (fun x => ∫ y, F y * K (x - y)) x‖ ≤
        Bn n * ∫ y, |F y| := by
  set g : Euc d → Euc d → ℝ := fun y x => F y * K (x - y) with hg
  have hKN : ∀ n : ℕ, n ≤ N → ContDiff ℝ n K := fun n hn => hK.of_le (by exact_mod_cast hn)
  have hgd : ∀ p n x, n ≤ N → iteratedFDeriv ℝ n (g p) x = F p • iteratedFDeriv ℝ n K (x - p) := by
    intro p n x hn
    have h1 : g p = fun x => F p • (fun z => K (z - p)) x := by funext z; simp [hg]
    have hcd : ContDiffAt ℝ n (fun z => K (z - p)) x :=
      ((hKN n hn).comp (contDiff_id.sub contDiff_const)).contDiffAt
    rw [h1, iteratedFDeriv_const_smul_apply' (a := F p) (f := fun z => K (z - p)) hcd,
      iteratedFDeriv_comp_sub]
  have hbd : ∀ p n x, n ≤ N → ‖iteratedFDeriv ℝ n (g p) x‖ ≤ |F p| * Bn n := by
    intro p n x hn
    rw [hgd p n x hn, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB n hn _) (abs_nonneg _)
  have hmeas : ∀ n ≤ N, ∀ x, AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (g p) x) volume := by
    intro n hn x
    have : (fun p => iteratedFDeriv ℝ n (g p) x) = fun p => F p • iteratedFDeriv ℝ n K (x - p) :=
      funext fun p => hgd p n x hn
    rw [this]
    exact hF.aestronglyMeasurable.smul
      ((((hKN n hn).continuous_iteratedFDeriv le_rfl).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hint : ∀ x, Integrable (fun p => g p x) volume := by
    intro x
    refine hF.mul_bdd (c := Bn 0) ((hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have := hB 0 (Nat.zero_le _) (x - p)
    simpa using this
  have hbi : ∀ n, Integrable (fun p => |F p| * Bn n) volume := fun n => hF.abs.mul_const _
  obtain ⟨hcd, hform⟩ := contDiff_integral_dominated volume g N hN
    (fun p => (contDiff_const.mul (hK.comp (contDiff_id.sub contDiff_const))))
    hint hmeas (fun n p => |F p| * Bn n) (fun j _ _ => hbi j) (fun j _ hjN p x => hbd p j x hjN)
  refine ⟨hcd, fun n hn x => ?_⟩
  rw [hform n hn x]
  calc ‖∫ p, iteratedFDeriv ℝ n (g p) x‖ ≤ ∫ p, |F p| * Bn n :=
        norm_integral_le_of_norm_le (hbi n) (Filter.Eventually.of_forall fun p => hbd p n x hn)
    _ = Bn n * ∫ y, |F y| := by rw [integral_mul_const, mul_comm]

/-- `F_j = ρ ∂_{w_j} u ∈ L¹` with norm `≤ C ‖u‖_{H^m_uloc}` -/
theorem ul1_L1_F {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (ψ : SchwartzMap (Euc d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ → ∀ j : Fin d,
      Integrable (fun y => ψ y * fderiv ℝ u y (ul1w M j)) ∧
      ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)| ≤ C * (ulocNormE m χ u).toReal := by
  obtain ⟨A, hA0, hA⟩ := ul1_env_F ψ M m
  obtain ⟨C0, C1, hC00, hC10, hqb⟩ := ul1_qb hχ m hd
  refine ⟨A * C1, by positivity, fun u hu hU j => ?_⟩
  obtain ⟨hint, -, -, hI1⟩ := hqb u hu hU
  have hFc : Continuous (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := by
    have := (ul1_F_contDiff ψ M hm hu j).continuous
    exact this
  have hb : ∀ y, ‖ψ y * fderiv ℝ u y (ul1w M j)‖ ≤
      A * (ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y))) := by
    intro y
    have := hA u hu j 0 (by omega) y
    simp only [norm_iteratedFDeriv_zero] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hi : Integrable (fun y => A * (ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y)))) :=
    hint.const_mul A
  refine ⟨hi.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall hb), ?_⟩
  calc ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)|
      ≤ ∫ y, A * (ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y))) :=
        integral_mono (hi.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall hb)).abs hi
          fun y => by simpa [Real.norm_eq_abs] using hb y
    _ = A * ∫ y, ul1q d y * (ul1wt d y * Real.sqrt (mriG m u y)) := integral_const_mul _ _
    _ ≤ A * (C1 * (ulocNormE m χ u).toReal) := mul_le_mul_of_nonneg_left hI1 hA0
    _ = _ := by ring

/-- the far part: `∑_j K_j * F_j ∈ C_b^{m-1}` -/
theorem ul1_far {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {s : ℝ} (hs0 : 0 ≤ s)
    (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (hm : 2 ≤ m) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ →
      ∃ f : Euc d → ℝ, (∀ x, ∑ j, ∫ z, ul1K d s j z * (ψ (x - z) * fderiv ℝ u (x - z) (ul1w M j)) = f x) ∧
        MemCb (m - 1) f ∧ cbNorm (m - 1) f ≤ C * (ulocNormE m χ u).toReal := by
  obtain ⟨CL, hCL0, hCL⟩ := ul1_L1_F hχ ψ M m (by omega) hd
  choose Bj hBj using fun (j : Fin d) (n : ℕ) => ul1_K_deriv_bdd (d := d) hs0 j n
  set Sn : ℕ → ℝ := fun n => ∑ j : Fin d, |Bj j n| with hSn
  have hSn0 : ∀ n, 0 ≤ Sn n := fun n => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨(∑ n ∈ Finset.range (m - 1 + 1), Sn n) * CL, by
    exact mul_nonneg (Finset.sum_nonneg fun n _ => hSn0 n) hCL0, fun u hu hU => ?_⟩
  set U := (ulocNormE m χ u).toReal with hUdef
  set Fj : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ u y (ul1w M j) with hFj
  have hFi : ∀ j, Integrable (Fj j) := fun j => (hCL u hu hU j).1
  set fj : Fin d → Euc d → ℝ := fun j x => ∫ y, Fj j y * ul1K d s j (x - y) with hfj
  have hsm : ∀ j, ContDiff ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (fj j) ∧
      ∀ n ≤ m - 1, ∀ x, ‖iteratedFDeriv ℝ n (fj j) x‖ ≤ Bj j n * ∫ y, |Fj j y| := fun j =>
    ul1_conv_smooth (N := m - 1) ((ul1_K_contDiff s j).of_le (ul1_le_top _))
      (fun n _ z => hBj j n z) (hFi j) (by omega)
  set f : Euc d → ℝ := fun x => ∑ j, fj j x with hf
  have hfsum : f = ∑ j : Fin d, fj j := by funext x; simp [hf, Finset.sum_apply]
  have hbound : ∀ n ≤ m - 1, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ Sn n * (CL * U) := by
    intro n hn x
    rw [hfsum, iteratedFDeriv_sum_apply (fun j _ => ((hsm j).1.of_le (by exact_mod_cast hn)).contDiffAt)]
    refine (norm_sum_le _ _).trans ?_
    rw [hSn, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine ((hsm j).2 n hn x).trans ?_
    calc Bj j n * ∫ y, |Fj j y| ≤ |Bj j n| * (CL * U) := by
          refine mul_le_mul (le_abs_self _) (hCL u hu hU j).2 (integral_nonneg fun y => abs_nonneg _)
            (abs_nonneg _)
      _ = _ := rfl
  refine ⟨f, fun x => ?_, ⟨ContDiff.sum fun j _ => (hsm j).1, fun n hn => ⟨Sn n * (CL * U), ?_⟩⟩, ?_⟩
  · -- the `z`-form of the convolution
    refine Finset.sum_congr rfl fun j _ => ?_
    have := integral_sub_left_eq_self (fun z => ul1K d s j z * Fj j (x - z)) volume x
    simp only [sub_sub_cancel] at this
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  · rintro _ ⟨x, rfl⟩
    exact hbound n hn x
  · unfold cbNorm
    calc ∑ n ∈ Finset.range (m - 1 + 1), ⨆ x, ‖iteratedFDeriv ℝ n f x‖
        ≤ ∑ n ∈ Finset.range (m - 1 + 1), Sn n * (CL * U) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' : n ≤ m - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
          exact ciSup_le fun x => hbound n hn' x
      _ = _ := by rw [← Finset.sum_mul]; ring

/-- the decomposition `ulNL u = (θ'g) * div F + ∑_j K_j * F_j` for `u ∈ C^m`, `F_j ∈ L¹` -/
theorem ul1_ulNL_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ψ : SchwartzMap (Euc d) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ} (hm : 2 ≤ m) {u : Euc d → ℝ} (hu : ContDiff ℝ m u)
    (hFi : ∀ j : Fin d, Integrable (fun y => ψ y * fderiv ℝ u y (ul1w M j))) (x : Euc d) :
    ulNL s M ψ u x = HRS.Whole.convFun (ul1H d s) (ul1G ψ M u) x +
      ∑ j, ∫ z, ul1K d s j z * (ψ (x - z) * fderiv ℝ u (x - z) (ul1w M j)) := by
  have hFc : ∀ j : Fin d, ContDiff ℝ 1 (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := fun j =>
    (ul1_F_contDiff ψ M (by omega) hu j).of_le (by
      have : 1 ≤ m - 1 := by omega
      exact_mod_cast this)
  have h := ul1_nl_decomp hs0 hsd (fun j y => ψ y * fderiv ℝ u y (ul1w M j)) hFc hFi x
  unfold ulNL
  simp only [ul1_matVec]
  rw [h]
  rfl

theorem ul1_mem_of_lt_top {r : ℝ} {f : Euc d → ℝ} (h : sobolevNormE r f < ⊤) :
    HRS.PDE.ToolboxRd.MemSobolev r f := by
  by_contra hn
  unfold sobolevNormE at h
  rw [if_neg hn] at h
  exact lt_irrefl _ h

/-- **UL-1 main estimate.**  For `0 ≤ s < d`, a Schwartz `ρ`, `2 ≤ m` and `u ∈ C^m` with finite
`H^m_uloc` norm, the nonlocal term `ulNL u` is the sum of an element of `H^{m-2+(d-s)}(ℝ^d)` and of a
`C_b^{m-1}` function, with norms `≤ C ‖u‖_{H^m_uloc}` (`C` independent of `u`). -/
theorem ul_nl_bound {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ →
      ∃ n f : Euc d → ℝ, (∀ x, ulNL s M ρ u x = n x + f x) ∧
        HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - 2 + ((d : ℝ) - s)) n ∧
        sobolevNormE ((m : ℝ) - 2 + ((d : ℝ) - s)) n ≤ ENNReal.ofReal C * ulocNormE m χ u ∧
        MemCb (m - 1) f ∧ cbNorm (m - 1) f ≤ C * (ulocNormE m χ u).toReal := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  obtain ⟨Cg, hCg0, hG⟩ := ul1_sobolev_G hχ ψ M m hm hd
  obtain ⟨Cf, hCf0, hF⟩ := ul1_far hχ hs0 ψ M m hm hd
  obtain ⟨CL, -, hL⟩ := ul1_L1_F hχ ψ M m (by omega) hd
  obtain ⟨Ct, hCt, hTC⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolevNormE_gain (d := d) (θ := ul1Th d)
    ul1_th_contDiff ul1_th_compact hs0 hsd
  refine ⟨max (Ct * Cg) Cf, le_max_of_le_right hCf0, fun u hu hU => ?_⟩
  obtain ⟨hGmem, hGbd⟩ := hG u hu hU
  obtain ⟨f, hfx, hMemCb, hcb⟩ := hF u hu hU
  have hmr : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub hm]; norm_num
  have hnbd : sobolevNormE ((m : ℝ) - 2 + ((d : ℝ) - s))
      (HRS.Whole.convFun (ul1H d s) (ul1G ψ M u)) ≤ ENNReal.ofReal (max (Ct * Cg) Cf) * ulocNormE m χ u := by
    have h1 := hTC (((m - 2 : ℕ) : ℝ)) (ul1G ψ M u)
    rw [hmr] at h1 hGbd
    refine h1.trans ?_
    calc ENNReal.ofReal Ct * sobolevNormE ((m : ℝ) - 2) (ul1G ψ M u)
        ≤ ENNReal.ofReal Ct * (ENNReal.ofReal Cg * ulocNormE m χ u) := by gcongr
      _ = ENNReal.ofReal (Ct * Cg) * ulocNormE m χ u := by
          rw [← mul_assoc, ENNReal.ofReal_mul hCt.le]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  refine ⟨HRS.Whole.convFun (ul1H d s) (ul1G ψ M u), f, fun x => ?_, ?_, hnbd, hMemCb, ?_⟩
  · rw [ul1_ulNL_eq hs0 hsd ψ M hm hu (fun j => (hL u hu hU j).1) x, hfx x]
  · exact ul1_mem_of_lt_top (lt_of_le_of_lt hnbd
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU))
  · exact (hcb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg))

/-! ### Continuity of `u ↦ ulNL u` on `C_b^m` -/

theorem ul1_cb_deriv_le {m : ℕ} {u : Euc d → ℝ} (hu : MemCb m u) {b : ℕ} (hb : b ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ b u x‖ ≤ cbNorm m u := by
  unfold cbNorm
  refine (le_ciSup (hu.2 b hb) x).trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j u z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem ul1_cb_nonneg {m : ℕ} {u : Euc d → ℝ} (hu : MemCb m u) : 0 ≤ cbNorm m u :=
  (norm_nonneg _).trans (ul1_cb_deriv_le hu (Nat.zero_le _) 0)

/-- `F_j ∈ L¹` with `‖F_j‖_{L¹} ≤ ‖w_j‖ ‖ρ‖_{L¹} ‖u‖_{C_b^1}` for `u ∈ C_b^m` -/
theorem ul1_L1_cb (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ} (hm : 1 ≤ m)
    {u : Euc d → ℝ} (hu : MemCb m u) (j : Fin d) :
    Integrable (fun y => ψ y * fderiv ℝ u y (ul1w M j)) ∧
      ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)| ≤ ‖ul1w M j‖ * cbNorm m u * ∫ y, |ψ y| := by
  have hb : ∀ y, |ψ y * fderiv ℝ u y (ul1w M j)| ≤ |ψ y| * (‖ul1w M j‖ * cbNorm m u) := by
    intro y
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : |fderiv ℝ u y (ul1w M j)| ≤ ‖fderiv ℝ u y‖ * ‖ul1w M j‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ u y).le_opNorm (ul1w M j)
    have e : ‖fderiv ℝ u y‖ = ‖iteratedFDeriv ℝ 1 u y‖ := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := y) (n := 0)
      simpa using this
    have h2 : ‖fderiv ℝ u y‖ ≤ cbNorm m u := by rw [e]; exact ul1_cb_deriv_le hu hm y
    calc |fderiv ℝ u y (ul1w M j)| ≤ ‖fderiv ℝ u y‖ * ‖ul1w M j‖ := h1
      _ ≤ cbNorm m u * ‖ul1w M j‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := by ring
  have hF : Continuous (fun y => ψ y * fderiv ℝ u y (ul1w M j)) :=
    (ul1_F_contDiff ψ M hm hu.1 j).continuous
  have hi : Integrable (fun y => |ψ y| * (‖ul1w M j‖ * cbNorm m u)) :=
    ψ.integrable.abs.mul_const _
  refine ⟨hi.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hb y), ?_⟩
  calc ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)| ≤ ∫ y, |ψ y| * (‖ul1w M j‖ * cbNorm m u) :=
        integral_mono (hi.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hb y)).abs hi hb
    _ = _ := by rw [integral_mul_const]; ring

/-- **UL-1 continuity.**  For `u ∈ C_b^m` (`3 ≤ m`) the nonlocal term is in `C_b^{m-2}` with
`‖ulNL u‖_{C_b^{m-2}} ≤ C ‖u‖_{C_b^m}`; the loss of two derivatives is the loss of the first-order
operator `div g * (ρ Mᵀ∇ ·)` (`m = 4` gives `C_b^2`).  Together with the linearity `ul_nl_sub` this is the
Lipschitz continuity of `u ↦ ulNL u` from `C_b^m` to `C_b^{m-2}`. -/
theorem ul_nl_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (m : ℕ) (hm : 3 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, MemCb m u →
      MemCb (m - 2) (ulNL s M ρ u) ∧ cbNorm (m - 2) (ulNL s M ρ u) ≤ C * cbNorm m u := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  obtain ⟨A, hA0, hA⟩ := ul1_env_G ψ M m
  choose Bj hBj using fun (j : Fin d) (n : ℕ) => ul1_K_deriv_bdd (d := d) hs0 j n
  set LH : ℝ := ∫ z, |ul1H d s z| with hLH
  set LΨ : ℝ := ∫ y, |ψ y| with hLΨ
  have hLH0 : 0 ≤ LH := integral_nonneg fun z => abs_nonneg _
  have hLΨ0 : 0 ≤ LΨ := integral_nonneg fun z => abs_nonneg _
  set Wn : ℕ → ℝ := fun n => ∑ j : Fin d, |Bj j n| * ‖ul1w M j‖ with hWn
  have hWn0 : ∀ n, 0 ≤ Wn n := fun n => Finset.sum_nonneg fun j _ => by positivity
  set T : ℕ → ℝ := fun n => LH * (A * Real.sqrt ((m : ℝ) + 1)) + Wn n * LΨ with hT
  have hT0 : ∀ n, 0 ≤ T n := fun n =>
    add_nonneg (mul_nonneg hLH0 (mul_nonneg hA0 (Real.sqrt_nonneg _))) (mul_nonneg (hWn0 n) hLΨ0)
  refine ⟨∑ n ∈ Finset.range (m - 2 + 1), T n, Finset.sum_nonneg fun n _ => hT0 n, fun u hu => ?_⟩
  set cb := cbNorm m u with hcb
  have hcb0 : 0 ≤ cb := ul1_cb_nonneg hu
  have hu1 : ContDiff ℝ m u := hu.1
  -- `G` is bounded with all derivatives
  have hGb : ∀ k ≤ m - 2, ∀ y, ‖iteratedFDeriv ℝ k (ul1G ψ M u) y‖ ≤ A * Real.sqrt ((m : ℝ) + 1) * cb := by
    intro k hk y
    refine (hA u hu1 k (by omega) y).trans ?_
    have hP : Real.sqrt (mriG m u y) ≤ Real.sqrt ((m : ℝ) + 1) * cb := by
      rw [show Real.sqrt ((m : ℝ) + 1) * cb = Real.sqrt (((m : ℝ) + 1) * cb ^ 2) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hcb0]]
      refine Real.sqrt_le_sqrt ?_
      unfold mriG
      calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i u y‖ ^ 2 ≤ ∑ _i ∈ Finset.range (m + 1), cb ^ 2 :=
            Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (norm_nonneg _)
              (ul1_cb_deriv_le hu (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) y) 2
        _ = _ := by simp
    have hwq : ul1wt d y * ul1q d y ≤ 1 := by
      have h1 : ul1wt d y ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (ul1_jb_ge_one y)
        (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; nlinarith)
      exact mul_le_one₀ h1 (ul1_q_nonneg y) (ul1_q_le_one y)
    calc A * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y)
        ≤ A * 1 * (Real.sqrt ((m : ℝ) + 1) * cb) := by
          gcongr
      _ = _ := by ring
  have hFi : ∀ j, Integrable (fun y => ψ y * fderiv ℝ u y (ul1w M j)) :=
    fun j => (ul1_L1_cb ψ M (by omega) hu j).1
  -- near part
  have hnear := ul1_conv_smooth (K := ul1G ψ M u) (N := m - 2) (ul1_G_contDiff ψ M (by omega) hu1)
    (Bn := fun _ => A * Real.sqrt ((m : ℝ) + 1) * cb) (fun n hn y => hGb n hn y)
    (ul1_H_integrable hs0 hsd) (by omega)
  -- far part
  have hfar : ∀ j : Fin d, ContDiff ℝ ((m - 2 : ℕ) : WithTop ℕ∞)
      (fun x => ∫ y, (ψ y * fderiv ℝ u y (ul1w M j)) * ul1K d s j (x - y)) ∧
      ∀ n ≤ m - 2, ∀ x, ‖iteratedFDeriv ℝ n
        (fun x => ∫ y, (ψ y * fderiv ℝ u y (ul1w M j)) * ul1K d s j (x - y)) x‖ ≤
        Bj j n * ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)| := fun j =>
    ul1_conv_smooth (K := ul1K d s j) (N := m - 2) ((ul1_K_contDiff s j).of_le (ul1_le_top _))
      (Bn := fun n => Bj j n) (fun n _ z => hBj j n z) (hFi j) (by omega)
  -- the decomposition as functions
  set nF : Euc d → ℝ := fun x => ∫ y, ul1H d s y * ul1G ψ M u (x - y) with hnF
  set fF : Fin d → Euc d → ℝ := fun j x => ∫ y, (ψ y * fderiv ℝ u y (ul1w M j)) * ul1K d s j (x - y)
    with hfF
  have hfun : ulNL s M ψ u = fun x => nF x + ∑ j, fF j x := by
    funext x
    rw [ul1_ulNL_eq hs0 hsd ψ M (by omega) hu1 hFi x]
    congr 1
    · have := integral_sub_left_eq_self (fun z => ul1H d s z * ul1G ψ M u (x - z)) volume x
      simp only [sub_sub_cancel] at this
      show ∫ y, ul1H d s (x - y) * ul1G ψ M u y = ∫ y, ul1H d s y * ul1G ψ M u (x - y)
      exact this
    · refine Finset.sum_congr rfl fun j _ => ?_
      have := integral_sub_left_eq_self (fun z => ul1K d s j z * (ψ (x - z) * fderiv ℝ u (x - z) (ul1w M j)))
        volume x
      simp only [sub_sub_cancel] at this
      rw [← this]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hsumF : (fun x => ∑ j, fF j x) = ∑ j : Fin d, fF j := by funext x; simp [Finset.sum_apply]
  have hfsum_cd : ContDiff ℝ ((m - 2 : ℕ) : WithTop ℕ∞) (∑ j : Fin d, fF j) := by
    rw [← hsumF]; exact ContDiff.sum fun j _ => (hfar j).1
  have hbound : ∀ n ≤ m - 2, ∀ x, ‖iteratedFDeriv ℝ n (ulNL s M ψ u) x‖ ≤ T n * cb := by
    intro n hn x
    rw [hfun, show (fun x => nF x + ∑ j, fF j x) = nF + ∑ j : Fin d, fF j from by
      funext x; simp [Finset.sum_apply], iteratedFDeriv_add_apply
      (hnear.1.of_le (by exact_mod_cast hn)).contDiffAt
      (hfsum_cd.of_le (by exact_mod_cast hn)).contDiffAt,
      iteratedFDeriv_sum_apply (fun j _ => ((hfar j).1.of_le (by exact_mod_cast hn)).contDiffAt)]
    refine (norm_add_le _ _).trans ?_
    have h1 := hnear.2 n hn x
    have h2 : ‖∑ j : Fin d, iteratedFDeriv ℝ n (fF j) x‖ ≤ Wn n * LΨ * cb := by
      refine (norm_sum_le _ _).trans ?_
      rw [hWn, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      refine ((hfar j).2 n hn x).trans ?_
      have hL1 := (ul1_L1_cb ψ M (by omega) hu j).2
      calc Bj j n * ∫ y, |ψ y * fderiv ℝ u y (ul1w M j)|
          ≤ |Bj j n| * (‖ul1w M j‖ * cb * LΨ) :=
            mul_le_mul (le_abs_self _) hL1 (integral_nonneg fun y => abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
    calc _ ≤ A * Real.sqrt ((m : ℝ) + 1) * cb * LH + Wn n * LΨ * cb := add_le_add h1 h2
      _ = T n * cb := by rw [hT]; ring
  refine ⟨⟨?_, fun n hn => ⟨T n * cb, ?_⟩⟩, ?_⟩
  · rw [hfun]
    exact hnear.1.add (ContDiff.sum fun j _ => (hfar j).1)
  · rintro _ ⟨x, rfl⟩
    exact hbound n hn x
  · unfold cbNorm
    calc ∑ n ∈ Finset.range (m - 2 + 1), ⨆ x, ‖iteratedFDeriv ℝ n (ulNL s M ψ u) x‖
        ≤ ∑ n ∈ Finset.range (m - 2 + 1), T n * cb := by
          refine Finset.sum_le_sum fun n hn => ?_
          exact ciSup_le fun x => hbound n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) x
      _ = _ := by rw [← Finset.sum_mul]

/-- Linearity of the nonlocal term on `C_b^m` (needed to turn `ul_nl_cont` into a Lipschitz estimate). -/
theorem ul_nl_sub {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) {m : ℕ} (hm : 2 ≤ m)
    {u v : Euc d → ℝ} (hu : MemCb m u) (hv : MemCb m v) (x : Euc d) :
    ulNL s M ρ (fun y => u y - v y) x = ulNL s M ρ u x - ulNL s M ρ v x := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by exact_mod_cast (by omega : 1 ≤ m))
  have hv1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast (by omega : 1 ≤ m))
  set Fu : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ u y (ul1w M j) with hFu
  set Fv : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ v y (ul1w M j) with hFv
  have hFuc : ∀ j, ContDiff ℝ 1 (Fu j) := fun j =>
    (ul1_F_contDiff ψ M (by omega) hu.1 j).of_le (by exact_mod_cast (by omega : 1 ≤ m - 1))
  have hFvc : ∀ j, ContDiff ℝ 1 (Fv j) := fun j =>
    (ul1_F_contDiff ψ M (by omega) hv.1 j).of_le (by exact_mod_cast (by omega : 1 ≤ m - 1))
  have hFui : ∀ j, Integrable (Fu j) := fun j => (ul1_L1_cb ψ M (by omega) hu j).1
  have hFvi : ∀ j, Integrable (Fv j) := fun j => (ul1_L1_cb ψ M (by omega) hv j).1
  have hFw : ∀ j, (fun y => ψ y * fderiv ℝ (fun y => u y - v y) y (ul1w M j)) = fun y => Fu j y - Fv j y := by
    intro j; funext y
    rw [fderiv_fun_sub (hu1.differentiable one_ne_zero y) (hv1.differentiable one_ne_zero y)]
    simp only [hFu, hFv, ContinuousLinearMap.sub_apply]; ring
  have key : ∀ j, (convGradConvW (rieszKernelGrad d s) (fun y => Fu j y - Fv j y) x) j =
      (convGradConvW (rieszKernelGrad d s) (Fu j) x) j - (convGradConvW (rieszKernelGrad d s) (Fv j) x) j := by
    intro j
    rw [ul1_conv_comp hs0 hsd j ((hFuc j).sub (hFvc j)) ((hFui j).sub (hFvi j)) x,
      ul1_conv_comp hs0 hsd j (hFuc j) (hFui j) x, ul1_conv_comp hs0 hsd j (hFvc j) (hFvi j) x,
      ← integral_sub (ul1_comp_integrable hs0 hsd j (hFuc j) (hFui j) x)
        (ul1_comp_integrable hs0 hsd j (hFvc j) (hFvi j) x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases h : ‖x - y‖ ≤ 1 / 4 <;> simp only [h, ↓reduceIte] <;> ring
  unfold ulNL
  simp only [ul1_matVec]
  simp_rw [hFw]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => key j

theorem ul1_memCb_sub {m : ℕ} {u v : Euc d → ℝ} (hu : MemCb m u) (hv : MemCb m v) :
    MemCb m (fun y => u y - v y) := by
  refine ⟨hu.1.sub hv.1, fun j hj => ?_⟩
  obtain ⟨Bu, hBu⟩ := hu.2 j hj
  obtain ⟨Bv, hBv⟩ := hv.2 j hj
  refine ⟨Bu + Bv, ?_⟩
  rintro _ ⟨x, rfl⟩
  have e : iteratedFDeriv ℝ j (fun y => u y - v y) x = iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j v x :=
    iteratedFDeriv_sub_apply (hu.1.of_le (by exact_mod_cast hj)).contDiffAt
      (hv.1.of_le (by exact_mod_cast hj)).contDiffAt
  beta_reduce
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hBu ⟨x, rfl⟩) (hBv ⟨x, rfl⟩))

/-- **UL-1 Lipschitz continuity** of `u ↦ ulNL u` from `C_b^m` to `C_b^{m-2}` (`m ≥ 3`; `m = 4`
gives `C_b^2`, the form needed for `cont_time_deriv`). -/
theorem ul_nl_lip {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (m : ℕ) (hm : 3 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Euc d → ℝ, MemCb m u → MemCb m v →
      MemCb (m - 2) (fun x => ulNL s M ρ u x - ulNL s M ρ v x) ∧
      cbNorm (m - 2) (fun x => ulNL s M ρ u x - ulNL s M ρ v x) ≤
        C * cbNorm m (fun y => u y - v y) := by
  obtain ⟨C, hC0, hC⟩ := ul_nl_cont hs0 hsd M ρ hρ m hm
  refine ⟨C, hC0, fun u v hu hv => ?_⟩
  have h := hC _ (ul1_memCb_sub hu hv)
  have e : (fun x => ulNL s M ρ u x - ulNL s M ρ v x) = ulNL s M ρ (fun y => u y - v y) := by
    funext x; exact (ul_nl_sub hs0 hsd M ρ hρ (by omega) hu hv x).symm
  rw [e]
  exact h

end HRS.MS.Ul
