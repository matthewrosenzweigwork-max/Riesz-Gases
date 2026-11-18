import HRS.MS.S104eC1C
import HRS.MS.S104eC1D

/-!
# S104E route C, packet C1 (part E): the sup-norm gain `D^{j+1} P_τ f` for `f ∈ C^j_b`, by induction on `j`

`s104c1_gain_core`: `K, s₀` independent of `j`: for `f ∈ Bd j M`, `0 < τ ≤ T`: `P_τ f ∈ C^{j+1}`,
`‖D^{j+1} P_τ f‖ ≤ K M τ^{-1/2}` and `D^{j+1} P_τ f` is Lipschitz with constant `K M τ^{-1}` at scale `s₀ τ^{1/2}`.
Induction step: `∂_v P_τ f = e^{-aτ} P_τ (∂_v f)` and `s104c1_dstep`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.Wad HRS.MS.R2WinOrbNL
variable {d : ℕ}

theorem s104c1_it1_sub (u : Euc d → ℝ) (x x' : Euc d) :
    ‖iteratedFDeriv ℝ 1 u x' - iteratedFDeriv ℝ 1 u x‖ ≤ ‖fderiv ℝ u x' - fderiv ℝ u x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
  rw [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
    ← ContinuousLinearMap.sub_apply, Fin.prod_univ_one]
  exact (fderiv ℝ u x' - fderiv ℝ u x).le_opNorm _

/-- directional derivatives of a `C^{j+1}_b` function are `C^j_b` -/
theorem s104c1_Bd_dir {j : ℕ} {M : ℝ} {f : Euc d → ℝ} (hf : Bd (j + 1) M f) (v : Euc d) :
    Bd j (M * ‖v‖) (fun z => fderiv ℝ f z v) := by
  have hd : ContDiff ℝ (j : WithTop ℕ∞) (fun z => fderiv ℝ f z) :=
    hf.1.fderiv_right (by norm_cast)
  refine ⟨hd.clm_apply contDiff_const, fun i hi x => ?_⟩
  have e : (fun z => fderiv ℝ f z v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fun z => fderiv ℝ f z) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left _ hd.contDiffAt (by exact_mod_cast hi)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun φ => by
      simpa [mul_comm] using φ.le_opNorm v
  have h2 : ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ f z) x‖ ≤ M := by
    rw [norm_iteratedFDeriv_fderiv]; exact hf.2 (i + 1) (by omega) x
  calc _ ≤ ‖v‖ * M := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    _ = M * ‖v‖ := mul_comm _ _

/-- the derivative of `P_τ f` -/
theorem s104c1_hasD {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) {M : ℝ} {f : Euc d → ℝ}
    (hf : Bd 1 M f) (y : Euc d) :
    HasFDerivAt (s83_P a ν τ f) (s83_mc a τ • s83_P a ν τ (fderiv ℝ f) y) y := by
  have hf1 : ContDiff ℝ 1 f := by exact_mod_cast hf.1
  have hw : Wt 0 M f := fun x => by
    simpa using hf.2 0 (Nat.zero_le _) x
  have hw' : Wt 0 M (fderiv ℝ f) := fun x => by
    simpa using hf.2 1 le_rfl x
  exact s83_G_hasFDerivAt hf1 (le_refl (0 : ℝ)) hw hw' (s83_abs_mc_le_one ha.le hτ.le)
    (s83_abs_ms_le ha hν.le hτ.le) y

theorem s104c1_hact {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) {M : ℝ} {f : Euc d → ℝ}
    (hf : Bd 1 M f) (y v : Euc d) :
    fderiv ℝ (s83_P a ν τ f) y v = s83_mc a τ * s83_P a ν τ (fun z => fderiv ℝ f z v) y := by
  have hf1 : ContDiff ℝ 1 f := by exact_mod_cast hf.1
  have hw' : Wt 0 M (fderiv ℝ f) := fun x => by
    simpa using hf.2 1 le_rfl x
  have hf'c : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  rw [(s104c1_hasD ha hν hτ hf y).fderiv]
  have hint := s83_int_shift hf'c (le_refl (0 : ℝ)) hw' (c := s83_mc a τ) (s83_abs_ms_le ha hν.le hτ.le) y
  have := s84_G_clm_apply hint v
  rw [smul_apply, show s83_P a ν τ (fderiv ℝ f) y = s83_G (s83_mc a τ) (s83_ms a ν τ) (fderiv ℝ f) y from rfl,
    this, smul_eq_mul]
  rfl

theorem s104c1_gain_core (a ν T : ℝ) (ha : 0 < a) (hν : 0 < ν) :
    ∃ K s0 : ℝ, 0 ≤ K ∧ 0 < s0 ∧ ∀ (j : ℕ) {M : ℝ} {f : Euc d → ℝ}, Bd j M f →
      ∀ {τ : ℝ}, 0 < τ → τ ≤ T →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s83_P a ν τ f) ∧
      (∀ x, ‖iteratedFDeriv ℝ (j + 1) (s83_P a ν τ f) x‖ ≤ K * M * (Real.sqrt τ)⁻¹) ∧
      ∀ x x' : Euc d, ‖x' - x‖ ≤ s0 * Real.sqrt τ →
        ‖iteratedFDeriv ℝ (j + 1) (s83_P a ν τ f) x' - iteratedFDeriv ℝ (j + 1) (s83_P a ν τ f) x‖ ≤
          K * M * τ⁻¹ * ‖x' - x‖ := by
  obtain ⟨K, s0, hK, hs0, hbase⟩ := s104c1_base (d := d) a ν T ha hν
  refine ⟨K, s0, hK, hs0, fun j => ?_⟩
  induction j with
  | zero =>
    intro M f hf τ hτ hτT
    have hfc : Continuous f := by simpa using hf.1
    have hfb : ∀ y, ‖f y‖ ≤ M := fun y => by simpa using hf.2 0 le_rfl y
    obtain ⟨h1, h2, h3⟩ := hbase hfc hfb hτ hτT
    refine ⟨by exact_mod_cast h1, fun x => ?_, fun x x' hxx => ?_⟩
    · simpa using h2 x
    · exact (s104c1_it1_sub _ x x').trans (h3 x x' hxx)
  | succ j ih =>
    intro M f hf τ hτ hτT
    have hf1 : Bd 1 M f := hf.mono_N (by omega)
    have hM : 0 ≤ M := hf.nonneg
    have hdiff : Differentiable ℝ (s83_P a ν τ f) := fun y => (s104c1_hasD ha hν hτ hf1 y).differentiableAt
    have hmc1 : |s83_mc a τ| ≤ 1 := s83_abs_mc_le_one ha.le hτ.le
    have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    have hfun : ∀ v : Euc d, (fun y => fderiv ℝ (s83_P a ν τ f) y v) =
        fun y => s83_mc a τ • s83_P a ν τ (fun z => fderiv ℝ f z v) y := fun v => by
      funext y; rw [s104c1_hact ha hν hτ hf1 y v]; rfl
    have key : ∀ v : Euc d, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
        (fun y => fderiv ℝ (s83_P a ν τ f) y v) ∧
        (∀ x, ‖iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ (s83_P a ν τ f) y v) x‖ ≤
          K * M * (Real.sqrt τ)⁻¹ * ‖v‖) ∧
        (∀ x x', ‖x' - x‖ ≤ s0 * Real.sqrt τ →
          ‖iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ (s83_P a ν τ f) y v) x' -
            iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ (s83_P a ν τ f) y v) x‖ ≤
            K * M * τ⁻¹ * ‖x' - x‖ * ‖v‖) := by
      intro v
      obtain ⟨hv1, hv2, hv3⟩ := ih (s104c1_Bd_dir hf v) hτ hτT
      rw [hfun v]
      refine ⟨hv1.const_smul _, fun x => ?_, fun x x' hxx => ?_⟩
      · rw [iteratedFDeriv_const_smul_apply' hv1.contDiffAt, norm_smul, Real.norm_eq_abs]
        calc |s83_mc a τ| * ‖iteratedFDeriv ℝ (j + 1) (s83_P a ν τ fun z => fderiv ℝ f z v) x‖
            ≤ 1 * (K * (M * ‖v‖) * (Real.sqrt τ)⁻¹) :=
              mul_le_mul hmc1 (hv2 x) (norm_nonneg _) zero_le_one
          _ = _ := by ring
      · rw [iteratedFDeriv_const_smul_apply' hv1.contDiffAt, iteratedFDeriv_const_smul_apply' hv1.contDiffAt,
          ← smul_sub, norm_smul, Real.norm_eq_abs]
        calc |s83_mc a τ| * ‖iteratedFDeriv ℝ (j + 1) (s83_P a ν τ fun z => fderiv ℝ f z v) x' -
              iteratedFDeriv ℝ (j + 1) (s83_P a ν τ fun z => fderiv ℝ f z v) x‖
            ≤ 1 * (K * (M * ‖v‖) * τ⁻¹ * ‖x' - x‖) :=
              mul_le_mul hmc1 (hv3 x x' hxx) (norm_nonneg _) zero_le_one
          _ = _ := by ring
    obtain ⟨hC, hb1, hb2⟩ := s104c1_dstep (u := s83_P a ν τ f) (j := j) (K1 := K * M * (Real.sqrt τ)⁻¹)
      (K2 := K * M * τ⁻¹) (r := s0 * Real.sqrt τ) (by positivity) (by positivity) hdiff
      (fun v => (key v).1) (fun v x => (key v).2.1 x) (fun v x x' hxx => (key v).2.2 x x' hxx)
    exact ⟨hC, hb1, hb2⟩

end HRS.MS.S104e.C
