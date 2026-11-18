import HRS.Main.ThermLin2Dy4

/-!
# THERMLIN 2, packet `Dy`, part 5: `tl2_dyson_pairing` (plan statement B1)

The coefficient identity `thermlin_dyson_coeff` (ThermLinAux9), with interval integrability of the Duhamel integrand
(`tl2dy_dyson_int`), is turned into real Fourier coefficients (`GF.gfevRc`), and then paired with `z ∈ E_m` by
`tl2dy_eval_duhamel_ioc` (a variant of `GF.gfev_eval_duhamel_abs`).  Uses no plan statement.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
/-- `U^{t,t}φ = φ` for the moving propagator and smooth `φ`. -/
theorem tl2dy_prop_self (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {t : ℝ} (ht : 0 ≤ t) : propagator S.dyn S.ρ t t φ = φ := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    have hK := PDE.ClassicalAux.convKernelFacts hd1 S.dyn
    have hV1 : Torus.IsCk 1 S.dyn.V := PDE.MFSemigroup.isCk_nat_of_isSmooth S.hV 1
    have hρ0 : Torus.IsCk 1 (S.ρ 0) := by
      rw [S.hρ_init]; exact PDE.MFSemigroup.isCk_nat_of_isSmooth S.hρ0.smooth 1
    exact PDE.MFSemigroup.propagator_zero S.dyn hK hV1 S.ρ hρ0 (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 2)
  · obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = PDE.mStar d + d + 6 := ⟨_, rfl⟩
    have hj : (d : ℝ) / 2 + 4 < (j : ℝ) := by
      have : d + 6 ≤ j := by omega
      have h2 : ((d + 6 : ℕ) : ℝ) ≤ j := by exact_mod_cast this
      push_cast at h2
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have hjms : PDE.mStar d ≤ j := by omega
    obtain ⟨R, Λ, hAtAll⟩ := tl2dy_moving S h j hj
    obtain ⟨C, Cs, -, -, hmain⟩ :=
      PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd j hjms R 1 Λ (Torus.cbNorm (j + 3) S.V)
    have hφc : Continuous φ := PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 1)
    have hφS : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
    obtain ⟨hcls, hpe, -, -⟩ := hmain S.dyn S.β⁻¹ t S.ρ (hAtAll t htp) t ⟨htp, le_rfl⟩ φ hφc hφS
    rw [hpe t ⟨htp.le, le_rfl⟩]
    exact hcls.terminal

open HRS.PDE HRS.PDE.MFAdjoint in
/-- (B1) the V-outer Dyson identity paired with `z ∈ E_m`, for smooth tests. -/
theorem tl2_dyson_pairing_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (z : NegSobolev d m) :
    NegSobolev.eval z (propagator S.dyn S.ρ u t φ) =
      NegSobolev.eval z (tl2Ub S ρβ u t φ) +
        ∫ r in u..t, NegSobolev.eval z
          (tl2Ub S ρβ u r (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  rcases hut.eq_or_lt with heq | hlt
  · subst heq
    simp only [intervalIntegral.integral_same, add_zero]
    rw [tl2dy_prop_self S h hφ hu]
    have e1 := Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h.1 hsm hpos φ hφ u hu
    show _ = NegSobolev.eval z (propagator (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) (fun _ => ρβ) u u φ)
    rw [e1]
  have ht : 0 < t := lt_of_le_of_lt hu hlt
  have hτ0 : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  obtain ⟨j', hj'def⟩ : ∃ j' : ℕ, j' = ⌈m⌉₊ + PDE.mStar d + d + 4 := ⟨_, rfl⟩
  have hj'ms : PDE.mStar d ≤ j' := by omega
  have hjd : (d : ℝ) / 2 + 2 < (j' : ℝ) := by
    have : d + 4 ≤ j' := by omega
    have h2 : ((d + 4 : ℕ) : ℝ) ≤ j' := by exact_mod_cast this
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmj : m ≤ (j' : ℝ) := by
    refine (Nat.le_ceil m).trans ?_
    exact_mod_cast (by omega : ⌈m⌉₊ ≤ j')
  obtain ⟨Bm, hBm, hfacts⟩ := tl2dy_moving_facts S h j' hj'ms hjd hφ ht
  obtain ⟨L, hL, hfr⟩ := tl2dy_frozen_facts S h j' hj'ms
  set j : ℕ := j' + 2 with hjdef
  have hj : (d : ℝ) / 2 + 4 < (j : ℝ) := by rw [hjdef]; push_cast; linarith
  have hjj : j - 2 = j' := by omega
  have hφc : Continuous φ := PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 1)
  have hφSj : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  have hφSj' : MemSobolev (j' : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  have hcm : MemHs (j : ℝ) (coeffOf φ) := (hsNormSq_coeffOf _ φ hφSj).1
  have hdys := HRS.ThermLin.thermlin_dyson_coeff S h j hj (coeffOf φ) hcm t ht (t - u) hτ0
  have hint := tl2dy_dyson_int S h j hj (coeffOf φ) hcm ht hτ0
  rw [hjj] at hdys hint
  -- the data
  set A := propagator S.dyn S.ρ u t φ with hA
  set B := tl2Ub S ρβ u t φ with hB
  set g : ℝ → Torus d → ℝ := fun r => tl2Ub S ρβ u r (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) with hg
  have huI : u ∈ Set.Icc (0 : ℝ) t := ⟨hu, hlt.le⟩
  obtain ⟨hA1, -, hA3, -⟩ := hfacts u huI
  have hBf := hfr hφc hφSj' hu hlt
  -- facts on `g r`, `r ∈ (u, t]`
  have hgr : ∀ r ∈ Set.Ioc u t,
      MemSobolev (j' : ℝ) (g r) ∧ sobolevNorm (j' : ℝ) (g r) ≤ Real.exp (L * t) * Bm ∧
      ∀ k : NonzeroLattice d, Torus.funRealCoeff (g r) k = GF.gfevRc k (frozenCoeff S.dyn ρβ j'
        (forwardGen S.dyn (S.ρ (t - (t - r))) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) -
          forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)))
        ((t - u) - (t - r)) k.1) := by
    intro r hr
    have hrI : r ∈ Set.Icc (0 : ℝ) t := ⟨hu.trans hr.1.le, hr.2⟩
    obtain ⟨-, -, -, hcont, he2, hΔS, hΔn⟩ := hfacts r hrI
    obtain ⟨hcoef, hMS, hnorm⟩ := hfr hcont hΔS hu hr.1
    have hgr_eq : g r = tl2Ub S ρβ u r (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := rfl
    refine ⟨hMS, ?_, ?_⟩
    · refine hnorm.trans ?_
      have hexp : Real.exp (L * (r - u)) ≤ Real.exp (L * t) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hL)
      exact mul_le_mul hexp hΔn (Real.sqrt_nonneg _) (Real.exp_pos _).le
    · intro k
      have hint_g : Integrable (g r) := (hMS.1).integrable one_le_two
      rw [GF.gfev_funRealCoeff_eq_rc _ hint_g, hgr_eq, hcoef, he2]
      have e3 : t - (t - r) = r := by ring
      have e4 : (t - u) - (t - r) = r - u := by ring
      rw [e3, e4]
  have hjj' : (j' : ℝ) ≤ (j : ℝ) := by rw [hjdef]; push_cast; linarith
  have hAS : MemSobolev m A := tl2dy_memSob_mono (hmj.trans hjj') hA3
  have hBS : MemSobolev m B := tl2dy_memSob_mono hmj hBf.2.1
  set Bd : ℝ := Real.exp (L * t) * Bm with hBd
  have hgS : ∀ s ∈ Set.Ioc u t, MemSobolev m (g s) ∧ sobolevNorm m (g s) ≤ Bd := fun s hs =>
    ⟨tl2dy_memSob_mono hmj (hgr s hs).1,
      (tl2dy_sobNorm_mono hmj (hgr s hs).1).trans (hgr s hs).2.1⟩
  -- the integrand in the coefficient identity, as a function of `σ = t - r`
  set P : ℝ → Coeff d := propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) with hP
  set F : NonzeroLattice d → ℝ → ℝ := fun k σ => GF.gfevRc k (frozenCoeff S.dyn ρβ j'
    (forwardGen S.dyn (S.ρ (t - σ)) (P σ) - forwardGen S.dyn ρβ (P σ)) ((t - u) - σ) k.1) with hF
  have hrc : ∀ k : NonzeroLattice d,
      ∫ r in u..t, Torus.funRealCoeff (g r) k = ∫ σ in (0 : ℝ)..(t - u), F k σ := by
    intro k
    have h1 : ∫ r in u..t, Torus.funRealCoeff (g r) k = ∫ r in u..t, F k (t - r) := by
      rw [intervalIntegral.integral_of_le hlt.le, intervalIntegral.integral_of_le hlt.le]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun r hr => (hgr r hr).2.2 k)
    rw [h1, intervalIntegral.integral_comp_sub_left (F k) t, sub_self]
  have hint' : ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r => Torus.funRealCoeff (g r) k) volume u t := by
    intro k
    have h0 : IntervalIntegrable (fun σ => F k σ) volume 0 (t - u) := by
      have := hint k.1
      rw [intervalIntegrable_iff] at this ⊢
      exact (GF.gfevRc k).integrable_comp this
    have h1 : IntervalIntegrable (fun r => F k (t - r)) volume u t := by
      have := h0.comp_sub_left t
      simpa using this.symm
    refine h1.congr fun r hr => ?_
    rw [Set.uIoc_of_le hlt.le] at hr
    exact ((hgr r hr).2.2 k).symm
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff A k - Torus.funRealCoeff B k =
      ∫ r in u..t, Torus.funRealCoeff (g r) k := by
    intro k
    have eA := GF.gfev_funRealCoeff_eq_rc A (hA3.1.integrable one_le_two) k
    have eB := GF.gfev_funRealCoeff_eq_rc B (hBf.2.1.1.integrable one_le_two) k
    rw [eA, eB, hA1, hBf.1, hrc k, hdys k.1, map_add]
    have := (GF.gfevRc k).intervalIntegral_comp_comm (hint k.1)
    rw [← this]
    ring
  set f : ℝ → Torus d → ℝ := fun s => if s = u then A else B with hf
  have hfu : f u = A := if_pos rfl
  have hft : f t = B := if_neg hlt.ne'
  have key := HRS.GF.tl2dy_eval_duhamel_ioc (m := m) (f := f) (g := g) (u := u) (u' := t) (B := Bd) hlt.le
    (by rw [hfu]; exact hAS) (by rw [hft]; exact hBS) hgS hint'
    (fun k => by rw [hfu, hft]; exact hcoef k) z
  rw [hfu, hft] at key
  linarith

example := (@tl2_dyson_pairing_proof : type_of% @tl2_dyson_pairing)

end HRS.ThermLin.Plan2
