import HRS.MS.R2WinOrbNLAux2

/-!
# S10.3 (nonlinear branch), part 3: orbit bounds from terminal-data bounds, and the first two orbit claims

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_orbit_of_data`: for a trajectory `ρ` with the gradient estimate (`S103nGrad`) and the
zeroth-order bound (`S103nZero`), a terminal datum `g` with `‖∇g‖_{C_b^k}, ‖g‖_∞, ‖√ρ_β Πg‖_{Σ^M} ≤ B` has the decaying gradient bound and the
zeroth-order bound for every classical adjoint solution.  `s103n_claims12`: the first two orbit claims (terminal datum `φ_α`) with a constant
independent of the trajectory and of `α, t`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc

variable {d : ℕ}

/-- The zeroth-order bound along a fixed trajectory `ρ` (conclusion of `s103n_zeroth`). -/
def S103nZero (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (Cz : ℝ) : Prop :=
  ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Bφ : ℝ), 0 ≤ T →
    IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
    ContDiff ℝ ((4 * d + 42 : ℕ) + 1) φ → MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ) →
    cbNormVecE (4 * d + 42) (fun x => gradient φ x) < ⊤ → (∀ x, |φ x| ≤ Bφ) →
    ∀ r' ∈ Icc (0 : ℝ) T, ∀ x, |f r' x| ≤ Bφ + Cz *
      ((cbNormVecE (4 * d + 42) (fun x => gradient φ x)).toReal +
        oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ))

theorem s103n_orbit_of_data {s a β : ℝ} {ρβ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} {Cg cg Cz : ℝ}
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hCz : 0 ≤ Cz) (hG : S103nGrad d s a β ρβ ρ Cg cg) (hZ : S103nZero d s a β ρβ ρ Cz)
    (g : Euc d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hgk : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) g)
    (hgrad : cbNormVecE (4 * d + 42) (fun x => gradient g x) ≤ ENNReal.ofReal B) (hsup : ∀ x, |g x| ≤ B)
    (hosc : MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g))
    (hoscB : oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g) ≤ B) (t : ℝ) (ht : 0 ≤ t) :
    R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (2 * Cg * B) cg ∧
    R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g
      ((1 + 2 * Cz) * B + 2 * Cg * B) := by
  have hgk' : ContDiff ℝ (((4 * d + 42 : ℕ) : WithTop ℕ∞) + 1) g := by exact_mod_cast hgk
  have hgrd : R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (2 * Cg * B) cg := by
    intro f hf r hr
    obtain ⟨h1, h2⟩ := hG t g f ht hf hgk' hosc r hr
    refine ⟨h1, h2.trans ?_⟩
    have a2 : cbNormVecE (4 * d + 42) (fun x => gradient g x) +
        ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g)) ≤ ENNReal.ofReal (2 * B) := by
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hgrad (ENNReal.ofReal_le_ofReal hoscB)
        _ = ENNReal.ofReal (2 * B) := by
          rw [← ENNReal.ofReal_add hB hB]; congr 1; ring
    calc ENNReal.ofReal (Cg * Real.exp (-cg * (t - r))) * (cbNormVecE (4 * d + 42) (fun x => gradient g x) +
          ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g)))
        ≤ ENNReal.ofReal (Cg * Real.exp (-cg * (t - r))) * ENNReal.ofReal (2 * B) := by gcongr
      _ = ENNReal.ofReal (2 * Cg * B * Real.exp (-cg * (t - r))) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hCg (Real.exp_pos _).le)]; congr 1; ring
  refine ⟨hgrd, ?_⟩
  intro f hf r hr
  obtain ⟨hgr1, hgr2⟩ := hgrd f hf r hr
  have hdiff : Differentiable ℝ (f r) := ((hf.c2 r hr).differentiable (by norm_num))
  have hfr : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) (f r) :=
    HRS.MS.R2WinOrb.s103_fderiv_contDiff hdiff hgr1
  have hexle : Real.exp (-cg * (t - r)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ t - r := sub_nonneg.2 hr.2
    nlinarith
  have hgr3 : cbNormVecE (4 * d + 42) (fun x => gradient (f r) x) ≤ ENNReal.ofReal (2 * Cg * B) :=
    hgr2.trans (ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ 2 * Cg * B := by positivity
      calc 2 * Cg * B * Real.exp (-cg * (t - r)) ≤ 2 * Cg * B * 1 :=
            mul_le_mul_of_nonneg_left hexle this
        _ = _ := mul_one _))
  refine ⟨hfr.of_le (by exact_mod_cast Nat.le_succ _), ?_⟩
  have hfin : cbNormVecE (4 * d + 42) (fun x => gradient g x) < ⊤ :=
    lt_of_le_of_lt hgrad ENNReal.ofReal_lt_top
  have hGB : (cbNormVecE (4 * d + 42) (fun x => gradient g x)).toReal ≤ B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgrad
    rwa [ENNReal.toReal_ofReal hB] at this
  have hz0 : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 0 (f r) x‖) ≤
      ENNReal.ofReal ((1 + 2 * Cz) * B) := by
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h1 := hZ t g f B ht hf hgk' hosc hfin hsup r hr x
    have h2 : Cz * ((cbNormVecE (4 * d + 42) (fun x => gradient g x)).toReal +
        oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g)) ≤ Cz * (B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add hGB hoscB) hCz
    nlinarith
  have hterm : ∀ i ∈ Finset.range (4 * d + 42), (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ (i + 1) (f r) x‖) =
      ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => gradient (f r) y) x‖ := by
    intro i hi
    have hi' : i + 1 ≤ 4 * d + 42 + 1 := by have := Finset.mem_range.1 hi; omega
    refine iSup_congr fun x => ?_
    rw [(s67_norm_iter_grad (hfr.of_le (by exact_mod_cast hi')) x).symm]
  unfold r2CbNormE
  rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm]
  have hsub : ∑ i ∈ Finset.range (4 * d + 42), (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => gradient (f r) y) x‖) ≤
      cbNormVecE (4 * d + 42) (fun x => gradient (f r) x) := by
    unfold cbNormVecE
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ _))
  calc _ ≤ cbNormVecE (4 * d + 42) (fun x => gradient (f r) x) + ENNReal.ofReal ((1 + 2 * Cz) * B) :=
        add_le_add hsub hz0
    _ ≤ ENNReal.ofReal (2 * Cg * B) + ENNReal.ofReal ((1 + 2 * Cz) * B) := by gcongr
    _ = ENNReal.ofReal ((1 + 2 * Cz) * B + 2 * Cg * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The first two orbit claims (terminal datum `φ_α`) along every trajectory with the gradient and zeroth-order bounds. -/
theorem s103n_claims12 {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) {Cg cg Cz : ℝ} (hCg : 0 ≤ Cg) (hcg : 0 < cg)
    (hCz : 0 ≤ Cz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ → Euc d → ℝ, S103nGrad d s a β ρβ ρ Cg cg → S103nZero d s a β ρβ ρ Cz →
      ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t →
        R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * HRS.MS.R2WinOrb.s103_b d α) ∧
        R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
          (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * HRS.MS.R2WinOrb.s103_b d α) cg := by
  obtain ⟨K, hK0, hK⟩ := HRS.MS.R2WinOrb.s103_data hd hs0 hsd ha hβ hρ
  refine ⟨max (2 * Cg * K) ((1 + 2 * Cz) * K + 2 * Cg * K), by positivity, fun ρ hG hZ α t ht => ?_⟩
  have hb0 := HRS.MS.R2WinOrb.s103_b_nonneg (d := d) α
  have hB0 : 0 ≤ K * HRS.MS.R2WinOrb.s103_b d α := mul_nonneg hK0 hb0
  obtain ⟨h1, h2, h3, h4, h5⟩ := hK 0 (by norm_num) α
  simp only [Function.iterate_zero, id_eq] at h1 h2 h3 h4 h5
  obtain ⟨g1, s1⟩ := s103n_orbit_of_data hCg hcg hCz hG hZ _ _ hB0
    (h1.of_le (HRS.MS.R2WinOrb.s103_cast_le_infty _)) h2 h3 h4 h5 t ht
  have hm1 : 2 * Cg * (K * HRS.MS.R2WinOrb.s103_b d α) ≤
      max (2 * Cg * K) ((1 + 2 * Cz) * K + 2 * Cg * K) * HRS.MS.R2WinOrb.s103_b d α := by
    calc 2 * Cg * (K * HRS.MS.R2WinOrb.s103_b d α) = (2 * Cg * K) * HRS.MS.R2WinOrb.s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  have hm2 : (1 + 2 * Cz) * (K * HRS.MS.R2WinOrb.s103_b d α) + 2 * Cg * (K * HRS.MS.R2WinOrb.s103_b d α) ≤
      max (2 * Cg * K) ((1 + 2 * Cz) * K + 2 * Cg * K) * HRS.MS.R2WinOrb.s103_b d α := by
    calc (1 + 2 * Cz) * (K * HRS.MS.R2WinOrb.s103_b d α) + 2 * Cg * (K * HRS.MS.R2WinOrb.s103_b d α) =
        ((1 + 2 * Cz) * K + 2 * Cg * K) * HRS.MS.R2WinOrb.s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
  exact ⟨HRS.MS.R2WinOrb.s103_orbitSup_mono s1 hm2, HRS.MS.R2WinOrb.s103_orbitGrad_mono g1 hm1⟩

end HRS.MS.R2WinOrbNL

end
