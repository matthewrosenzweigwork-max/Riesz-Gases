import HRS.MS.R2WinOrbAux4
import HRS.MS.R2WinOrbAux3
import HRS.Whole.Window

/-!
# S10.3 (stationary half), part 5: orbit bounds from terminal-data bounds

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_orbit_of_data`: with `k = 4d+42`, `M = 8d+80`, a terminal datum `g` with
`‖∇g‖_{C_b^k} ≤ B`, `‖g‖_∞ ≤ B`, `‖√ρ_β Πg‖_{Σ^M} ≤ B` has the decaying gradient bound and the zeroth-order bound for every classical
adjoint solution of the stationary coefficient (`mov_global_adjoint_stationary_proof` and `s103_zeroth`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.MovAdj

variable {d : ℕ}

theorem s103_fderiv_contDiff {u : Euc d → ℝ} {n : ℕ} (hu : Differentiable ℝ u)
    (h : ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradient u x)) :
    ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u := by
  rw [show (((n + 1 : ℕ)) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
  refine ⟨hu, by simp, ?_⟩
  have e : fderiv ℝ u = fun x => (InnerProductSpace.toDual ℝ (Euc d)) (gradient u x) := by
    funext x; simp [gradient]
  rw [e]
  exact (InnerProductSpace.toDual ℝ (Euc d)).contDiff.comp h

theorem s103_orbit_of_data {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) :
    ∃ Cg cg Cz : ℝ, 0 ≤ Cg ∧ 0 < cg ∧ 0 ≤ Cz ∧ ∀ (g : Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) g →
      cbNormVecE (4 * d + 42) (fun x => gradient g x) ≤ ENNReal.ofReal B → (∀ x, |g x| ≤ B) →
      MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g) → oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g) ≤ B →
      ∀ t : ℝ, 0 ≤ t →
        R2OrbitGrad ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) (4 * d + 42) t g (2 * Cg * B) cg ∧
        R2OrbitSup ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) (4 * d + 42) t g
          ((1 + Cz) * B + 2 * Cg * B) := by
  have hM : (d : ℝ) / 2 + ((4 * d + 42 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hM0 : (d : ℝ) / 2 + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cg0, cg, hcg, hmov⟩ :=
    mov_global_adjoint_stationary_proof (d := d) (s := s) hd hs0 hsd β q hβ hq ρβ hρ (4 * d + 42) (8 * d + 80) hM
  obtain ⟨Cz, hCz0, hz⟩ := s103_zeroth hd hs0 hsd hq hβ hρ (8 * d + 80) hM0
  set Cg : ℝ := max Cg0 0 with hCgdef
  have hCg : 0 ≤ Cg := le_max_right _ _
  refine ⟨Cg, cg, Cz, hCg, hcg, hCz0, fun g B hB hgk hgrad hsup hosc hoscB t ht => ?_⟩
  have hgk' : ContDiff ℝ (((4 * d + 42 : ℕ) : WithTop ℕ∞) + 1) g := by exact_mod_cast hgk
  have hgrd : R2OrbitGrad ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) (4 * d + 42) t g
      (2 * Cg * B) cg := by
    intro f hf r hr
    obtain ⟨h1, h2⟩ := hmov t g f ht hf hgk' hosc r hr
    refine ⟨h1, h2.trans ?_⟩
    have hex : 0 ≤ Real.exp (-cg * (t - r)) := (Real.exp_pos _).le
    have a1 : ENNReal.ofReal (Cg0 * Real.exp (-cg * (t - r))) ≤ ENNReal.ofReal (Cg * Real.exp (-cg * (t - r))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hex)
    have a2 : cbNormVecE (4 * d + 42) (fun x => gradient g x) +
        ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x) * (g x - ∫ y, g y * ρβ y))) ≤
        ENNReal.ofReal (2 * B) := by
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hgrad (ENNReal.ofReal_le_ofReal hoscB)
        _ = ENNReal.ofReal (2 * B) := by
          rw [← ENNReal.ofReal_add hB hB]; congr 1; ring
    calc ENNReal.ofReal (Cg0 * Real.exp (-cg * (t - r))) * (cbNormVecE (4 * d + 42) (fun x => gradient g x) +
          ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (fun x => Real.sqrt (ρβ x) * (g x - ∫ y, g y * ρβ y))))
        ≤ ENNReal.ofReal (Cg * Real.exp (-cg * (t - r))) * ENNReal.ofReal (2 * B) := mul_le_mul' a1 a2
      _ = ENNReal.ofReal (2 * Cg * B * Real.exp (-cg * (t - r))) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hCg hex)]; congr 1; ring
  refine ⟨hgrd, ?_⟩
  intro f hf r hr
  obtain ⟨hgr1, hgr2⟩ := hgrd f hf r hr
  have hdiff : Differentiable ℝ (f r) := ((hf.c2 r hr).differentiable (by norm_num))
  have hfr : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) (f r) := s103_fderiv_contDiff hdiff hgr1
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
  -- the `C_b^k` norm splits into the zeroth term and the gradient terms
  have hz0 : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 0 (f r) x‖) ≤ ENNReal.ofReal ((1 + Cz) * B) := by
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have := hz t g f B ht hf hosc hsup r hr x
    have h2 : Cz * oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ g) ≤ Cz * B := mul_le_mul_of_nonneg_left hoscB hCz0
    linarith
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
  calc _ ≤ cbNormVecE (4 * d + 42) (fun x => gradient (f r) x) + ENNReal.ofReal ((1 + Cz) * B) :=
        add_le_add hsub hz0
    _ ≤ ENNReal.ofReal (2 * Cg * B) + ENNReal.ofReal ((1 + Cz) * B) := by gcongr
    _ = ENNReal.ofReal ((1 + Cz) * B + 2 * Cg * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end HRS.MS.R2WinOrb

end
