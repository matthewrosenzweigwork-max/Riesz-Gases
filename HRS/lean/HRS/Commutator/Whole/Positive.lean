import HRS.Commutator.Whole.PositiveAux9

/-!
# Sub-Coulomb commutator on `ℝ^d`: the positive truncation (Section 2.1 of the note)

Source `[N]` = `source/external/subcoulomb_commutator_20261013T142216Z/*.tex`, Section 2.1
(L243-322), Lemma 2.1 `lem:positive` (L266-284) and its proof (L286-322).  Packet `CMX-POS`.

Standing assumptions of the note (L76): `d ≥ 3`, `0 ≤ s < d-2`.  All statements are for the data
`phi`, `fTrunc s 1 = f_1`, `g1 s = g_1`, `g1Hat`, `f1Hat` of `Defs.lean`.  Lemma 2.1 is split into
the independently provable assertions below (`posDef_f1`, `posDef_g1`, `quadForm_f1` restricted to densities after the audit) (each cites its TeX lines).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- `[N] (2.gaussian-mixture)` (L289): `φ` is a positive mixture of Gaussians,
`φ(x) = Γ(d+2)⁻¹ ∫_0^∞ t^{d+1} e^{-t} e^{-t|x|²} dt`. -/
theorem phi_gaussian_mixture (x : Euc d) :
    phi x = (Real.Gamma ((d : ℝ) + 2))⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) + 1) * Real.exp (-t) * Real.exp (-t * ‖x‖ ^ 2) := by
  exact phi_mixture_aux x

/-- `[N] L290-291`: `φ̂` is real and strictly positive (a positive mixture of Gaussians has a
strictly positive Fourier transform; `φ ∈ L¹` so `φ̂` is continuous). -/
theorem phiHat_pos (ξ : Euc d) :
    0 < (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) ξ).re ∧
      (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) ξ).im = 0 := by
  rw [fourier_phi]
  exact ⟨by simpa using phiHatR_pos (d := d) ‖ξ‖, by simp⟩

/-- `[N] (2.positive-spatial)`, `(2.log-f)` (L295, L301): the spatial formula
`f_1(x) = c_φ |x|^{-s} ∫_{|x|}^∞ r^{s-1} φ(r) dr` (`s > 0`), `f_1(x) = ∫_{|x|}^∞ φ(r) dr/r`
(`s = 0`), `x ≠ 0` (change of variables `r = |x|/t`). -/
theorem fTrunc_spatial (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (x : Euc d)
    (hx : x ≠ 0) :
    fTrunc s 1 x =
      if s = 0 then ∫ r in Set.Ioi ‖x‖, phiR d r / r
      else cPhi d s * ‖x‖ ^ (-s) * ∫ r in Set.Ioi ‖x‖, r ^ (s - 1) * phiR d r := by
  exact fTrunc_spatial_aux x hx

/-- `[N] L266` (first sentence): `f_1` is positive away from the origin.  (The hypothesis `s < d-2`
is needed: for `s ≥ 2d+4` the integral defining `c_φ` diverges and `cPhi = 0` is a junk value.) -/
theorem fTrunc_pos (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (x : Euc d) (hx : x ≠ 0) :
    0 < fTrunc s 1 x := by
  exact fTrunc_pos_aux hs0 (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) x hx

/-- `[N] (2.f-L1)` (L309-311): `f_1` is integrable and `‖f_1‖_{L¹} = c_φ ‖φ‖_{L¹}/(d-s)`. -/
theorem fTrunc_integrable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Integrable (fTrunc s 1 : Euc d → ℝ) ∧
      ∫ x : Euc d, fTrunc s 1 x = cPhi d s * (∫ x : Euc d, phi x) / ((d : ℝ) - s) := by
  exact fTrunc_integrable_aux (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])

/-- `[N] L297` (`s > 0`) and `(2.log-g)`, `(2.log-g-origin)` (L299-307): `g_1` extends smoothly
across the origin, with the value `g_1(0)` of `g1Zero` (so `g1` is `C^∞` on all of `ℝ^d`). -/
theorem g1_smooth (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ContDiff ℝ ∞ (g1 s : Euc d → ℝ) := by
  exact g1_smooth_aux hs0 (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])

/-- `[N] (2.fourierpositive)` consequence, second form (L313-319): for a bounded compactly supported
density `ρ` (the only use: `‖μ‖²_{f₁}`), `‖ρ‖²_{f₁} = ∫ f̂₁ |ρ̂|² dξ`, absolutely convergent.  (For a general
finite measure, e.g. `σ = δ₀`, `|σ̂|² f̂₁` is not integrable and `f₁(0)` is a junk value, so the
statement is restricted to densities.) -/
theorem quadForm_f1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) :
    Integrable (fun ξ : Euc d => f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2) ∧
      kerEnergy (fTrunc s 1) (SMeas.ofDensity ρ) =
        ∫ ξ, f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2 := by
  exact quadForm_f1_aux hd hs0 hsd ρ hρ

/-- `[N] (2.fourierpositive)`, `(2.log-positive-form)` (L313-319, L401-406): for a compactly supported
finite signed measure `σ` (of mass zero when `s = 0`), `‖σ‖²_{g_1} = ∫ ĝ_1 |σ̂|² dξ` (for `s = 0`
this is "applying `(2.log-g)` to `σ^{⊗2}`, Fubini–Tonelli", L401-405; `ĝ_1` is the function
`g1Hat`, no value at `ξ = 0` is needed). -/
theorem quadForm_g1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (σ : SMeas d)
    (hf : σ.IsFinite) (hc : σ.CompactSupp) (hm : s = 0 → σ.mass = 0) :
    Integrable (fun ξ : Euc d => g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) ∧
      kerEnergy (g1 s) σ = ∫ ξ, g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2 := by
  by_cases hs : s = 0
  · exact quadForm_g1_zero hs hsd σ hf hc (hm hs)
  · exact quadForm_g1_pos (lt_of_le_of_ne hs0 (Ne.symm hs)) hsd σ hf

/-- `[N] L267`: `f_1` is positive definite on bounded compactly supported densities (`‖ρ‖²_{f₁} ≥ 0`,
from `quadForm_f1` and `f1Hat ≥ 0`; for general measures the value `fTrunc s 1 0` is junk, so the
statement is restricted to densities). -/
theorem posDef_f1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) : 0 ≤ kerEnergy (fTrunc s 1) (SMeas.ofDensity ρ) := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [(quadForm_f1 hd hs0 hsd ρ hρ).2]
  exact integral_nonneg fun ξ => mul_nonneg (f1Hat_nonneg hs0 hs2 ξ) (sq_nonneg _)

/-- `[N] L267`: `g_1` is positive definite (`s > 0`) resp. conditionally positive definite (`s = 0`,
mass zero) on compactly supported finite signed measures (`g1` has the explicit smooth value at `0`). -/
theorem posDef_g1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (σ : SMeas d)
    (hf : σ.IsFinite) (hc : σ.CompactSupp) :
    (s = 0 → σ.mass = 0 → 0 ≤ kerEnergy (g1 s) σ) ∧ (0 < s → 0 ≤ kerEnergy (g1 s) σ) := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  refine ⟨fun hs hmass => ?_, fun hs => ?_⟩
  · rw [(quadForm_g1 hd hs0 hsd σ hf hc (fun _ => hmass)).2]
    exact integral_nonneg fun ξ => mul_nonneg (g1Hat_nonneg hs0 hs2 ξ) (sq_nonneg _)
  · rw [(quadForm_g1 hd hs0 hsd σ hf hc (fun h0 => absurd h0 hs.ne')).2]
    exact integral_nonneg fun ξ => mul_nonneg (g1Hat_nonneg hs0 hs2 ξ) (sq_nonneg _)

/-- `(2.lowcoercive)` (`[N] L269`, proof L320-321): for every `R > 0` there is `c_R > 0` with
`ĝ_1(ξ) ≥ c_R |ξ|^{-2α}` for `0 < |ξ| ≤ R`. -/
theorem lowcoercive (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (R : ℝ) (hR : 0 < R) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ ξ : Euc d, ξ ≠ 0 → ‖ξ‖ ≤ R →
      cR * ‖ξ‖ ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ := by
  exact lowcoercive_aux (by omega) hs0 hsd hR

/-- `(2.shortcoercive)` (`[N] L271`, proof L321): `f̂_1(ξ) ≥ c (1+4π²|ξ|²)^{-α}` for all `ξ`. -/
theorem shortcoercive (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Euc d,
      c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(alphaE d s)) ≤ f1Hat s ξ := by
  exact shortcoercive_aux (by omega) hs0 hsd

/-- `(2.fcomparison)` (`[N] L276-282`, from the spatial formulas L295, L301):
`f_1 ∼ |x|^{-s}` (`0 < |x| ≤ 1`, `s > 0`), `∼ 1 + |log|x||` (`0 < |x| ≤ 1`, `s = 0`),
`∼ |x|^{-2d-4}` (`|x| ≥ 1`), with constants depending only on `d, s`. -/
theorem fcomparison (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Euc d, x ≠ 0 →
      (0 < s → ‖x‖ ≤ 1 →
        c * ‖x‖ ^ (-s) ≤ fTrunc s 1 x ∧ fTrunc s 1 x ≤ C * ‖x‖ ^ (-s)) ∧
      (s = 0 → ‖x‖ ≤ 1 →
        c * (1 + |Real.log ‖x‖|) ≤ fTrunc s 1 x ∧ fTrunc s 1 x ≤ C * (1 + |Real.log ‖x‖|)) ∧
      (1 ≤ ‖x‖ →
        c * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) ≤ fTrunc s 1 x ∧
          fTrunc s 1 x ≤ C * ‖x‖ ^ (-(2 * (d : ℝ) + 4))) := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ := cmp_far (d := d) hs0 hs2
  by_cases hs : s = 0
  · obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ := cmp_near_zero (d := d) hs
    refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, fun x hx => ?_⟩
    refine ⟨fun hs' => absurd hs hs'.ne', fun _ hx1 => ?_, fun hx1 => ?_⟩
    · obtain ⟨a, b⟩ := h₂ x hx hx1
      have hp : 0 ≤ 1 + |Real.log ‖x‖| := by positivity
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hp) a,
        le_trans b (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)⟩
    · obtain ⟨a, b⟩ := h₁ x hx1
      have hp : 0 ≤ ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by positivity
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hp) a,
        le_trans b (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)⟩
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ := cmp_near_pos (d := d) hs' hs2
    refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, fun x hx => ?_⟩
    refine ⟨fun _ hx1 => ?_, fun h => absurd h hs, fun hx1 => ?_⟩
    · obtain ⟨a, b⟩ := h₂ x hx hx1
      have hp : 0 ≤ ‖x‖ ^ (-s) := by positivity
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hp) a,
        le_trans b (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)⟩
    · obtain ⟨a, b⟩ := h₁ x hx1
      have hp : 0 ≤ ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by positivity
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hp) a,
        le_trans b (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)⟩

/-- `[N] L283` ("In particular, `f_1` is bounded below by a positive constant on `0 < |x| ≤ √d`"). -/
theorem fTrunc_lower_near (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ Real.sqrt d → c ≤ fTrunc s 1 x := by
  obtain ⟨c, C, hc, hC, h⟩ := fcomparison (d := d) (s := s) hd hs0 hsd
  have hd3 : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  refine ⟨min c (c * (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))), lt_min hc (by positivity), fun x hx hxd => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨h1, h2, h3⟩ := h x hx
  by_cases hx1 : ‖x‖ ≤ 1
  · by_cases hs : s = 0
    · have := (h2 hs hx1).1
      have : 1 ≤ 1 + |Real.log ‖x‖| := by linarith [abs_nonneg (Real.log ‖x‖)]
      calc min c (c * (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))) ≤ c := min_le_left _ _
        _ = c * 1 := (mul_one _).symm
        _ ≤ c * (1 + |Real.log ‖x‖|) := by gcongr
        _ ≤ _ := (h2 hs hx1).1
    · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have h1' := (h1 hs' hx1).1
      have : 1 ≤ ‖x‖ ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hxn hx1 (by linarith)
      calc min c (c * (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))) ≤ c := min_le_left _ _
        _ = c * 1 := (mul_one _).symm
        _ ≤ c * ‖x‖ ^ (-s) := by gcongr
        _ ≤ _ := h1'
  · have hx1' : 1 ≤ ‖x‖ := le_of_lt (not_le.1 hx1)
    have h3' := (h3 hx1').1
    have : (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4)) ≤ ‖x‖ ^ (-(2 * (d : ℝ) + 4)) :=
      Real.rpow_le_rpow_of_nonpos hxn hxd (by linarith)
    calc min c (c * (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))) ≤ c * (Real.sqrt d) ^ (-(2 * (d : ℝ) + 4)) :=
          min_le_right _ _
      _ ≤ c * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by gcongr
      _ ≤ _ := h3'

/-- `[N] L283`, L321 ("`f_1 ∈ L^{p'}` for `p > d/(d-s)`"): for `p ∈ (d/(d-s), ∞]` and its Hölder
conjugate `q` (`p⁻¹ + q⁻¹ = 1`). -/
theorem fTrunc_Lq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    MemLp (fTrunc s 1 : Euc d → ℝ) q volume := by
  exact fTrunc_Lq_aux hd hs0 hsd p q hp hpq

end HRS.Commutator.Whole
