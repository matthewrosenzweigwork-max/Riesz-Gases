import HRS.MS.Fp81S21ShiftedMild6
import HRS.MS.Fp81S21OrbitMaximalSix

/-!
# HRS S2.1(iii), packet 9c: a feature bound uniform in the shifted window

The `s104_window_feature` estimate has the decay factor `s104_theta cdec b r`.
Since that factor is at most one, the remaining bound depends on the horizon
and the orbit constants, but not on the window start `b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R26T3
open HRS.MP.RdRem

/-- A uniform-in-`b` bound for the shifted feature.  The bound may depend on
the fixed horizon `H`, while its construction is independent of the window
start. -/
theorem fp81s21_shiftedNoiseFeature_uniform_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Cs0 cdec : ℝ, 0 ≤ Cs0 ∧ 0 < cdec ∧
          ∀ H : ℝ, 0 < H → ∃ B : ℝ, 0 ≤ B ∧
            ∀ b : ℝ, 0 ≤ b → ∀ a : Fin p.d,
              ∀ r ∈ Icc (0 : ℝ) (b + H), ∀ x,
                ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B := by
  obtain ⟨δ0, Co, co, hδ0, hδ0half, hco, hcommon⟩ :=
    fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hOrbit : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co := by
    intro ρβ hρβ
    exact (hcommon δ hδ hδle ρβ hρβ).1
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgrad⟩ :=
    fp81s21_orbitGrad_commonRadius p p.hT hco hOrbit
  have hTerm : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        S104bTermRegGen p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ := by
    intro ρβ hρβ
    exact (hcommon δ hδ hδle ρβ hρβ).2.2.1
  have hNL : S104nAllOrb p.d p.s p.a p.β δ p.c₁ p.C₁ :=
    HRS.MS.R2WinErr.s104b_allOrb_of_termRegGen hTerm
  have htraj : IsR2WindowTrajectory p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ R.ρ :=
    Or.inr ⟨R.ε, R.ψ, R.admissible, R.resulting⟩
  have hgradR := hgrad R.ρβ R.thermal R.ρ htraj
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  obtain ⟨Cphi, hCphi0, hphi'⟩ := HRS.MS.R2WinErr.s104_hphi hd1
  let Cs : ℝ := max Cs0 Cphi
  have hCs : 0 ≤ Cs := hCs0.trans (le_max_left _ _)
  have hG : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
        (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
        (Cs * s104_b p.d α) cdec := by
    intro α t ht
    have hle : Cs0 * s104_b p.d α ≤ Cs * s104_b p.d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    have h0 : R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
        (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
        (Cs0 * s104_b p.d α) cdec := by
      simpa only [r26t3_coeff] using (hgradR α).1 t ht
    exact HRS.MS.R2WinErr.s104_R2OrbitGrad_mono
      (r26t3_coeff R) h0 hle
  have hG' : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
        (generatorW (r26t3_coeff R) t
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
        (Cs * s104_b p.d α) cdec := by
    intro α t ht
    have hle : Cs0 * s104_b p.d α ≤ Cs * s104_b p.d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    have h0 : R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
        (generatorW (r26t3_coeff R) t
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
        (Cs0 * s104_b p.d α) cdec := by
      simpa only [r26t3_coeff] using (hgradR α).2 t ht
    exact HRS.MS.R2WinErr.s104_R2OrbitGrad_mono
      (r26t3_coeff R) h0 hle
  have hphi : ∀ α : MultiIndex p.d, ∀ a : Fin p.d,
      ContDiff ℝ (4 * p.d + 42 : ℕ)
          (fun x => gradComp a
            (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) x) ∧
        ∀ j ≤ 4 * p.d + 42, ∀ x,
          ‖iteratedFDeriv ℝ j
            (fun x => gradComp a
              (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) x) x‖ ≤
            Cs * s104_b p.d α := by
    intro α a
    exact ⟨(hphi' α a).1, fun j hj x =>
      ((hphi' α a).2 j hj x).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (s104_b_nonneg α))⟩
  refine ⟨Cs0, cdec, hCs0, hcdec, ?_⟩
  intro H hH
  let B : ℝ := (2 + (p.d : ℝ) ^ (4 * p.d + 42) * Real.sqrt H) *
    (Cs * ∑' α : MultiIndex p.d, s104_b p.d α)
  have hts : 0 ≤ ∑' α : MultiIndex p.d, s104_b p.d α :=
    tsum_nonneg fun α => s104_b_nonneg α
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro b hb a r hr x
  have hmeasU : ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      AEStronglyMeasurable
        (fun u : ℝ => if r < b + u then
          gradComp a (propagatorW (r26t3_coeff R) r (b + u)
            (generatorW (r26t3_coeff R) (b + u)
              (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))) x
          else 0)
        (volume.restrict (Icc (0 : ℝ) H)) := by
    intro α x
    exact HRS.MS.R2WinErr.s104n_hobs_traj
      p.hd p.hs0 hsd p.ha p.hβ hNL R.thermal htraj H b r hH.le hb hr.1 a α x
  have hfeat := HRS.MS.R2WinErr.s104_window_feature
    hd1 (r26t3_coeff R) (4 * p.d + 42)
    ((wholeSpaceIndex p.d : ℕ) : ℝ) H cdec Cs hH.le hcdec.le hCs
    (s104_b p.d) (fun α => s104_b_nonneg α) hsum hG hG' hphi hb hr.1 a
    hmeasU
  have h0 := hfeat.2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero] at h0
  dsimp [B]
  exact h0.trans (mul_le_of_le_one_right (by positivity)
    (s104_theta_le_one hcdec.le b r))

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoiseFeature_uniform_bound

/-- Every oscillator coordinate is bounded by the `OscDual` norm. -/
theorem fp81s21_shiftedNoise_coord_abs_le_norm {d : ℕ} {m : ℝ}
    (u : OscDual d m) (α : MultiIndex d) :
    |OscDual.coord u α| ≤ ‖u‖ := by
  have hsumm := OscDual.coord_sq_summable' u
  have hsq : OscDual.coord u α ^ 2 ≤
      ∑' β : MultiIndex d, OscDual.coord u β ^ 2 :=
    hsumm.le_tsum α (fun β _ => sq_nonneg (OscDual.coord u β))
  calc
    |OscDual.coord u α| = Real.sqrt (OscDual.coord u α ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (∑' β : MultiIndex d, OscDual.coord u β ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ‖u‖ := (OscDual.norm_eq_coord u).symm

/-- The supplied sixth moment theorem gives a maximal bound for the reconstructed
continuous martingale. The local bracket constant is `H * 2 β⁻¹ d B²`. -/
theorem fp81s21_shiftedNoise_reconstruction_maximal_six
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) H, ENNReal.ofReal (‖reconstructPath
        ((wholeSpaceIndex p.d : ℕ) : ℝ) H
        (Classical.choose (fp81s21_shiftedNoise_feature_martingale
          p R hN A F hH hb hphysical)) ζ t‖)) ^ 6 ∂A.P ≤
        ENNReal.ofReal (C₆ * (H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)) ^ 3) := by
  let z := fp81s21_shiftedNoise_feature_martingale p R hN A F hH hb hphysical
  let M := Classical.choose z
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ b.toNNReal
  let Sg : ℝ → A.Ω → KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H →L[ℝ]
      KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H →L[ℝ] ℝ :=
    fun u ζ => hsCovForm (s105Phi
      (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
      (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ)
  have hHM : IsHilbertMartingaleWithCovariation A.P ℱb H M Sg := by
    exact (Classical.choose_spec z).2
  have htrace := fp81s21_shiftedNoise_trace_integral
    p R hN A F hH hb hphysical B hB hbound
  let K : ℝ := H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)
  have hβinv : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨C₆, hC₆, hmax⟩ := fp81s21_orbit_maximal_six_of_bracket_le
    ((wholeSpaceIndex p.d : ℕ) : ℝ) H hH.le p.d
  refine ⟨C₆, hC₆, ?_⟩
  simpa only [M, ℱb, Sg, K] using hmax A.P ℱb M Sg hHM K hK htrace

/-- A countable dense-time version of the shifted noise maximal estimate.
The reconstruction is the continuous-process version supplied by the Hilbert
martingale; the equality to the displayed Itô noise is asserted on the
rational local times, where the fixed-time reconstruction theorem applies. -/
theorem fp81s21_shiftedNoise_rational_sup_six
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (hC : OscAdjointInput (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) (b + H))
    (hK : ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ) H b a r x)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B)
    (α : MultiIndex p.d) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧
      ∫⁻ ζ, (⨆ q : ℚ, ENNReal.ofReal (abs
        (fp81s21_shiftedNoiseDiff p R A F b
          (b + mrrClamp H (q : ℝ)) α ζ))) ^ 6 ∂A.P ≤
        ENNReal.ofReal (C₆ * (H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)) ^ 3) := by
  let z := fp81s21_shiftedNoise_feature_martingale p R hN A F hH hb hphysical
  let M := Classical.choose z
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let Gsup : A.Ω → ℝ≥0∞ := fun ζ => ⨆ t : Set.Icc (0 : ℝ) H,
    ENNReal.ofReal ‖reconstructPath m H M ζ t‖
  let Qsup : A.Ω → ℝ≥0∞ := fun ζ => ⨆ q : ℚ, ENNReal.ofReal (abs
    (fp81s21_shiftedNoiseDiff p R A F b (b + mrrClamp H (q : ℝ)) α ζ))
  obtain ⟨C₆, hC₆, hmax⟩ := fp81s21_shiftedNoise_reconstruction_maximal_six
    p R hN A F hH hb hphysical B hB hbound
  have hqEq : ∀ᵐ ζ ∂A.P, ∀ q : ℚ,
      OscDual.coord (reconstructPath m H M ζ (mrrClamp H (q : ℝ))) α =
        fp81s21_shiftedNoiseDiff p R A F b
          (b + mrrClamp H (q : ℝ)) α ζ := by
    apply ae_all_iff.2
    intro q
    exact fp81s21_shiftedNoise_reconstruction_at p R hN A F hH hb
      hphysical hC hK (mrrClamp_mem hH.le (q : ℝ)) α
  have hsup : ∀ᵐ ζ ∂A.P, Qsup ζ ≤ Gsup ζ := by
    filter_upwards [hqEq] with ζ hζ
    apply iSup_le
    intro q
    let s : ℝ := mrrClamp H (q : ℝ)
    have hs : s ∈ Icc (0 : ℝ) H := mrrClamp_mem hH.le (q : ℝ)
    let t : Set.Icc (0 : ℝ) H := ⟨s, hs⟩
    have hcoord := fp81s21_shiftedNoise_coord_abs_le_norm
      (reconstructPath m H M ζ s) α
    have hvalue : |fp81s21_shiftedNoiseDiff p R A F b (b + s) α ζ| ≤
        ‖reconstructPath m H M ζ s‖ := by
      rw [← hζ q]
      exact hcoord
    exact le_iSup_of_le t (ENNReal.ofReal_le_ofReal hvalue)
  refine ⟨C₆, hC₆, ?_⟩
  calc
    ∫⁻ ζ, (Qsup ζ) ^ 6 ∂A.P ≤ ∫⁻ ζ, (Gsup ζ) ^ 6 ∂A.P := by
      apply lintegral_mono_ae
      filter_upwards [hsup] with ζ hζ
      gcongr
    _ ≤ ENNReal.ofReal (C₆ * (H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)) ^ 3) := by
      simpa only [Gsup, M] using hmax

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_reconstruction_maximal_six
#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_rational_sup_six
#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_coord_abs_le_norm

end HRS.Fp81.S21

end
