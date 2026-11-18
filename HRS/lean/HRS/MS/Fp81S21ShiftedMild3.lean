import HRS.MS.Fp81S21ShiftedMild2
import HRS.MS.Fp81S21WindowOrbitDecay2

/-!
# HRS S2.1(iii), packet 9c: regularity of the shifted feature family

This packages the moving orbit decay and the nonlinear terminal-time regularity
into the existing `S105Feat` contract.  The latter is the compiled interface
for boundedness, continuity in position, and weak measurability in physical
time of the `KSpace`-valued window feature.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R26T3

/-- The compiled window feature family for the shifted observation interval.
Its parameter `r` is physical noise time; at local time `u`, it is the feature
`fp81s21_shiftedNoiseFeature ... b u`. -/
def fp81s21_shiftedNoiseFeatureFamily
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (H b : ℝ) : Fin p.d → ℝ → Euc p.d →
      KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
  fun a r x => r2WindowFeature (r26t3_coeff R)
    ((wholeSpaceIndex p.d : ℕ) : ℝ) H (gradComp a) b r x

/-- The oscillator orbit package makes the shifted `KSpace` feature bounded,
continuous in position, and weakly measurable in physical noise time.  The
constants precede `H` and `b`; the feature bound itself may depend on `H`. -/
theorem fp81s21_shiftedNoiseFeature_regular (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Cs0 cdec : ℝ, 0 ≤ Cs0 ∧ 0 < cdec ∧
          ∀ H b : ℝ, 0 < H → 0 ≤ b →
            HRS.MS.R2GenInit.S105Feat p.d
              ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
              (fp81s21_shiftedNoiseFeatureFamily p R H b) := by
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
  have hex0 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      ∃ f, IsClassicalAdjointW (r26t3_coeff R) t
        (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) f := by
    intro α t ht
    exact fp81s21_adjoint_of_osc_test p R
      (HRS.MS.GenPath.s56_isOscTest
        ((wholeSpaceIndex p.d : ℕ) : ℝ) α) ht
  have hex1 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      ∃ f, IsClassicalAdjointW (r26t3_coeff R) t
        (generatorW (r26t3_coeff R) t
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)) f := by
    intro α t ht
    obtain ⟨hex, -, -⟩ :=
      hTerm R.ρβ R.thermal R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    simpa only [s103nData, r26t3_coeff] using
      hex ⟨1, by omega⟩ t ⟨ht, le_rfl⟩
  refine ⟨Cs, cdec, hCs, hcdec, ?_⟩
  intro H b hH hb
  have hmeasU : ∀ r : ℝ, 0 ≤ r → ∀ (a : Fin p.d)
      (α : MultiIndex p.d) (x : Euc p.d),
      AEStronglyMeasurable
        (fun u : ℝ => if r < b + u then
          gradComp a (propagatorW (r26t3_coeff R) r (b + u)
            (generatorW (r26t3_coeff R) (b + u)
              (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))) x
          else 0)
        (volume.restrict (Icc (0 : ℝ) H)) := by
    intro r hr a α x
    exact HRS.MS.R2WinErr.s104n_hobs_traj
      p.hd p.hs0 hsd p.ha p.hβ hNL R.thermal htraj H b r hH.le hb hr a α x
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  have hfeat := HRS.MS.R2GenInit.s105_win_feat
    (show 1 ≤ p.d by omega) (r26t3_coeff R) (4 * p.d + 42) m H b cdec Cs
    hb hH.le hcdec.le hCs hsum hG hG' hphi hex0 hex1 hmeasU
  change HRS.MS.R2GenInit.S105Feat p.d m H (b + H)
    (fun a r x => r2WindowFeature (r26t3_coeff R) m H (gradComp a) b r x)
  exact hfeat

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoiseFeature_regular

end HRS.Fp81.S21

end
