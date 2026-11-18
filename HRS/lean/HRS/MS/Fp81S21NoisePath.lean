import HRS.MS.Fp81S21ShiftedMild7

/-! Horizon-uniform quantitative bounds for shifted noise features. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R26T3

/-- The physical feature is regular and bounded by a constant chosen before the horizon. -/
theorem fp81s21_noisePath_feature (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
          S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
            (fp81s21_shiftedNoiseFeatureFamily p R H b) ∧
          ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
            ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤
              C0 * (1 + Real.sqrt H) := by
  obtain ⟨δ0, Co, co, hδ0, hδ0half, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δr, hδr, hδrh, hregular⟩ := fp81s21_shiftedNoiseFeature_regular p
  refine ⟨min δ0 δr, lt_min hδ0 hδr, (min_le_left _ _).trans hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδ0le : δ ≤ δ0 := hδle.trans (min_le_left _ _)
  have hδrle : δ ≤ δr := hδle.trans (min_le_right _ _)
  obtain ⟨Cr, cr, hCr, hcr, hphysical⟩ := hregular δ hδ hδrle R
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hOrbit : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co := by
    intro ρβ hρβ
    exact (hcommon δ hδ hδ0le ρβ hρβ).1
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgrad⟩ :=
    fp81s21_orbitGrad_commonRadius p p.hT hco hOrbit
  have hTerm : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        S104bTermRegGen p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ := by
    intro ρβ hρβ
    exact (hcommon δ hδ hδ0le ρβ hρβ).2.2.1
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
  let C0 : ℝ := max 2 ((p.d : ℝ) ^ (4 * p.d + 42)) *
    (Cs * ∑' α : MultiIndex p.d, s104_b p.d α)
  have hts : 0 ≤ ∑' α : MultiIndex p.d, s104_b p.d α :=
    tsum_nonneg fun α => s104_b_nonneg α
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro H hH b hb
  refine ⟨hphysical H b hH hb, ?_⟩
  let B : ℝ := (2 + (p.d : ℝ) ^ (4 * p.d + 42) * Real.sqrt H) *
    (Cs * ∑' α : MultiIndex p.d, s104_b p.d α)
  intro a r hr x
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
  have hbase : ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B := by
    dsimp [B]
    exact h0.trans (mul_le_of_le_one_right (by positivity)
      (s104_theta_le_one hcdec.le b r))
  refine hbase.trans ?_
  dsimp [B, C0]
  have hsqrt : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hfactor : 2 + (p.d : ℝ) ^ (4 * p.d + 42) * Real.sqrt H ≤
      max 2 ((p.d : ℝ) ^ (4 * p.d + 42)) * (1 + Real.sqrt H) := by
    have h1 := le_max_left (2 : ℝ) ((p.d : ℝ) ^ (4 * p.d + 42))
    have h2 := le_max_right (2 : ℝ) ((p.d : ℝ) ^ (4 * p.d + 42))
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hfactor (mul_nonneg hCs hts)]


#print axioms HRS.Fp81.S21.fp81s21_noisePath_feature
end HRS.Fp81.S21
