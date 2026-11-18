import HRS.MS.Fp81S21RemotePhysicalN2
import HRS.MS.Fp81S21RemotePhysicalG4

/-! Packet 38Profile: a common exponential tail for the supplied physical records. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

local instance fp81s21_remotePhysical_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_remotePhysical_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_remotePhysical_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The particle and Gaussian records share exactly the future, start and test.
Their probability spaces, histories and prediction paths remain independent inputs.
The constants follow `Q` and precede every consumer variable, including `Y` and `L`.
The radius is the minimum of the two producer radii. -/
theorem fp81s21_remote_physical (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)),
      fp81s21_moving_heat_full_clause p R future →
      ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
        (a : ℝ) (ha : 0 ≤ a) (D : fp81s21_finproj_shared_data p R a A F)
        (Cmix cdec : ℝ) (K : ℝ → ℝ),
      fp81s21_shared_physical_window_covariance_identification p R a ha A Cmix cdec K D.Fj →
      ∀ (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
        let H := a + p.T
        let W := HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
        let Ad := fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (D.Yh ω τ))
        let Fdw := fun ω t => fp81s21_weightedDrift_windowCum
          (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl (r26t3_coeff R)
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t
        let Aj := fun ω τ => fp81s21_covariance_pairingCLM
          (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
        let Fjw := fun ω t => fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
        ∀ (WN : fp81s21_WindowRS A.P H Ad Fdw Aj Fjw) (G : GaussianRealization R)
          (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))),
        fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G))
          Q.MUG 0 (a + p.T) UG →
        fp81s21_TimeL2Rep G.P (Q.S.qe G) (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB →
        ∀ (Y : G.Ω → ℝ → Window p)
          (WG : fp81s21_remote_G_RS_at Q future G a ha UG UB Φ Y) (L : ℝ), 0 < L →
          |fp81s21_WindowRS_corr WN 0 (max (a - L) 0)| +
            |fp81s21_WindowRS_corr WG 0 (max (a - L) 0)| ≤ C * Real.exp (-c * L)) := by
  obtain ⟨δN, hδN, hδNh, hNbound⟩ := fp81s21_remote_physical_N p
  obtain ⟨δG, hδG, _, hGbound⟩ := fp81s21_remote_physical_G_at p
  refine ⟨min δN δG, lt_min hδN hδG, (min_le_left _ _).trans hδNh, ?_⟩
  intro δ hδ hδle R Q
  obtain ⟨CN, cN, hCN, hcN, hn⟩ :=
    hNbound δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨CG, cG, hCG, hcG, hg⟩ :=
    hGbound δ hδ (hδle.trans (min_le_right _ _)) R Q
  refine ⟨max 1 (CN + CG), min cN cG,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), lt_min hcN hcG, ?_⟩
  intro future hf N hN A F a ha D Cmix cdec K hcov Φ hΦ
  dsimp only
  intro WN G UG UB hUG hUB Y WG L hL
  have hn' := hn future hf N hN A F a ha D Cmix cdec K hcov Φ hΦ WN L hL
  have hg' := hg future hf G a ha UG UB hUG hUB Φ hΦ Y WG L hL
  have heN : Real.exp (-cN * L) ≤ Real.exp (-(min cN cG) * L) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hL.le)
  have heG : Real.exp (-cG * L) ≤ Real.exp (-(min cN cG) * L) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hL.le)
  calc
    _ ≤ CN * Real.exp (-cN * L) + CG * Real.exp (-cG * L) := add_le_add hn' hg'
    _ ≤ CN * Real.exp (-(min cN cG) * L) + CG * Real.exp (-(min cN cG) * L) :=
      add_le_add (mul_le_mul_of_nonneg_left heN hCN.le)
        (mul_le_mul_of_nonneg_left heG hCG.le)
    _ = (CN + CG) * Real.exp (-(min cN cG) * L) := (add_mul _ _ _).symm
    _ ≤ max 1 (CN + CG) * Real.exp (-(min cN cG) * L) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

#print axioms fp81s21_remote_physical
end HRS.Fp81.S21
end
