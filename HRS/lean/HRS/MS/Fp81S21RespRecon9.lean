import HRS.MS.Fp81S21RespRecon8
import HRS.MS.Fp81S21ResponseWindow2
import HRS.MS.Fp81S21CosRecon

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr

/-- Uniform spatial bounds and pointwise time continuity for every shifted
oscillator orbit, in the smooth class on which the response is defined. -/
theorem fp81s21_respRecon_orbit_bounds (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ a : ℝ, 0 ≤ a → ∀ α : MultiIndex p.d,
          ∃ B : ℝ, 0 ≤ B ∧
            (∀ t ∈ Icc (0 : ℝ) p.T,
              MemCb (r26t3_J p.d) (r26t3_U R 0 (a + t)
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) ∧
              ∀ x, |r26t3_U R 0 (a + t)
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x| ≤ B) ∧
            ∀ x, ContinuousOn (fun t => r26t3_U R 0 (a + t)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x) (Icc (0 : ℝ) p.T) := by
  obtain ⟨δ0, Co, co, hδ0, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hhalf, fun δ hδ hδle R a ha α => ?_⟩
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  let B := |Co| * s103_b p.d α
  have hB0 : 0 ≤ B := mul_nonneg (abs_nonneg _) (s103_b_nonneg α)
  have hmono : Co * s103_b p.d α ≤ B :=
    mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
  refine ⟨B, hB0, ?_, ?_⟩
  · intro t ht
    have htime : 0 ≤ a + t := add_nonneg ha ht.1
    let Cf : WholeCoeff p.d := r26t3_coeff R
    let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have horb : S104nOrbit Cf φ (a + t) :=
      s104b_orbit_of_termRegGen hterm R.admissible R.resulting α (a + t) htime
    obtain ⟨f, hf⟩ := horb.ex0 (a + t) ⟨htime, le_rfl⟩
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α (a + t) htime
    have hsup := s103_orbitSup_mono hraw.1 hmono
    have hU := hsup (fun z => propagatorW Cf z (a + t) φ) hcanonical 0 ⟨le_rfl, htime⟩
    have hderiv := s103_cb_of_E hB0 hU.2
    have hmemK : MemCb (4 * p.d + 42) (propagatorW Cf 0 (a + t) φ) := by
      refine ⟨hU.1, ?_⟩
      intro j hj
      exact ⟨B, by rintro _ ⟨y, rfl⟩; exact hderiv j hj y⟩
    have hcbK : cbNorm (4 * p.d + 42) (propagatorW Cf 0 (a + t) φ) ≤ B := by
      apply (ENNReal.ofReal_le_ofReal_iff hB0).1
      rw [← s103_cbE_eq hmemK]
      exact hU.2
    have hmemJ : MemCb (r26t3_J p.d) (propagatorW Cf 0 (a + t) φ) :=
      HRS.MS.R2Obs.s910_memCb_mono (by dsimp [r26t3_J]; omega) hmemK
    have hcbJ : cbNorm (r26t3_J p.d) (propagatorW Cf 0 (a + t) φ) ≤ B :=
      (HRS.MS.R2Obs.s910_cbNorm_mono (by dsimp [r26t3_J]; omega) _).trans hcbK
    refine ⟨hmemJ, fun x => ?_⟩
    have hx := HRS.MS.Tc5.tc5_cb_sup_le hmemJ x
    have hx' : |propagatorW Cf 0 (a + t) φ x| ≤
        cbNorm (r26t3_J p.d) (propagatorW Cf 0 (a + t) φ) := by
      simpa [Real.norm_eq_abs] using hx
    exact hx'.trans hcbJ
  · intro x
    have hT0 : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
    have hOrbit : S104nOrbit (r26t3_coeff R)
        (oscTestFun (wholeSpaceIndex p.d) α) (a + p.T) :=
      s104b_orbit_of_termRegGen hterm R.admissible R.resulting α (a + p.T) hT0
    have hc := HRS.MS.S21A.s21a_cont_of_diff hT0 hOrbit x
    have hmap : Set.MapsTo (fun t : ℝ => a + t) (Icc (0 : ℝ) p.T)
        (Icc (0 : ℝ) (a + p.T)) := by
      intro t ht
      exact ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
    simpa [Function.comp_def, r26t3_U, r26t3_coeff] using
      hc.comp (continuousOn_const.add continuousOn_id) hmap

#print axioms fp81s21_respRecon_orbit_bounds

end HRS.Fp81.S21
end
