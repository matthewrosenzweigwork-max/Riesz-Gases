import HRS.MS.R26T8AP28
import HRS.MS.R26T8AP27

/-!
# S8.2 T8A P29 (part a): weighted pair-kernel bookkeeping for the smooth remainder and its inverse
`ContDiff 8` with weighted jet bounds `A Phase2S82.pairWeight K`, `K < M`, give `MemCMpair M 8` and `pairNormE M 8 ≤ A`; conversely
`pairNormE M 8 Ψ ≤ B` gives the jet bounds `B Phase2S82.pairWeight M`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_pairWeight_mono {K M : ℝ} (hK : K ≤ M) (x y : Euc d) : Phase2S82.pairWeight K x y ≤ Phase2S82.pairWeight M x y := by
  unfold Phase2S82.pairWeight
  have h1 : jbracket x ^ K ≤ jbracket x ^ M := Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb x) hK
  have h2 : jbracket y ^ K ≤ jbracket y ^ M := Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb y) hK
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (s83_jb_pos y).le _) (Real.rpow_nonneg (s83_jb_pos x).le _)

theorem r26t8a_p29_pair_of_bound {R : Euc d → Euc d → ℝ} {A K M : ℝ} (hA : 0 ≤ A) (hKM : K < M)
    (hR : ContDiff ℝ 8 (Function.uncurry R))
    (hb : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ A * Phase2S82.pairWeight K x y) :
    MemCMpair M 8 R ∧ pairNormE M 8 R ≤ ENNReal.ofReal A := by
  have hg : ∀ k : ℕ, k ≤ 8 → ∃ CR : ℝ, ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ k (Function.uncurry R) (x, y)‖ ≤ CR * jbracket x ^ K * jbracket y ^ K :=
    fun k hk => ⟨A, fun x y => by
      have := hb k hk x y
      unfold Phase2S82.pairWeight at this
      simpa [mul_assoc] using this⟩
  have hP := s8h2_pair_of_growth (M := M) hKM (F := Function.uncurry R) (by exact_mod_cast hR) hg
  refine ⟨s8h_pair_iff.2 hP, ?_⟩
  refine r26t8a_p24_norm_le (fun i hi z => ?_)
  refine (hb i hi z.1 z.2).trans ?_
  exact mul_le_mul_of_nonneg_left (r26t8a_p29_pairWeight_mono (le_of_lt hKM) z.1 z.2) hA

theorem r26t8a_p29_of_norm {Ψ : Euc d → Euc d → ℝ} {M B : ℝ} (hB : 0 ≤ B) (h : pairNormE M 8 Ψ ≤ ENNReal.ofReal B)
    (j : ℕ) (hj : j ≤ 8) (x y : Euc d) :
    ‖iteratedFDeriv ℝ j (Function.uncurry Ψ) (x, y)‖ ≤ B * Phase2S82.pairWeight M x y := by
  have h1 : ENNReal.ofReal (jbracket x ^ (-M) * jbracket y ^ (-M) * ‖iteratedFDeriv ℝ j (Function.uncurry Ψ) (x, y)‖) ≤
      pairNormE M 8 Ψ :=
    le_iSup₂_of_le (⟨j, by omega⟩ : Fin (8 + 1)) (x, y) le_rfl
  have h2 := (h1.trans h)
  rw [ENNReal.ofReal_le_ofReal_iff hB] at h2
  have hw : 0 < Phase2S82.pairWeight M x y := s8h_w_pos M (x, y)
  have e : jbracket x ^ (-M) * jbracket y ^ (-M) = (Phase2S82.pairWeight M x y)⁻¹ := by
    unfold Phase2S82.pairWeight
    rw [Real.rpow_neg (s83_jb_pos x).le, Real.rpow_neg (s83_jb_pos y).le, mul_inv]
  rw [e] at h2
  rw [inv_mul_le_iff₀ hw] at h2
  linarith

end HRS.MS.R26T8A

end
