import HRS.MC.Sec7Vocab
import HRS.Equilibrium.FieldSingAux

/-!
# Packet `s7_S16d_modePair_clm`: the mode-pair map is a bounded linear map
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7

/-- the pair map as a linear map -/
def s7d_lin (d : ℕ) (m : ℝ) (k : NonzeroLattice d) :
    NegSobolev d m →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun F := s7_modePair m k F
  map_add' F G := by
    have hadd : ∀ j, NegSobolev.fourierCoeff (F + G) j =
        NegSobolev.fourierCoeff F j + NegSobolev.fourierCoeff G j :=
      fun j => (HRS.FieldSingAux.coordCLM m j).map_add F G
    ext i
    fin_cases i <;> simp [s7_modePair, hadd]
  map_smul' r F := by
    have hsm : ∀ j, NegSobolev.fourierCoeff (r • F) j = r * NegSobolev.fourierCoeff F j :=
      fun j => (HRS.FieldSingAux.coordCLM m j).map_smul r F
    ext i
    fin_cases i <;> simp [s7_modePair, hsm]

theorem s7d_neg_ne {d : ℕ} (k : NonzeroLattice d) : s7_neg k ≠ k := by
  intro h
  have h1 : (-k.1 : Lattice d) = k.1 := congrArg Subtype.val h
  apply k.2
  funext i
  have := congrFun h1 i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

theorem s7d_norm_le (d : ℕ) (m : ℝ) (k : NonzeroLattice d) (F : NegSobolev d m) :
    ‖s7_modePair m k F‖ ≤ Lattice.jp k.1 ^ m * ‖F‖ := by
  have hj : 0 < Lattice.jp k.1 ^ m := Real.rpow_pos_of_pos (Torus.jp_pos k.1) m
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have h2 : (NegSobolev.coord F k) ^ 2 + (NegSobolev.coord F (s7_neg k)) ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [hn, ← Finset.sum_pair (f := fun k => NegSobolev.coord F k ^ 2) (s7d_neg_ne k).symm]
    exact hs.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hjn : Lattice.jp (s7_neg k).1 = Lattice.jp k.1 := Torus.jp_neg k.1
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [s7_modePair, NegSobolev.fourierCoeff]
  simp only [ite_true, Fin.one_eq_zero_iff, Nat.succ_ne_self, ite_false, Real.norm_eq_abs, sq_abs]
  rw [hjn]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc _ = (Lattice.jp k.1 ^ m) ^ 2 * (NegSobolev.coord F k ^ 2 + NegSobolev.coord F (s7_neg k) ^ 2) := by ring
    _ ≤ (Lattice.jp k.1 ^ m) ^ 2 * ‖F‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem s7_S16d_modePair_clm_proof (d : ℕ) (m : ℝ) (k : NonzeroLattice d) :
    ∃ π : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin 2), (∀ F, π F = s7_modePair m k F) ∧ ‖π‖ ≤ Lattice.jp k.1 ^ m := by
  have hj : 0 ≤ Lattice.jp k.1 ^ m := (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le
  refine ⟨(s7d_lin d m k).mkContinuous (Lattice.jp k.1 ^ m) (fun F => s7d_norm_le d m k F),
    fun F => rfl, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ hj _

end HRS.MC.Sec7.S16d
