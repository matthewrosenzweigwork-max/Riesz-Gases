import HRS.Main.ThermAux1
import HRS.Main.ThermAux2

/-!
# THERM helper 3: `ofFun` linearity, the rate `j_{N,m} → 0`, and Example 2.6's limit
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem therm_coord_smul {m : ℝ} (a : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (a • F) k = a * NegSobolev.coord F k := by
  unfold NegSobolev.coord
  exact congrFun (lp.coeFn_smul a (F : lp (fun _ : NonzeroLattice d => ℝ) 2)) k

theorem therm_ext_coord {m : ℝ} {F G : NegSobolev d m} (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) :
    F = G :=
  (lp.ext (funext h) : (F : lp (fun _ : NonzeroLattice d => ℝ) 2) = G)

/-- `ofSeq` is homogeneous. -/
theorem therm_ofSeq_smul (m a : ℝ) (c : NonzeroLattice d → ℝ) :
    NegSobolev.ofSeq m (fun k => a * c k) = a • NegSobolev.ofSeq m c := by
  classical
  by_cases ha : a = 0
  · subst ha
    have hz : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (0 * c k)) 2 := by
      have : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (0 * c k)) = 0 := by
        funext k; simp
      rw [this]; exact zero_memℓp
    refine therm_ext_coord fun k => ?_
    rw [NegSobolev.coord_ofSeq_of_mem _ hz, therm_coord_smul]
    simp
  · by_cases h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2
    · have h' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a * c k)) 2 := by
        have := h.const_smul a
        convert this using 1
        funext k
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      refine therm_ext_coord fun k => ?_
      rw [NegSobolev.coord_ofSeq_of_mem _ h', therm_coord_smul, NegSobolev.coord_ofSeq_of_mem _ h]
      ring
    · have h' : ¬ Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a * c k)) 2 := by
        intro h'
        apply h
        have := h'.const_smul a⁻¹
        convert this using 1
        funext k
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      have e1 : NegSobolev.ofSeq m c = 0 := by
        unfold NegSobolev.ofSeq; exact dif_neg h
      have e2 : NegSobolev.ofSeq m (fun k => a * c k) = 0 := by
        unfold NegSobolev.ofSeq; exact dif_neg h'
      rw [e1, e2, smul_zero]

end Main

end HRS
