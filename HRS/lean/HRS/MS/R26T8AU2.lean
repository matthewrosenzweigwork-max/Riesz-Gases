import HRS.MS.R26T8AU1

/-!
# S8.2 T8A U2: symmetry is preserved by `rawNewton`, `localNewton`, `pairA`, `newtonDefect`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_U2_rawNewton_symm (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {F : Euc d → Euc d → ℝ}
    (hF : ∀ x y, F x y = F y x) (x y : Euc d) : rawNewton nu chi F x y = rawNewton nu chi F y x := by
  unfold rawNewton
  have hK : ∀ w : Euc d, newtonKernel d nu (-w) = newtonKernel d nu w := fun w => by
    unfold newtonKernel; simp [norm_neg]
  have hc : chi (y - x) = chi (x - y) := by rw [← neg_sub x y, hchi.2.1]
  rw [hc, add_comm y x]
  congr 1
  rw [← integral_neg_eq_self (fun z => newtonKernel d nu (y - x - z) * chi z *
    midPair F ((1 / 2 : ℝ) • (x + y)) z) volume]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  beta_reduce
  have e1 : y - x - -z = -(x - y - z) := by abel
  rw [e1, hK, hchi.2.1]
  unfold midPair
  rw [hF (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • -z)]
  congr 3 <;> module

theorem r26t8a_U2_center_symm (mu : Measure (Euc d)) {k : Euc d → Euc d → ℝ} (hk : ∀ x y, k x y = k y x)
    (x y : Euc d) : r2CenterKernel mu k x y = r2CenterKernel mu k y x := by
  unfold r2CenterKernel
  have e1 : (fun y' => k x y') = fun x' => k x' x := funext fun y' => hk x y'
  have e2 : (fun x' => k x' y) = fun y' => k y y' := funext fun x' => hk x' y
  rw [hk x y, e1, e2]
  ring

theorem r26t8a_U2_pairA_symm (C : WholeCoeff d) (mu : Measure (Euc d)) {G : Euc d → Euc d → ℝ}
    (hG : ∀ x y, G x y = G y x) (x y : Euc d) : pairA C mu G x y = pairA C mu G y x := by
  unfold pairA
  have e1 : (fun x' => G x' y) = G y := funext fun x' => hG x' y
  have e2 : (fun x' => G x' x) = G x := funext fun x' => hG x' x
  rw [e1, e2]
  ring

theorem r26t8a_U2_newtonDefect_symm (C : WholeCoeff d) (mu : Measure (Euc d)) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) {F : Euc d → Euc d → ℝ} (hF : ∀ x y, F x y = F y x) (x y : Euc d) :
    newtonDefect C mu chi F x y = newtonDefect C mu chi F y x := by
  have hL : ∀ x y, localNewton mu C.ν chi F x y = localNewton mu C.ν chi F y x := fun x y =>
    r26t8a_U2_center_symm mu (fun x y => r26t8a_U2_rawNewton_symm C.ν hchi hF x y) x y
  unfold newtonDefect
  rw [hF x y, r26t8a_U2_pairA_symm C mu hL x y]

theorem r26t8a_U2_term_symm (C : WholeCoeff d) (mu : Measure (Euc d)) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) (f : Euc d → ℝ) (h0 : ∀ x y, HSource mu f x y = HSource mu f y x) (j : ℕ)
    (x y : Euc d) : r26t8a_parametrixTerm C mu chi f j x y = r26t8a_parametrixTerm C mu chi f j y x := by
  induction j generalizing x y with
  | zero => exact h0 x y
  | succ j ih =>
    have e : r26t8a_parametrixTerm C mu chi f (j + 1) = newtonDefect C mu chi (r26t8a_parametrixTerm C mu chi f j) :=
      Function.iterate_succ_apply' _ _ _
    rw [e]
    exact r26t8a_U2_newtonDefect_symm C mu hchi ih x y

theorem r26t8a_U2_parametrix_symm (C : WholeCoeff d) (mu : Measure (Euc d)) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) (f : Euc d → ℝ) (h0 : ∀ x y, HSource mu f x y = HSource mu f y x)
    (x y : Euc d) : r26t8a_parametrix C mu chi f x y = r26t8a_parametrix C mu chi f y x := by
  unfold r26t8a_parametrix
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact r26t8a_U2_center_symm mu (fun x y => r26t8a_U2_rawNewton_symm C.ν hchi (r26t8a_U2_term_symm C mu hchi f h0 j) x y) x y

end HRS.MS.R26T8A
