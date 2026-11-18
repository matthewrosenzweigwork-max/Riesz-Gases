import HRS.MS.Fp81S21WindowSup8

/-!
# HRS S2.1(iii), SOL40 packet 9d: joint measurability of the orbit derivative

`S101Data` defines `s101Dt` as `derivWithin` on `[b,T]` and `s101Th` as
the same derivative on `b < s ≤ T`, zero outside. The existing
`s101_th_aesm` is only an almost-everywhere-in-time statement. The lemma here
uses the exact interior derivative formula and patches the single terminal
endpoint, then applies the measurable-continuous (Carathéodory) criterion.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open HRS.Whole HRS.MS.CovMeas HRS.MS.Go

namespace HRS.Fp81.S21

/-- Joint measurability of the endpoint-cutoff time derivative and spatial
argument on `[b,T] × Euc d`, from `S101Data`. -/
theorem fp81s21_s101Th_joint_measurable
    {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hD : S101Data C m T r c)
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) T) (α : MultiIndex d) :
    Measurable (fun z : ℝ × Euc d => s101Th C m T b z.1 α z.2) := by
  have htime (x : Euc d) : Measurable (fun s : ℝ => s101Th C m T b s α x) := by
    let f : ℝ → ℝ := fun t' => propagatorW C b t' (oscTestFun m α) x
    let q : ℝ → ℝ := fun s => if b < s ∧ s < T then derivWithin f (Ici s) s else 0
    have hq : Measurable q := by
      dsimp [q]
      exact Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio)
        (measurable_derivWithin_Ici f) measurable_const
    let q' : ℝ → ℝ := fun s => if s = T then s101Th C m T b T α x else q s
    have hq' : Measurable q' :=
      Measurable.ite (measurableSet_singleton T) (measurable_const) hq
    have heq : q' = fun s => s101Th C m T b s α x := by
      funext s
      by_cases hsT : s = T
      · simp [q', hsT]
      · by_cases hs : b < s ∧ s < T
        · have hsIcc : s ∈ Ioo b T := hs
          have hsData : s ∈ Icc b T := ⟨hs.1.le, hs.2.le⟩
          have hder := s101_derivWithin_Icc_eq hsIcc (hD.diffT α b hb x s hsData)
          simp only [q', hsT, if_false, q, hs.1, hs.2, and_self, if_true,
            s101Th, hs.1, hs.2.le, and_self, if_true]
          exact hder.symm
        · have hcut : ¬ (b < s ∧ s ≤ T) := by
            rintro ⟨hbs, hsTle⟩
            exact hs ⟨hbs, lt_of_le_of_ne hsTle hsT⟩
          simp [q', hsT, q, hs, s101Th, hcut]
    rw [← heq]
    exact hq'
  have hcont (s : ℝ) : Continuous (fun x : Euc d => s101Th C m T b s α x) := by
    by_cases hs : b < s ∧ s ≤ T
    · have hsData : s ∈ Icc b T := ⟨hs.1.le, hs.2⟩
      simpa [s101Th, hs] using (hD.smoothD α b hb s hsData).continuous
    · simpa [s101Th, hs] using (continuous_const : Continuous fun _ : Euc d => (0 : ℝ))
  have hjoint : Measurable
      (Function.uncurry (fun x : Euc d => fun s : ℝ => s101Th C m T b s α x)) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun x : Euc d => fun s : ℝ => s101Th C m T b s α x)
      (fun s => hcont s) (fun x => htime x)
  change Measurable (fun z : ℝ × Euc d =>
    (fun p : Euc d × ℝ => s101Th C m T b p.2 α p.1) (Prod.swap z))
  exact hjoint.comp measurable_swap

#print axioms fp81s21_s101Th_joint_measurable

end HRS.Fp81.S21

end
