import HRS.MS.Fp81S21PredMap6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas
  HRS.MS.ProClosureS111

/-- The encoded adjoint orbit of an oscillator test is continuous in its
source time in the weighted chart norm. -/
theorem fp81s21_chartOrbit_source_cont
    {d r : ℕ} {Pw m T : ℝ} {C : WholeCoeff d} {c : MultiIndex d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (E : r26t6_WeightedChart d r Pw) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) T) (α : MultiIndex d) :
    ContinuousOn (fun u => E.encode (propagatorW C u q (oscTestFun m α)))
      (Icc 0 q) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (continuous_iff_seqContinuous).2 ?_
  intro us u hus
  let F₀ : Euc d → ℝ := propagatorW C (u : ℝ) q (oscTestFun m α)
  let Fₙ : ℕ → Euc d → ℝ := fun n => propagatorW C (us n : ℝ) q (oscTestFun m α)
  have hreg : ∀ v ∈ Icc (0 : ℝ) q,
      ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C v q (oscTestFun m α)) := by
    intro v hv
    have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hq.2⟩
    have hqv : q ∈ Icc v T := ⟨hv.2, hq.2⟩
    exact hD.smoothU α v hvT q hqv
  have hbound : ∀ v ∈ Icc (0 : ℝ) q, ∀ j ≤ r + 1, ∀ x,
      ‖iteratedFDeriv ℝ j (propagatorW C v q (oscTestFun m α)) x‖ ≤ c α := by
    intro v hv j hj x
    have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hq.2⟩
    have hqv : q ∈ Icc v T := ⟨hv.2, hq.2⟩
    exact hD.bddU α v hvT q hqv j hj x
  have huT : (u : ℝ) ∈ Icc (0 : ℝ) T := ⟨u.2.1, u.2.2.trans hq.2⟩
  have hqu : q ∈ Icc (u : ℝ) T := ⟨u.2.2, hq.2⟩
  have hbase := s102_orbit_test (r := r) (Pw := Pw) hP hD huT hqu α
  have hseq : ∀ n, IsR2WeightedTest r Pw (Fₙ n) := by
    intro n
    have hnT : (us n : ℝ) ∈ Icc (0 : ℝ) T := ⟨(us n).2.1, (us n).2.2.trans hq.2⟩
    have hqn : q ∈ Icc (us n : ℝ) T := ⟨(us n).2.2, hq.2⟩
    exact (s102_orbit_test (r := r) (Pw := Pw) hP hD hnT hqn α).1
  let G₀ : weightedTestSubmodule d r Pw := ⟨F₀, weightedTestSubmodule_iff.2 hbase.1⟩
  let Gₙ : ℕ → weightedTestSubmodule d r Pw := fun n =>
    ⟨Fₙ n, weightedTestSubmodule_iff.2 (hseq n)⟩
  have hdiff : ∀ n, IsR2WeightedTest r Pw (fun x => F₀ x - Fₙ n x) := by
    intro n
    exact weightedTestSubmodule_iff.1 (G₀ - Gₙ n).property
  have hencode : ∀ n,
      E.encode (fun x => F₀ x - Fₙ n x) = E.encode F₀ - E.encode (Fₙ n) := by
    intro n
    have hneg : IsR2WeightedTest r Pw ((-1 : ℝ) • Fₙ n) :=
      weightedTestSubmodule_iff.1 ((-1 : ℝ) • Gₙ n).property
    calc
      E.encode (fun x => F₀ x - Fₙ n x) = E.encode (F₀ + (-1 : ℝ) • Fₙ n) := by
        congr 1
        funext x
        simp [sub_eq_add_neg]
      _ = E.encode F₀ + E.encode ((-1 : ℝ) • Fₙ n) := E.add _ _ hbase.1 hneg
      _ = E.encode F₀ - E.encode (Fₙ n) := by
        rw [E.smul (-1) (Fₙ n) (hseq n)]
        simp [sub_eq_add_neg]
  have hnorm : ∀ n,
      ‖E.encode (Fₙ n) - E.encode F₀‖ =
        (weightedSobolevE r Pw (fun x => F₀ x - Fₙ n x)).toReal := by
    intro n
    calc
      ‖E.encode (Fₙ n) - E.encode F₀‖ =
          ‖E.encode F₀ - E.encode (Fₙ n)‖ := by rw [norm_sub_rev]
      _ = ‖E.encode (fun x => F₀ x - Fₙ n x)‖ := by rw [hencode n]
      _ = _ := E.norm _ (hdiff n)
  have hsource := fp81s21_prop_source_norm_tendsto
    (r := r) (Pw := Pw) (q := q) (C := C)
    hP (hD.nonneg α) hreg hbound us u hus
  have henc : Tendsto (fun n => E.encode (Fₙ n)) atTop (𝓝 (E.encode F₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hsource.congr fun n => (hnorm n).symm
  simpa [Function.comp_def, F₀, Fₙ] using henc

#print axioms HRS.Fp81.S21.fp81s21_chartOrbit_source_cont

end HRS.Fp81.S21
