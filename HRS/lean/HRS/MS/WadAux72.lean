import HRS.MS.WadAux71

/-!
# S8.3, packet S8E-1, part 1: mild solutions with an abstract source

`S8eSol q a ν t M Φ w`: the data of `S84Sol` with the source `s ↦ 𝓑 w_s` replaced by an arbitrary jointly continuous
source `q` of polynomial growth (the hypothesis on the weighted size of `q_s` is supplied separately, in terms of an
admissible constant of `w`).  This is the structure of the difference quotients of a classical solution.
`s8e_P_shift`: `P_τ g (x + z) = P_τ (g(· + e^{-aτ} z)) x` (the Mehler semigroup is covariant under the flow of
the drift), `s8e_P_sub`: additivity of `P_τ` on continuous weighted functions.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

structure S8eSol (q : ℝ → Euc d → ℝ) (a ν t M Φ : ℝ) (w : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (w r)
  hqc : ContinuousOn (fun p : ℝ × Euc d => q p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ)
  hqb : ∃ (K : ℝ) (p : ℕ), ∀ s ∈ Set.Icc 0 t, ∀ y, |q s y| ≤ K * (1 + ‖y‖) ^ p
  mild : ∀ r ∈ Set.Icc 0 t, ∀ x, w r x =
    s83_P a ν (t - r) (w t) x + ∫ s in r..t, s83_P a ν (s - r) (q s) x
  term_cont : Continuous (w t)
  term_wt : Wt M Φ (w t)
  bdd : ∃ B1 B2 : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (w r) y‖ ≤ B1 ∧
    ‖fderiv ℝ (fderiv ℝ (w r)) y‖ ≤ B2

theorem s8e_hint {q : ℝ → Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (sol : S8eSol q a ν t M Φ w) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (y : Euc d) :
    IntervalIntegrable (fun s => s83_P a ν (s - r) (q s) y) volume r t := by
  obtain ⟨K, p, hb⟩ := sol.hqb
  have := s83_cont_param (Φ := fun s y => q s y) hr.1 hr.2 sol.hqc hb ha hν.le y
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hr.2]
  exact this

theorem s8e_qcont {q : ℝ → Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (sol : S8eSol q a ν t M Φ w)
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) : Continuous (fun y : Euc d => q s y) := by
  have h1 := continuousOn_iff_continuous_restrict.1 sol.hqc
  have h2 : Continuous (fun y : Euc d => (⟨(s, y), ⟨hs, Set.mem_univ y⟩⟩ :
      (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))))) :=
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) _
  have h3 := h1.comp h2
  simpa [Function.comp_def, Set.restrict] using h3

/-- Covariance of the Mehler semigroup under the flow of the drift. -/
theorem s8e_P_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a ν τ : ℝ) (g : Euc d → E)
    (x z : Euc d) :
    s83_P a ν τ g (x + z) = s83_P a ν τ (fun y => g (y + Real.exp (-a * τ) • z)) x := by
  unfold s83_P s83_G s83_mc
  congr 1
  funext u
  congr 1
  rw [smul_add, add_assoc, add_comm (Real.exp (-a * τ) • z), ← add_assoc]

theorem s8e_P_sub {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) {M C C' : ℝ} (hM : 0 ≤ M)
    (hwf : Wt M C f) (hwg : Wt M C' g) {a ν τ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (x : Euc d) :
    s83_P a ν τ (fun y => f y - g y) x = s83_P a ν τ f x - s83_P a ν τ g x := by
  have hg' : Wt M C' ((-1 : ℝ) • g) := fun y => by
    simpa [norm_smul] using hwg y
  have h := congrFun (s83_G_add (c := s83_mc a τ) (σ := s83_ms a ν τ) hf (hg.const_smul (-1 : ℝ)) hM hwf hg'
    (s83_abs_ms_le ha hν hτ)) x
  have h2 := congrFun (s83_G_smul (d := d) (s83_mc a τ) (s83_ms a ν τ) (-1 : ℝ) g) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h h2
  unfold s83_P
  have e : (fun y => f y - g y) = f + (-1 : ℝ) • g := by funext y; simp [sub_eq_add_neg]
  rw [e, h, h2]; ring

end HRS.MS.Wad
