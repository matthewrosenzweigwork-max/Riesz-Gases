import HRS.MS.R26T8AO04a

/-!
# S8.2 T8A O04 (part b): measurability of the zero-extended noise profile
`G b r x i` is the noise integrand as a function of the state; it is Borel measurable in `(b, r, x)` (continuous off
the collision set and for nonnegative ages by O03b, zero elsewhere), and `X` is jointly measurable in `(t, ω)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

open Classical in
/-- the noise integrand as a function of the state -/
def r26t8a_o04_G (d N : ℕ) (a beta m : ℝ) (rho : Euc d → ℝ) (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (alpha : MultiIndex d) (j : ℕ) (b r : ℝ) (x : EucConfig d N) (i : Fin N × Fin d) : ℝ :=
  if 0 ≤ r ∧ r ≤ b ∧ x ∉ eucCollisionSet d N then
    Real.sqrt (2 / beta) * Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha j (b - r)) x i.1 i.2
  else 0

theorem r26t8a_o04_noiseAge_eq {Omega : Type*} (a beta m : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (alpha : MultiIndex d) (X : ℝ≥0 → Omega → EucConfig d N)
    (j : ℕ) (b r : ℝ) (w : Omega) :
    r26t8a_noiseAge a beta m rho Psi alpha X j b r w =
      r26t8a_o04_G d N a beta m rho Psi alpha j b r (X r.toNNReal w) := rfl

theorem r26t8a_o04_X_meas {Omega : Type*} [mOmega : MeasurableSpace Omega] {F : Filtration ℝ mOmega}
    {X : ℝ≥0 → Omega → EucConfig d N} (hp : IsProgressive F (ofNNRealTime X)) :
    Measurable (fun p : ℝ × Omega => X p.1.toNNReal p.2) := by
  have hclamp : ∀ n : ℕ, Measurable (fun p : ℝ × Omega => ofNNRealTime X (min p.1 (n : ℝ)) p.2) :=
    fun n => HRS.measurable_clamp hp (n : ℝ)
  have hcomb : Measurable (fun q : ℕ × (ℝ × Omega) => ofNNRealTime X (min q.2.1 (q.1 : ℝ)) q.2.2) :=
    measurable_from_prod_countable_right (fun n => hclamp n)
  have hceil : Measurable (fun p : ℝ × Omega => (⌈p.1⌉₊, p)) :=
    ((Nat.measurable_ceil.comp measurable_fst)).prodMk measurable_id
  have heq : (fun p : ℝ × Omega => X p.1.toNNReal p.2) =
      (fun q : ℕ × (ℝ × Omega) => ofNNRealTime X (min q.2.1 (q.1 : ℝ)) q.2.2) ∘
        (fun p : ℝ × Omega => (⌈p.1⌉₊, p)) := by
    funext p
    simp only [Function.comp, ofNNRealTime]
    rw [min_eq_left (Nat.le_ceil p.1)]
  rw [heq]
  exact hcomb.comp hceil

end HRS.MS.R26T8A

end
