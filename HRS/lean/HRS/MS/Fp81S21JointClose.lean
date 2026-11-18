import HRS.MS.Fp81S21JointAvg

/-! The numerical infimum profile used to close uniform joint estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- The profile obtained by infimizing a numerical bound over the three
approximation choices. The third index can encode the cutoff `r + 1`. -/
def fp81s21_jointClose_profile
    (b : ℕ → ℕ → ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨅ i : ℕ × (ℕ × ℕ), b i.1 i.2.1 i.2.2 N

/-- If every fixed approximation triple eventually gives an arbitrarily small
bound for some triple chosen before `N`, the infimum profile is nonnegative
and tends to zero. This is the sequential choice step used after fixing `m`,
then `k`, then the cutoff index. -/
theorem fp81s21_jointClose_profile_spec
    (b : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hb : ∀ m k r N, 0 ≤ b m k r N)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ m k r, ∀ᶠ N : ℕ in atTop, b m k r N < ε) :
    (∀ N, 0 ≤ fp81s21_jointClose_profile b N) ∧
      Tendsto (fp81s21_jointClose_profile b) atTop (𝓝 0) := by
  have hnonneg : ∀ N, 0 ≤ fp81s21_jointClose_profile b N := by
    intro N
    change 0 ≤ ⨅ i : ℕ × (ℕ × ℕ), b i.1 i.2.1 i.2.2 N
    apply le_ciInf
    intro i
    exact hb i.1 i.2.1 i.2.2 N
  have hbelow (N : ℕ) :
      BddBelow (Set.range (fun i : ℕ × (ℕ × ℕ) => b i.1 i.2.1 i.2.2 N)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨i, rfl⟩
    exact hb i.1 i.2.1 i.2.2 N
  refine ⟨hnonneg, ?_⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [] with N
    exact lt_of_lt_of_le ha (hnonneg N)
  · intro ε hε
    obtain ⟨m, k, r, hN⟩ := hsmall ε hε
    filter_upwards [hN] with N hN
    calc
      fp81s21_jointClose_profile b N ≤ b m k r N :=
        ciInf_le (hbelow N) (m, (k, r))
      _ < ε := hN

/-- A uniform `ofReal` estimate at every approximation triple descends to the
same infimum profile. -/
theorem fp81s21_jointClose_inf_bound
    (w : ℝ≥0∞) (b : ℕ → ℕ → ℕ → ℕ → ℝ) (N : ℕ)
    (hbelow : BddBelow
      (Set.range (fun i : ℕ × (ℕ × ℕ) => b i.1 i.2.1 i.2.2 N)))
    (hbound : ∀ m k r, w ≤ ENNReal.ofReal (b m k r N)) :
    w ≤ ENNReal.ofReal (fp81s21_jointClose_profile b N) := by
  calc
    w ≤ ⨅ i : ℕ × (ℕ × ℕ), ENNReal.ofReal (b i.1 i.2.1 i.2.2 N) := by
      apply le_iInf
      intro i
      exact hbound i.1 i.2.1 i.2.2
    _ = ENNReal.ofReal (fp81s21_jointClose_profile b N) := by
      exact (ENNReal.ofReal_iInf
        (fun i : ℕ × (ℕ × ℕ) => b i.1 i.2.1 i.2.2 N)).symm

#print axioms fp81s21_jointClose_profile_spec
#print axioms fp81s21_jointClose_inf_bound

end HRS.Fp81.S21
