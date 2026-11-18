import HRS.MS.R2InterpAux128

/-!
# S10.2 (worker S10S), part 129 (packet M3d): continuity of the slice `u ↦ V^{q,u} z^u` in `B_m`, and joint continuity of `(u,t) ↦ V^{t,u} z^u`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_V_slice_cont (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    {zf : ℝ → (Euc d → ℝ) → ℝ} (hZ : ∀ u ∈ Icc (0 : ℝ) T, S102Z r Pw (zf u)) {M : ℝ}
    (hM : ∀ u ∈ Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      |zf u f| ≤ M * (weightedSobolevE r Pw f).toReal)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) T)
    (hc : ∀ α : MultiIndex d, ContinuousOn (fun u => zf u (propagatorW C u q (oscTestFun m α))) (Icc 0 q)) :
    ContinuousOn (fun u => r2Vprop C m q u (zf u)) (Icc 0 q) := by
  have hmem : ∀ u : ℝ, Memℓp (fun α => OscDual.coord (r2Vprop C m q u (zf u)) α) 2 := fun u =>
    (show lp (fun _ : MultiIndex d => ℝ) 2 from r2Vprop C m q u (zf u)).2
  have hcoord : ∀ u ∈ Icc (0 : ℝ) q, ∀ α, OscDual.coord (r2Vprop C m q u (zf u)) α =
      zf u (propagatorW C u q (oscTestFun m α)) := fun u hu α =>
    s102_Vprop_coord hP hD (hZ u ⟨hu.1, hu.2.trans hq.2⟩) hlin ⟨hu.1, hu.2.trans hq.2⟩ ⟨hu.2, hq.2⟩ α
  have hb : Summable fun α => (|M| * (s57pC d r Pw * c α)) ^ 2 :=
    (hD.summable.mul_left ((|M| * s57pC d r Pw) ^ 2)).congr (fun α => by ring)
  have := s102_lp_continuousOn (m := m) (S := Icc 0 q) (fun u α => OscDual.coord (r2Vprop C m q u (zf u)) α) hmem
    (fun α => |M| * (s57pC d r Pw * c α)) hb
    (fun u hu α => by
      rw [hcoord u hu α]
      exact s102_z_orbit_bound hP hD (hZ u ⟨hu.1, hu.2.trans hq.2⟩) (hM u ⟨hu.1, hu.2.trans hq.2⟩)
        ⟨hu.1, hu.2.trans hq.2⟩ ⟨hu.2, hq.2⟩ α)
    (fun α => (hc α).congr fun u hu => hcoord u hu α)
  exact this

/-- The set of grid times: rational times in `[0,T]` and `T`. -/
def s102_Qset (T : ℝ) : Set ℝ := {x : ℝ | x ∈ Icc (0 : ℝ) T ∧ ∃ r : ℚ, (r : ℝ) = x} ∪ {T}

theorem s102_Qset_countable (T : ℝ) : (s102_Qset T).Countable := by
  refine (((Set.countable_range ((↑) : ℚ → ℝ)).union (Set.countable_singleton T))).mono ?_
  rintro x (⟨-, r, rfl⟩ | rfl)
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr rfl

theorem s102_Qset_sub {T : ℝ} (hT : 0 ≤ T) : s102_Qset T ⊆ Icc (0 : ℝ) T := by
  rintro x (⟨hx, -⟩ | rfl)
  · exact hx
  · exact ⟨hT, le_rfl⟩

end HRS.MS.R2Interp

end
