import HRS.MS.SA12AssemblyDefs
import HRS.MS.SA12AssemblyP1
import HRS.MS.SA12LimitL6
import HRS.MS.SA12LimitL9
import HRS.MS.SA12LimitL10
import HRS.MS.SA12LimitL15
import HRS.MS.SA12LimitL16

/-!
# S.A.12 P3: the limit of an approximation sequence is a uloc solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Limit

/-- The limit data of an approximation sequence: one subsequence and its limit. -/
theorem sa12y_limit_data (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s<d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ulocNormE m χ φ<⊤)
    (profile : ℝ → ℝ) (a : ApproximationSequence χ m (D.coeff μ) t φ profile) :
    ∃ (n : ℕ → ℕ) (G : ℝ → Euc d → ℝ), StrictMono n ∧ IsUlocSolutionRd χ m (D.coeff μ) t φ G ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal (profile τ)) ∧
      (∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
        Tendsto (fun k => ∫ x, a.F (n k) τ x*ψ x) atTop (𝓝 (∫ x, G τ x*ψ x))) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ R : ℝ, 0<R → MemLp (G τ) 2 (volume.restrict (Metric.ball 0 R))) := by
  have hF0 : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (a.F n τ) ≤ ENNReal.ofReal a.B := by
    intro n τ hτ
    exact (HRS.MS.SA12BD.sa12_uloc_mono d m 0 (Nat.zero_le m) χ (a.F n τ)).trans
      ((a.bound n τ hτ).trans (ENNReal.ofReal_le_ofReal (a.profile_bound τ hτ)))
  obtain ⟨n,G,hn,hG0,huniform⟩ := uloc_weak_compact hd χ hχ a.B t a.nonneg_B ht.1 a.F hF0 a.equi
  have hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      Tendsto (fun k => ∫ x, a.F (n k) τ x*ψ x) atTop (𝓝 (∫ x, G τ x*ψ x)) := by
    intro ψ hψ τ hτ
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    filter_upwards [huniform ψ hψ (ε/2) (half_pos hε)] with k hk
    simpa only [Real.dist_eq] using lt_of_le_of_lt (hk τ hτ) (half_lt_self hε)
  have hGloc : ∀ τ ∈ Icc (0 : ℝ) t, ∀ R : ℝ, 0<R →
      MemLp (G τ) 2 (volume.restrict (Metric.ball 0 R)) := by
    intro τ hτ
    exact (uloc_local_l2 hd χ hχ 0 (G τ)
      (lt_of_le_of_lt (hG0 τ hτ).2 ENNReal.ofReal_lt_top)).2
  have hweak : IsWeakSol (weakOp (D.coeff μ) t) t φ G := by
    apply weak_limit_passage hd χ hχ a.B t ht.1
      (weakOp (D.coeff μ) t) (fun k => a.A (n k)) (fun k => a.F (n k))
      (fun k => a.datum (n k)) G φ
    · intro ψ hψ σ hσ
      exact ⟨(a.operator_measurable ψ hψ σ hσ).1,
        fun k => (a.operator_measurable ψ hψ σ hσ).2 (n k)⟩
    · exact (uloc_local_l2 hd χ hχ m φ hφ).2
    · intro k
      exact a.weak (n k)
    · intro k τ hτ
      exact hF0 (n k) τ hτ
    · intro τ hτ
      exact (hG0 τ hτ).2
    · exact hconv
    · intro ψ hψ
      exact (a.initial_converges ψ hψ).comp hn.tendsto_atTop
    · intro ψ hψ δ hδ
      exact hn.tendsto_atTop.eventually (a.operator_converges ψ hψ δ hδ)
    · exact a.operator_bound
  have hforward := weak_components hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
    φ G a.B (fun τ hτ => (hG0 τ hτ).2) hweak
  have hbound : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal (profile τ) := by
    intro τ hτ
    exact (local_norm_lower_semicontinuity hd m χ hχ (profile τ)
      (fun k => a.F (n k) τ) (G τ) (hGloc τ hτ)
      (fun ψ hψ => hconv ψ hψ τ hτ) (fun k => a.bound (n k) τ hτ)).1
  have hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal a.B :=
    fun τ hτ => (hbound τ hτ).trans (ENNReal.ofReal_le_ofReal (a.profile_bound τ hτ))
  exact ⟨n, G, hn, ⟨hforward, ⟨a.B, hB⟩, real_order_continuity hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
    φ G hforward a.B hB⟩, hbound, hconv, hGloc⟩

-- BEGIN SA12.P3
/-- Written limit assembly, with the exact local-L2 and measurability
premises visible at each call. -/
theorem limit_from_sequence (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s<d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ulocNormE m χ φ<⊤)
    (profile : ℝ → ℝ) (a : ApproximationSequence χ m (D.coeff μ) t φ profile) :
    ∃ G : ℝ → Euc d → ℝ, IsUlocSolutionRd χ m (D.coeff μ) t φ G ∧
      ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal (profile τ) := by
  obtain ⟨n, G, -, hG, hbound, -, -⟩ := sa12y_limit_data d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD
    t ht φ hφ profile a
  exact ⟨G, hG, hbound⟩
-- END SA12.P3

end HRS.MH.AdjointRd.Phase2SA12Assembly
