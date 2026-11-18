import HRS.MS.SA12AssemblyP3
import HRS.MS.SA12CompB2
import HRS.MS.AdjRdUniqueness
import HRS.MS.SA12LimitL15

/-!
# S.A.12 S7: the paired limit bounds
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Companions

variable {d : ℕ}

/-- A subsequence of an approximation sequence is an approximation sequence. -/
def ApproximationSequence.subseq {m : ℕ} {χ : Euc d → ℝ} {coeff : WholeCoeff d} {t : ℝ}
    {φ : Euc d → ℝ} {profile : ℝ → ℝ} (a : ApproximationSequence χ m coeff t φ profile)
    (n : ℕ → ℕ) (hn : StrictMono n) : ApproximationSequence χ m coeff t φ profile where
  F := fun k => a.F (n k)
  datum := fun k => a.datum (n k)
  A := fun k => a.A (n k)
  B := a.B
  nonneg_B := a.nonneg_B
  profile_bound := a.profile_bound
  bound := fun k => a.bound (n k)
  weak := fun k => a.weak (n k)
  equi := fun ψ hψ => by
    obtain ⟨K, hK⟩ := a.equi ψ hψ
    exact ⟨K, fun k => hK (n k)⟩
  initial_converges := fun ψ hψ => (a.initial_converges ψ hψ).comp hn.tendsto_atTop
  operator_measurable := fun ψ hψ σ hσ =>
    ⟨(a.operator_measurable ψ hψ σ hσ).1, fun k => (a.operator_measurable ψ hψ σ hσ).2 (n k)⟩
  operator_converges := fun ψ hψ δ hδ => hn.tendsto_atTop.eventually (a.operator_converges ψ hψ δ hδ)
  operator_bound := a.operator_bound

/-- A difference of two functions with finite uloc norms has finite uloc norm. -/
theorem sa12y_uloc_sub_le (m : ℕ) (χ : Euc d → ℝ) {f g : Euc d → ℝ} {b1 b2 : ℝ}
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hf : ulocNormE m χ f ≤ ENNReal.ofReal b1) (hg : ulocNormE m χ g ≤ ENNReal.ofReal b2) :
    ulocNormE m χ (fun x => f x - g x) ≤ ENNReal.ofReal (2 * (b1 + b2)) := by
  unfold ulocNormE at hf hg ⊢
  refine iSup_le fun z => ?_
  have h1 : sobolevNormE (m : ℝ) (fun x => χ (x - z) * f x) ≤ ENNReal.ofReal b1 :=
    (le_iSup (fun w : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - w) * f x) z).trans hf
  have h2 : sobolevNormE (m : ℝ) (fun x => χ (x - z) * g x) ≤ ENNReal.ofReal b2 :=
    (le_iSup (fun w : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - w) * g x) z).trans hg
  obtain ⟨m1, s1⟩ := sa12x_sobE_le hb1 h1
  obtain ⟨m2, s2⟩ := sa12x_sobE_le hb2 h2
  obtain ⟨hmem, hS⟩ := sa12l12_sq_split (m : ℝ) m1 m2 (t := 1) one_pos
  have e : (fun x => χ (x - z) * f x - χ (x - z) * g x) =
      fun x => χ (x - z) * (f x - g x) := funext fun x => by ring
  rw [e] at hmem hS
  refine sa12x_sobE_of_le (by positivity) hmem (hS.trans ?_)
  norm_num
  nlinarith [s1, s2, sq_nonneg (b1 - b2), mul_nonneg hb1 hb2]

end HRS.MH.AdjointRd.Phase2SA12Assembly

namespace HRS.MH.AdjointRd.Phase2SA12Stability

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Assembly HRS.MH.AdjointRd.Phase2SA12Limit
open HRS.MH.AdjointRd.Phase2SA12Companions

variable {d : ℕ}

-- BEGIN SA12.S7
theorem paired_limit_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D₁ D₂ : WholeDyn d)
    (ν₀ : ℝ) (μ₁ μ₂ : ℝ → Euc d → ℝ)
    (hD₁ : AdjointRdData s (m+2) MB Λ ΛV G₀ νbar D₁ T μ₁)
    (hD₂ : AdjointRdData s (m+2) MB Λ ΛV G₀ νbar D₂ T μ₂)
    (hR₁ : RdRegimeHolds Rg d s D₁.M D₁.invβ ν₀)
    (hR₂ : RdRegimeHolds Rg d s D₂.M D₂.invβ ν₀)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ulocNormE (m+2) χ φ < ⊤)
    (profile₁ profile₂ : ℝ → ℝ)
    (a₁ : ApproximationSequence (d := d) χ (m+2) (D₁.coeff μ₁) t φ profile₁)
    (a₂ : ApproximationSequence (d := d) χ (m+2) (D₂.coeff μ₂) t φ profile₂)
    (U W : ℝ → ℝ≥0∞)
    (hbound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t,
      ulocNormE m χ (fun x => a₁.F n τ x - a₂.F n τ x) ≤ U τ ∧
      varpiNormE m χ (fun x => a₁.F n τ x - a₂.F n τ x) ≤ W τ)
    (F₁ F₂ : ℝ → Euc d → ℝ)
    (hF₁ : IsUlocSolutionRd χ (m+2) (D₁.coeff μ₁) t φ F₁)
    (hF₂ : IsUlocSolutionRd χ (m+2) (D₂.coeff μ₂) t φ F₂) :
    ∀ τ ∈ Icc (0 : ℝ) t,
      ulocNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤ U τ ∧
      varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤ W τ := by
  intro τ hτ
  have hm2 : 1 ≤ m + 2 := by omega
  obtain ⟨n₁, G₁, hn₁, hG₁, -, hc₁, hl₁⟩ :=
    sa12y_limit_data d hd s hs0 hsd (m+2) hm2 MB Λ ΛV G₀ νbar T χ hχ D₁ μ₁ hD₁ t ht φ hφ profile₁ a₁
  obtain ⟨n₂, G₂, hn₂, hG₂, -, hc₂, hl₂⟩ :=
    sa12y_limit_data d hd s hs0 hsd (m+2) hm2 MB Λ ΛV G₀ νbar T χ hχ D₂ μ₂ hD₂ t ht φ hφ profile₂
      (a₂.subseq n₁ hn₁)
  have hn₂' : Tendsto n₂ atTop atTop := hn₂.tendsto_atTop
  have hGF₁ := HRS.MS.SA12BD.sa12_uniqueness d hd s hs0 hsd (m+2) hm2 Rg MB Λ ΛV G₀ νbar T χ hχ D₁ ν₀ μ₁
    hD₁ hR₁ t ht φ G₁ F₁ hG₁ hF₁
  have hGF₂ := HRS.MS.SA12BD.sa12_uniqueness d hd s hs0 hsd (m+2) hm2 Rg MB Λ ΛV G₀ νbar T χ hχ D₂ ν₀ μ₂
    hD₂ hR₂ t ht φ G₂ F₂ hG₂ hF₂
  have hae : (fun x => F₁ τ x - F₂ τ x) =ᵐ[volume] (fun x => G₁ τ x - G₂ τ x) := by
    filter_upwards [hGF₁ τ hτ, hGF₂ τ hτ] with x h1 h2
    rw [h1, h2]
  have hn := norm_congr_ae m χ _ _ hae
  rw [hn.1, hn.2.1]
  set N : ℕ → ℕ := fun k => n₁ (n₂ k) with hNdef
  set un : ℕ → Euc d → ℝ := fun k x => a₁.F (N k) τ x - a₂.F (N k) τ x with hun
  set u : Euc d → ℝ := fun x => G₁ τ x - G₂ τ x with hu
  have hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball 0 R)) := fun R hR =>
    (hl₁ τ hτ R hR).sub (hl₂ τ hτ R hR)
  have hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun k => ∫ x, un k x * ψ x) atTop (𝓝 (∫ x, u x * ψ x)) := by
    intro ψ hψ
    have h1 := (hc₁ ψ hψ τ hτ).comp hn₂'
    have h2 := hc₂ ψ hψ τ hτ
    have e1 : ∀ k, ∫ x, un k x * ψ x = (∫ x, a₁.F (N k) τ x * ψ x) - ∫ x, a₂.F (N k) τ x * ψ x := by
      intro k
      rw [← integral_sub ((a₁.weak (N k)).integrable_x ψ hψ τ hτ).1
        ((a₂.weak (N k)).integrable_x ψ hψ τ hτ).1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hun]; ring
    have e2 : ∫ x, u x * ψ x = (∫ x, G₁ τ x * ψ x) - ∫ x, G₂ τ x * ψ x := by
      rw [← integral_sub (hG₁.sol.integrable_x ψ hψ τ hτ).1 (hG₂.sol.integrable_x ψ hψ τ hτ).1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hu]; ring
    simp_rw [e1, e2]
    exact h1.sub h2
  refine ⟨?_, ?_⟩
  · by_cases hU : U τ = ⊤
    · rw [hU]; exact le_top
    · have := (local_norm_lower_semicontinuity hd m χ hχ (U τ).toReal un u hloc hconv
        (fun k => by rw [ENNReal.ofReal_toReal hU]; exact (hbound (N k) τ hτ).1)).1
      rwa [ENNReal.ofReal_toReal hU] at this
  · set b1 : ℝ := max (profile₁ τ) 0 with hb1
    set b2 : ℝ := max (profile₂ τ) 0 with hb2
    have hB : ∀ k, ulocNormE m χ (un k) ≤ ENNReal.ofReal (2 * (b1 + b2)) := by
      intro k
      refine sa12y_uloc_sub_le m χ (le_max_right _ _) (le_max_right _ _) ?_ ?_
      · exact (HRS.MS.SA12BD.sa12_uloc_mono d (m+2) m (by omega) χ _).trans
          ((a₁.bound (N k) τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      · exact (HRS.MS.SA12BD.sa12_uloc_mono d (m+2) m (by omega) χ _).trans
          ((a₂.bound (N k) τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have hlsc := (local_norm_lower_semicontinuity hd m χ hχ (2 * (b1 + b2)) un u hloc hconv hB).2.2
    refine hlsc.trans ?_
    calc liminf (fun k => varpiNormE m χ (un k)) atTop
        ≤ liminf (fun _ : ℕ => W τ) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall fun k => (hbound (N k) τ hτ).2)
      _ = W τ := Filter.liminf_const _
-- END SA12.S7

end HRS.MH.AdjointRd.Phase2SA12Stability
