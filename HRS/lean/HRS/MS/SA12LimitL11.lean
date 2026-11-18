import HRS.MS.SA12LimitL11A
import HRS.MS.UlocCbAux1
import HRS.MS.MovOpAux1

/-!
# S.A.12 L11: `ℓ¹(L²)` bound of the weak operator on a localized test by the `H^{m_*}` norm of the test
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- A `C_c^∞` function lies in every `H^q`. -/
theorem sa12y_memSob {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (q : ℝ) :
    HRS.PDE.ToolboxRd.MemSobolev q ψ := by
  have := HRS.MS.MovC1.movc1_memSob_schwartz (d := d) (hψ.2.toSchwartzMap hψ.1) q
  exact this

theorem sa12y_jets_embed (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ i ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ i ψ x‖ ≤ C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (mStar d : ℝ) ψ) := by
  have hq : ((2 : ℕ) : ℝ) + d / 2 < (mStar d : ℝ) := by
    unfold mStar
    have h1 : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.div_add_mod d 2
      have h2 : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have : d ≤ 2 * (d / 2) + 1 := by omega
      exact_mod_cast this
    push_cast
    linarith
  obtain ⟨C, hC0, hC⟩ := HRS.MS.UlocCb.ucb_local_embedding (d := d) 2 hq
  refine ⟨C, hC0, fun ψ hψ i hi x => ?_⟩
  obtain ⟨g, hge, hg2, hgb⟩ := hC ψ (sa12y_memSob hψ _)
  have hgψ : g = ψ := by
    refine (Continuous.ae_eq_iff_eq volume (hg2.continuous) hψ.1.continuous).1 hge
  subst hgψ
  exact hgb i hi x

theorem sa12y_cut_jets {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (z : Euc d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ M := by
  have hf : ContDiff ℝ ∞ (fun y : Euc d => χ (y - z)) := hχ.1.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport (fun y : Euc d => χ (y - z)) :=
    hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  have hex : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ C := fun i =>
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hfc.iteratedFDeriv i)
  choose C hC using hex
  refine ⟨|C 0| + |C 1| + |C 2|, by positivity, fun i hi x => ?_⟩
  refine (hC i x).trans ?_
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    linarith [abs_nonneg (C 0), abs_nonneg (C 1), abs_nonneg (C 2),
      le_abs_self (C 0), le_abs_self (C 1), le_abs_self (C 2)]

theorem sa12y_prod_jets {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {Mf Mg : ℝ}
    (hf0 : 0 ≤ Mf) (hg0 : 0 ≤ Mg)
    (hMf : ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ Mf)
    (hMg : ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ Mg) :
    ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i (fun y => f y * g y) x‖ ≤ 4 * (Mf * Mg) := by
  intro i hi x
  refine (norm_iteratedFDeriv_mul_le hf hg x (n := i) (by exact_mod_cast le_top)).trans ?_
  calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Mf * Mg := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ 2 := by have := Finset.mem_range.1 hj; omega
        have hj'' : i - j ≤ 2 := by omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hMf j hj' x) (by positivity)) (hMg _ hj'' x)
          (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ i * (Mf * Mg) := by
        have : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        rw [← Finset.sum_mul, ← Finset.sum_mul, this]
        ring
    _ ≤ 4 * (Mf * Mg) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hi
          _ = 4 := by norm_num

theorem sa12y_loc_supp {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (z : Euc d) (ψ : Euc d → ℝ) :
    tsupport (fun x => χ (x - z) * ψ x) ⊆ Metric.closedBall (0 : Euc d) (‖z‖ + 2) := by
  intro x hx
  have h1 : tsupport (fun x => χ (x - z) * ψ x) ⊆ tsupport (fun x => χ (x - z)) :=
    tsupport_mul_subset_left
  have h2 : tsupport (fun x : Euc d => χ (x - z)) ⊆ (fun x => x - z) ⁻¹' tsupport χ := by
    refine closure_minimal ?_ ((isClosed_tsupport χ).preimage (continuous_id.sub continuous_const))
    intro y hy
    exact subset_tsupport χ hy
  have h3 : x - z ∈ tsupport χ := h2 (h1 hx)
  have h4 := hχ.2.2.1 h3
  rw [mem_ball_zero_iff] at h4
  rw [mem_closedBall_zero_iff]
  calc ‖x‖ = ‖(x - z) + z‖ := by simp
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ := by linarith

-- BEGIN SA12.L11
theorem localized_test_operator_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (z : Euc d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (weakOp (D.coeff μ) t σ (fun x => χ (x - z) * ψ x)) ≤
        ENNReal.ofReal K * sobolevNormE (mStar d : ℝ) ψ := by
  set R : ℝ := ‖z‖ + 2 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  obtain ⟨K0, hK0, hK⟩ := sa12y_weakOp_bound hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD R hR1
  obtain ⟨CA, hCA, hCell⟩ := sa12y_cell_decay hd
  obtain ⟨Ce, hCe, hE⟩ := sa12y_jets_embed hd
  obtain ⟨Mχ, hMχ0, hMχ⟩ := sa12y_cut_jets hχ z
  refine ⟨CA * K0 * (4 * (Mχ * Ce)), by positivity, fun ψ hψ σ hσ => ?_⟩
  set S : ℝ := HRS.PDE.ToolboxRd.sobolevNormSq (mStar d : ℝ) ψ with hS
  have hS0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  set A : ℝ := 4 * (Mχ * (Ce * Real.sqrt S)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hφ : ContDiff ℝ ∞ (fun x => χ (x - z) * ψ x) :=
    (hχ.1.comp (contDiff_id.sub contDiff_const)).mul hψ.1
  have hjet := sa12y_prod_jets (f := fun y => χ (y - z)) (g := ψ)
    (hχ.1.comp (contDiff_id.sub contDiff_const)) hψ.1 hMχ0 (by positivity) hMχ
    (fun i hi x => hE ψ hψ i hi x)
  have hbd := hK (fun x => χ (x - z) * ψ x) A hφ (sa12y_loc_supp hχ z ψ) hA0 hjet (t - σ) hr
  have hcell := hCell (weakOp (D.coeff μ) t σ (fun x => χ (x - z) * ψ x)) (K0 * A)
    (by positivity) (fun x => by simpa [weakOp, mul_assoc] using hbd x)
  have e : sobolevNormE (mStar d : ℝ) ψ = ENNReal.ofReal (Real.sqrt S) := by
    unfold sobolevNormE
    rw [if_pos (sa12y_memSob hψ _)]
  rw [e]
  refine hcell.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hA]; ring
-- END SA12.L11

end HRS.MH.AdjointRd.Phase2SA12Limit
