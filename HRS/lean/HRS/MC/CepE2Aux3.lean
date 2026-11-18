import HRS.MC.CepE2Aux2

/-!
# Packet CEPE2, auxiliary 3: existence of the resolvent (minimisation on a compact sublevel set)
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

open HRS.MC.CepE1

variable {N : ℕ}

theorem cepe2_hasGradient_quad (z x : Ch N) (n : ℝ) :
    HasGradientAt (fun y : Ch N => (n / 2) * ‖y - z‖ ^ 2) (n • (x - z)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 : HasFDerivAt (fun y : Ch N => y - z) (ContinuousLinearMap.id ℝ (Ch N)) x :=
    (hasFDerivAt_id x).sub_const z
  have h1 := (h0.norm_sq).const_mul (n / 2)
  convert h1 using 1
  ext w
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  ring

/-- The evenly spaced configuration lies in the alcove. -/
theorem cepe2_base_mem : (WithLp.toLp 2 (fun k : Fin N => ((k : ℕ) : ℝ) / N) : Ch N) ∈ cep_Alcove N := by
  rw [cepe2_mem_alcove_iff]
  intro k l hkl
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by rintro rfl; exact k.elim0)
  have hkl' : (k : ℕ) < (l : ℕ) := hkl
  have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hkl'
  have h2 : ((l : ℕ) : ℝ) < N := by exact_mod_cast l.2
  have h3 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Ioo, mem_setOf_eq]
  constructor
  · show 0 < ((l : ℕ) : ℝ) / N - ((k : ℕ) : ℝ) / N
    rw [← sub_div]; apply div_pos <;> linarith
  · show ((l : ℕ) : ℝ) / N - ((k : ℕ) : ℝ) / N < 1
    rw [← sub_div, div_lt_one hN]; linarith

theorem cepe2_exists_resolvent {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    ∃ x ∈ cep_Alcove N, n • (z - x) = cepe1_pairGrad (cepe1_h1 a N) x := by
  classical
  set E : Ch N → ℝ := fun x => cep_chamberPot a N x + (n / 2) * ‖x - z‖ ^ 2 with hE
  set x₀ : Ch N := WithLp.toLp 2 (fun k : Fin N => ((k : ℕ) : ℝ) / N) with hx₀
  have hx₀A : x₀ ∈ cep_Alcove N := cepe2_base_mem
  set B : ℝ := E x₀ with hB
  by_cases hN0 : N = 0
  · -- trivial case: no pairs
    subst hN0
    refine ⟨z, ?_, ?_⟩
    · rw [cepe2_mem_alcove_iff]; intro k; exact k.elim0
    · ext k; exact k.elim0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set c : ℝ := a / N with hc
  have hcpos : 0 < c := div_pos ha hNpos
  set P : ℝ := cepe2_npairs N with hP
  set M : ℝ := B / c + P * Real.log 2 with hM
  set δ : ℝ := cepe2_delta M with hδ
  have hδpos : 0 < δ := cepe2_delta_pos M
  set T : ℝ := (2 / n) * (B + c * P * Real.log 2) with hT
  -- the compact set
  set K : Set (Ch N) := {x | (∀ k l : Fin N, k < l → δ ≤ x l - x k ∧ x l - x k ≤ 1 - δ) ∧ ‖x - z‖ ^ 2 ≤ T} with hK
  have hKA : K ⊆ cep_Alcove N := by
    intro x hx
    rw [cepe2_mem_alcove_iff]
    intro k l hkl
    obtain ⟨h1, h2⟩ := hx.1 k l hkl
    exact ⟨by linarith, by linarith⟩
  have hsub : ∀ x ∈ cep_Alcove N, E x ≤ B → x ∈ K := by
    intro x hxA hxB
    have hq : 0 ≤ (n / 2) * ‖x - z‖ ^ 2 := by positivity
    have hΦ : cep_chamberPot a N x ≤ B := by simp only [hE] at hxB; linarith
    have hlow := cepe2_lower ha.le hxA
    refine ⟨fun k l hkl => ?_, ?_⟩
    · have hf : cepe2_f (x l - x k) ≤ cep_chamberPot a N x / c + P * Real.log 2 :=
        cepe2_gap_bound ha hxA hkl
      have : cepe2_f (x l - x k) ≤ M := by
        have : cep_chamberPot a N x / c ≤ B / c := div_le_div_of_nonneg_right hΦ hcpos.le
        simp only [hM]; linarith
      obtain ⟨h1, h2⟩ := cepe2_barrier (cepe2_mem_alcove_iff.1 hxA k l hkl) this
      exact ⟨h1, by linarith⟩
    · have h1 : (n / 2) * ‖x - z‖ ^ 2 ≤ B + c * P * Real.log 2 := by
        simp only [hE] at hxB; linarith
      have : ‖x - z‖ ^ 2 ≤ (2 / n) * (B + c * P * Real.log 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hn]
        nlinarith
      exact this
  have hx₀K : x₀ ∈ K := hsub x₀ hx₀A le_rfl
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : K = (⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l),
          {x : Ch N | δ ≤ x l - x k ∧ x l - x k ≤ 1 - δ}) ∩ {x : Ch N | ‖x - z‖ ^ 2 ≤ T} := by
        ext x
        simp only [hK, mem_setOf_eq, mem_inter_iff, mem_iInter]
      rw [this]
      refine IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ => ?_) ?_
      · have hd : Continuous fun x : Ch N => x l - x k :=
          ((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).continuous).sub ((EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).continuous)
        exact (isClosed_le continuous_const hd).inter (isClosed_le hd continuous_const)
      · exact isClosed_le ((continuous_id.sub continuous_const).norm.pow 2) continuous_const
    · refine (Metric.isBounded_closedBall (x := z) (r := Real.sqrt T)).subset fun x hx => ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := Real.abs_le_sqrt hx.2
      rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hcont : ContinuousOn E K := by
    intro x hx
    have hxA := hKA hx
    have h1 : ContinuousAt (cep_chamberPot a N) x := (cepe2_hasGradient hxA).differentiableAt.continuousAt
    have h2 : ContinuousAt (fun y : Ch N => (n / 2) * ‖y - z‖ ^ 2) x :=
      (cepe2_hasGradient_quad z x n).differentiableAt.continuousAt
    exact (h1.add h2).continuousWithinAt
  obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hcont
  have hxA := hKA hxK
  have hglob : ∀ y ∈ cep_Alcove N, E x ≤ E y := by
    intro y hy
    by_cases hyK : y ∈ K
    · exact hxmin hyK
    · have : B < E y := by
        by_contra hcon
        exact hyK (hsub y hy (not_lt.1 hcon))
      have : E x ≤ B := hxmin hx₀K
      linarith
  have hloc : IsLocalMin E x :=
    Filter.eventually_of_mem (cepe2_isOpen_alcove.mem_nhds hxA) hglob
  have hgrad : HasGradientAt E (cepe1_pairGrad (cepe1_h1 a N) x + n • (x - z)) x :=
    cepe1_hasGradientAt_add (cepe2_hasGradient hxA) (cepe2_hasGradient_quad z x n)
  have h0 := hloc.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.1 hgrad)
  have h00 : cepe1_pairGrad (cepe1_h1 a N) x + n • (x - z) = 0 := by
    have := (InnerProductSpace.toDual ℝ (Ch N)).injective (h0.trans (map_zero _).symm)
    exact this
  refine ⟨x, hxA, ?_⟩
  have : cepe1_pairGrad (cepe1_h1 a N) x = -(n • (x - z)) := eq_neg_of_add_eq_zero_left h00
  rw [this, ← smul_neg, neg_sub]

end HRS.MC.CepE2
