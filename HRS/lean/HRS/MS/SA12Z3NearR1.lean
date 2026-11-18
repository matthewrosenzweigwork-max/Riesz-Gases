import HRS.MS.SA12Z3NearN7

/-!
# S.A.12 N7 (SA12Z3): `near_R1`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `cbNorm ≤ max Λ 0` from the regularity predicate. -/
theorem sa12z3_cb_le {r : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW r Λ μ) :
    cbNorm r μ ≤ max Λ 0 := by
  have h1 : ENNReal.ofReal (cbNorm r μ) ≤ ENNReal.ofReal Λ := le_trans le_self_add hμ.2.2
  rcases (ENNReal.ofReal_le_ofReal_iff').1 h1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

theorem near_R1 (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ)-2) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0 (fun M => PDE.MatBound MB M) := by
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨B, R, hB, hR1, hfacts⟩ := HRS.MH.AdjointRd.Phase2SA12.advected_cutoff_jets d hd m Cb T χ χh hχ
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  set Ka : ℝ := 2 ^ (m + 1) * B * Λ' with hKa
  obtain ⟨A1, hA1, hidx⟩ := sa12z3_idx_bound hd hs0 hs2 m hm MB Ka R hR1
  set Q : ℝ := ∑ r ∈ Finset.range (m + 1), (Nat.choose m r : ℝ) * (d : ℝ) ^ r with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun r _ => by positivity
  refine ⟨E, 2 * A1 * Q, hE, by positivity, ?_⟩
  intro b Ψ hb hΨ M hM μ hμ F hF τ hτ z
  have hFi : ContDiff ℝ ∞ F := hF.1
  -- cutoff facts at every centre
  have hcut := fun (z' : Euc d) => hfacts b Ψ hb hΨ τ hτ z'
  have hcont : ∀ (z' : Euc d), Continuous (advCutoff χ Ψ τ z') ∧ Continuous (advCutoff χh Ψ τ z') :=
    fun z' => ⟨(hcut z').1.1.continuous, (hcut z').1.2.continuous⟩
  have hsupp : ∀ (z' : Euc d), Function.support (advCutoff χ Ψ τ z') ⊆ closedBall (Ψ τ z') R :=
    fun z' => (sa12z3_adv_support_le hχ Ψ τ z').trans (hcut z').2.2
  have hcs : ∀ (z' : Euc d), HasCompactSupport (advCutoff χ Ψ τ z') := fun z' =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp z')
  set c : Euc d := Ψ τ (cellPt d z) with hc
  set om : Euc d → ℝ := advCutoff χ Ψ τ (cellPt d z) with hom
  set oh : Euc d → ℝ := advCutoff χh Ψ τ (cellPt d z) with hoh
  set W : Euc d → ℝ := sa12z3_W E χ Ψ τ z with hW
  have hWc : Continuous W := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact (hcont _).1.pow 2
  have hWcs : HasCompactSupport W := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := ⋃ k ∈ E, closedBall (Ψ τ (cellPt d (z + k))) R) ?_ ?_
    · exact (E.finite_toSet.isCompact_biUnion fun k _ => isCompact_closedBall _ _)
    · intro x hx
      have : ∃ k ∈ E, advCutoff χ Ψ τ (cellPt d (z + k)) x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hx
        exact Finset.sum_eq_zero fun k hk => by rw [hcon k hk]; norm_num
      obtain ⟨k, hk, hk0⟩ := this
      exact Set.mem_iUnion₂.2 ⟨k, hk, hsupp _ (Function.mem_support.2 hk0)⟩
  have hom1 : ∀ x, |om x| ≤ 1 := fun x => by
    have := hχ.1.2.2.2.1 (Function.invFun (Ψ τ) x - cellPt d z)
    show |χ (Function.invFun (Ψ τ) x - cellPt d z)| ≤ 1
    rw [abs_of_nonneg this.1]; exact this.2
  have hWom : ∀ x, om x ^ 2 ≤ W x := by
    intro x
    by_cases hx : om x = 0
    · rw [hx]; simpa using sa12z3_W_nonneg E χ Ψ τ z x
    · have h1 := sa12z3_adv_ne_norm_lt hχ Ψ τ (cellPt d z) hx
      have h2 := sa12z3_W_ge_one hχ hE Ψ τ z x (by linarith)
      have h3 : om x ^ 2 ≤ 1 := by
        have := hom1 x; nlinarith [abs_nonneg (om x), sq_abs (om x)]
      exact h3.trans h2
  -- the density cut
  set a : Euc d → ℝ := fun y => oh y * μ y with ha
  have hμ2 : ContDiff ℝ (m + 1) μ := hμ.1.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 3))
  have haC : ContDiff ℝ (m + 1) a := (hcut (cellPt d z)).1.2.mul hμ2
  have hasup : Function.support a ⊆ closedBall c R := fun y hy =>
    (hcut (cellPt d z)).2.2 (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hac : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hasup
  have hμb : ∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ' := fun j hj x =>
    (HRS.MH.AdjointRd.Phase2SA12.sa12r35_single_le_cb hμ.2.1 hj x).trans (sa12z3_cb_le hμ)
  have hKaB : ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka := by
    intro k hk x
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ((m + 1 : ℕ) : WithTop ℕ∞)) (hf := (hcut (cellPt d z)).1.2)
      (hg := hμ2) x (n := k) (by exact_mod_cast hk)
    refine h1.trans ?_
    have h2 : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i oh x‖ *
        ‖iteratedFDeriv ℝ (k - i) μ x‖ ≤ (k.choose i : ℝ) * (B * Λ') := by
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have b1 := ((hcut (cellPt d z)).2.1 i (by omega) x).2
      have b2 := hμb (k - i) (by omega) x
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i oh x‖ * ‖iteratedFDeriv ℝ (k - i) μ x‖
          ≤ (k.choose i : ℝ) * B * Λ' := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.sum_mul]
    have : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
    rw [this]
    have h3 : (2 : ℝ) ^ k ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) hk
    calc (2 : ℝ) ^ k * (B * Λ') ≤ 2 ^ (m + 1) * (B * Λ') :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Ka := by rw [hKa]; ring
  have hWa : ∀ x ∈ tsupport a, 1 ≤ W x := by
    have hcl : IsClosed {x | 1 ≤ W x} := isClosed_le continuous_const hWc
    refine closure_minimal (fun y hy => ?_) hcl
    have hy0 : oh y ≠ 0 := left_ne_zero_of_mul (Function.mem_support.1 hy)
    exact sa12z3_W_ge_one hχ hE Ψ τ z y (le_of_lt (sa12z3_advh_ne_norm_lt hχ Ψ τ _ hy0))
  have hbd : ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d),
      |∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (eucNonlocal s M a F) x)| ≤ A1 * ∫ x, W x * sa12z3_Y m F x :=
    fun n hn idx => hidx c om a W F M hM (hcont _).1 (hcs _) (hsupp _) hom1 hWc hWcs hWom haC hac hasup hKaB hWa hFi n hn idx
  have hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ => ⟨(hcont _).1, hcs _⟩
  have he := sa12z3_e_le m (E := E) (χ := χ) (Ψ := Ψ) (τ := τ) (z := z) hFi hω
  set e : ℝ := ∫ x, W x * sa12z3_Y m F x with he_def
  have he0 : 0 ≤ e := integral_nonneg fun x =>
    mul_nonneg ((sq_nonneg _).trans (hWom x)) (sa12z3_Y_nonneg _ _ _)
  have hjet : |jetPair m om F (eucNonlocal s M a F)| ≤ A1 * e * Q := by
    unfold jetPair
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range (m + 1), |(Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x)| ≤
        (Nat.choose m j : ℝ) * (d : ℝ) ^ j * (A1 * e) := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun idx _ => hbd j hjm idx).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      exact le_refl _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [hQ, Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => by ring)
  have hS0 : 0 ≤ ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := le_trans he0 he
  have hfin : -(2 * jetPair m om F (eucNonlocal s M a F)) ≤ 2 * (A1 * e * Q) := by
    have := neg_abs_le (jetPair m om F (eucNonlocal s M a F))
    linarith
  calc -(2 * jetPair m om F (eucNonlocal s M a F)) ≤ 2 * (A1 * e * Q) := hfin
    _ = (2 * A1 * Q) * e := by ring
    _ ≤ (2 * A1 * Q) * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 0 * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F +
        (2 * A1 * Q) * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
