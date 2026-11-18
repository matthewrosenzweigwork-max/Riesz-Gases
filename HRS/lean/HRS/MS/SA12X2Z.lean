import HRS.MS.SA12X2Y

/-!
# S.A.12 N8 (SA12X2), part Z: `near_R2a`

`d - 1 < s < d`: the localizer `η` is the advected cutoff of a bump equal to `1` on `tsupport χ̂`; the case `s ≤ d - 1` is
`sa12x2_near_R2a_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_eta0 {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    ∃ η0 : Euc d → ℝ, IsCutoffPair χ η0 ∧ ∀ x ∈ tsupport χh, η0 x = 1 := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨g1, g2, g3, g4, g5⟩⟩ := hχ
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport χh) g3
  set r1 : ℝ := max r 6 with hr1
  have hr16 : 6 ≤ r1 := le_max_right _ _
  have hr18 : r1 < 8 := max_lt hr (by norm_num)
  let f : ContDiffBump (0 : Euc d) := ⟨r1, (r1 + 8) / 2, by linarith, by linarith⟩
  have hfs : tsupport f ⊆ ball (0 : Euc d) 8 := by
    rw [f.tsupport_eq]
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    have : f.rOut = (r1 + 8) / 2 := rfl
    linarith
  refine ⟨f, ⟨⟨h1, h2, h3, h4, h5⟩, f.contDiff, f.hasCompactSupport, hfs,
    fun x => ⟨f.nonneg, f.le_one⟩, fun x hx => f.one_of_mem_closedBall ?_⟩, fun x hx => ?_⟩
  · have : f.rIn = r1 := rfl
    rw [this]
    exact closedBall_subset_closedBall hr16 hx
  · refine f.one_of_mem_closedBall ?_
    have : f.rIn = r1 := rfl
    rw [this]
    have h0 := mem_ball_zero_iff.1 (hsub hx)
    rw [mem_closedBall_zero_iff]
    exact (h0.trans_le (le_max_left _ _)).le

/-- N8 for `d - 1 < s < d`. -/
theorem sa12x2_near_R2a_hard (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0
        (fun M => PDE.MatBound MB M ∧ Torus.symPart M = 0) := by
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨B, R, hB, hR1, hfacts⟩ := HRS.MH.AdjointRd.Phase2SA12.advected_cutoff_jets d hd m Cb T χ χh hχ
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  set Ka : ℝ := 2 ^ (m + 1) * B * Λ' with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  obtain ⟨η0, hχη, hη0one⟩ := sa12x2_eta0 hχ
  obtain ⟨B2, R2, hB2, hR21, hfacts2⟩ := HRS.MH.AdjointRd.Phase2SA12.advected_cutoff_jets d hd m Cb T χ η0 hχη
  set Rm : ℝ := max R R2 with hRm
  have hRm1 : 1 ≤ Rm := hR1.trans (le_max_left _ _)
  have hKw0 : 0 ≤ B := hB.le
  have hKe0 : 0 ≤ B2 := hB2.le
  have hKp0 : 0 ≤ Λ' := hΛ'0
  obtain ⟨A1, hA1, hidx⟩ := sa12x2_idx_hard hd hs0 hsd hs1 m hm MB Ka B B2 Λ' Rm hKa0 hKw0 hKe0 hKp0 hRm1
  set Q : ℝ := ∑ r ∈ Finset.range (m + 1), (Nat.choose m r : ℝ) * (d : ℝ) ^ r with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun r _ => by positivity
  refine ⟨E, 2 * A1 * Q, hE, by positivity, ?_⟩
  intro b Ψ hb hΨ M hM μ hμ F hF τ hτ z
  have hFi : ContDiff ℝ ∞ F := hF.1
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
  -- the localizer `η`
  set η : Euc d → ℝ := advCutoff η0 Ψ τ (cellPt d z) with hη
  have hcut2 := hfacts2 b Ψ hb hΨ τ hτ (cellPt d z)
  have hη_cd : ContDiff ℝ (m + 1) η := hcut2.1.2
  have hη2 : ContDiff ℝ 2 η := hη_cd.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hηsup : Function.support η ⊆ closedBall c Rm :=
    hcut2.2.2.trans (closedBall_subset_closedBall (le_max_right _ _))
  have hηc : HasCompactSupport η :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hηsup
  have hηle : ∀ x, η x ≤ 1 := fun x => (hχη.2.2.2.2.1 _).2
  have hηjet : ∀ k ≤ 1, ∀ x, ‖iteratedFDeriv ℝ k η x‖ ≤ B2 := fun k hk x =>
    (hcut2.2.1 k (by omega) x).2
  have hηom : ∀ x, om x ≠ 0 → η x = 1 := by
    intro x hx
    have h2 := sa12z3_adv_ne_norm_lt hχ Ψ τ (cellPt d z) hx
    exact hχη.2.2.2.2.2 _ (by rw [mem_closedBall, dist_zero_right]; linarith)
  have hηa : ∀ x ∈ tsupport a, η x = 1 := by
    have hcl : IsClosed {x | η x = 1} := isClosed_eq hη_cd.continuous continuous_const
    refine closure_minimal (fun y hy => ?_) hcl
    have hy0 : oh y ≠ 0 := left_ne_zero_of_mul (Function.mem_support.1 hy)
    exact hη0one _ (subset_tsupport _ hy0)
  have hclW : IsClosed {x | 1 ≤ W x} := isClosed_le continuous_const hWc
  have hWo : ∀ y ∈ tsupport om, 1 ≤ W y := by
    refine closure_minimal (fun y hy => ?_) hclW
    have := sa12z3_adv_ne_norm_lt hχ Ψ τ (cellPt d z) (Function.mem_support.1 hy)
    exact sa12z3_W_ge_one hχ hE Ψ τ z y (by linarith)
  have hWη : ∀ y ∈ tsupport η, 1 ≤ W y := by
    refine closure_minimal (fun y hy => ?_) hclW
    have := sa12z3_advh_ne_norm_lt hχη Ψ τ (cellPt d z) (Function.mem_support.1 hy)
    exact sa12z3_W_ge_one hχ hE Ψ τ z y (le_of_lt this)
  have hW0 : ∀ y, 0 ≤ W y := fun y => sa12z3_W_nonneg E χ Ψ τ z y
  have hom2 : ContDiff ℝ 2 om := (hcut (cellPt d z)).1.1.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hKwb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ B := fun k hk x =>
    ((hcut (cellPt d z)).2.1 k (by omega) x).1
  have hμ3 : ContDiff ℝ 3 μ := hμ.1.of_le (by exact_mod_cast (by omega : 3 ≤ m + 3))
  have hμ3b : ∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k μ x‖ ≤ Λ' := fun k hk x => hμb k (by omega) x
  have hamu : ∀ l x, om x ^ 2 * D1 l a x = om x ^ 2 * D1 l μ x := by
    intro l x
    by_cases hx : om x = 0
    · simp [hx]
    · have h2 := sa12z3_adv_ne_norm_lt hχ Ψ τ (cellPt d z) hx
      have h1 : oh x = 1 := hχ.2.2.2.2.2 _ (by rw [mem_closedBall, dist_zero_right]; linarith)
      have := sa12x2_eta_D1 (η := oh) (Z := μ) ((hcut (cellPt d z)).1.2.of_le (by
        exact_mod_cast (by omega : 1 ≤ m + 1))) (fun y => (hχ.2.2.2.2.1 _).2)
        (hμ2.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))) x h1 l
      rw [show D1 l a x = D1 l (fun y => oh y * μ y) x from rfl, this]
  have hbd : ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d),
      -(∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (eucNonlocal s M a F) x)) ≤ A1 * ∫ x, W x * sa12z3_Y m F x :=
    fun n hn idx => hidx c om η a μ W F M hM.1 hM.2 hom2 (hcs _) hom1 hKwb
      (hsupp _ |>.trans (closedBall_subset_closedBall (le_max_left _ _))) hη2 hηc hηsup hηle hηjet hηom
      hηa hWc hWcs hW0 hWo hWη haC (hasup.trans (closedBall_subset_closedBall (le_max_left _ _)))
      hKaB hμ3 hμ3b hamu hFi n hn idx
  have hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ => ⟨(hcont _).1, hcs _⟩
  have he := sa12z3_e_le m (E := E) (χ := χ) (Ψ := Ψ) (τ := τ) (z := z) hFi hω
  set e : ℝ := ∫ x, W x * sa12z3_Y m F x with he_def
  have he0 : 0 ≤ e := integral_nonneg fun x =>
    mul_nonneg ((sq_nonneg _).trans (hWom x)) (sa12z3_Y_nonneg _ _ _)
  have hjet : -(jetPair m om F (eucNonlocal s M a F)) ≤ A1 * e * Q := by
    unfold jetPair
    rw [← Finset.sum_neg_distrib]
    have hterm : ∀ j ∈ Finset.range (m + 1), -((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x)) ≤
        (Nat.choose m j : ℝ) * (d : ℝ) ^ j * (A1 * e) := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [neg_mul_eq_mul_neg, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← Finset.sum_neg_distrib]
      refine (Finset.sum_le_sum fun idx _ => hbd j hjm idx).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      exact le_refl _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [hQ, Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => by ring)
  have hS0 : 0 ≤ ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := le_trans he0 he
  calc -(2 * jetPair m om F (eucNonlocal s M a F)) = 2 * (-(jetPair m om F (eucNonlocal s M a F))) := by ring
    _ ≤ 2 * (A1 * e * Q) := by gcongr
    _ = (2 * A1 * Q) * e := by ring
    _ ≤ (2 * A1 * Q) * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 0 * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F +
        (2 * A1 * Q) * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := by ring

theorem near_R2a (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs2 : (d : ℝ)-2<s) (hsd : s<d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0
        (fun M => PDE.MatBound MB M ∧ Torus.symPart M=0) := by
  by_cases h : s ≤ (d : ℝ) - 1
  · exact sa12x2_near_R2a_le d hd s hs0 h m hm MB Λ Cb T χ χh hχ
  · exact sa12x2_near_R2a_hard d hd s hs0 (not_le.1 h) hsd m hm MB Λ Cb T χ χh hχ

end HRS.MH.AdjointRd.Phase2SA12Near
