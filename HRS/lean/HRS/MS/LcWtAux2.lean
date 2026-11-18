import HRS.MS.FlowC

/-!
# LC-2, part 2: weighted derivative bounds for a `C^{m+1}` parametrisation `Ξ` of a flow

Generic space `E` (finite dimensional, complete).  Setting of `FlowCAux2`: `Ξ : E → (ℝ →ᵇ E)` is
`C^{m+1}` with `Gmap S b (Ξ x) = constCLM E x` (the path of the flow of `-b` from `x`), and `tay S b α k`
is the `k`-th derivative of the Nemytskii-integral operator at `α`.  The unweighted induction of
`FlowC` (`fc_step`, `fc_induction`) is redone with a decay factor along the trajectory.

Weights.  Fix `σ ≥ 0` and `ω ∈ (0,1]` (in the application `ω = ⟨x₀⟩⁻¹`, `σ = s+1`).  An `a`-th variation
of the flow is expected to be of size `ω^{lc2_e σ a}` with `lc2_e σ 1 = 0`, `lc2_e σ a = σ + a` (`a ≥ 2`),
while `D^k b` along the trajectory is of size `ω^{σ+k}` (`k ≥ 2`, hypothesis `htay`).  The exponent count of
the TeX (S L3040-3050) is `lc2_comb`: for every ordered finpartition `c` of `{1..j}`,
`ω^{β+ℓ} ∏_i ω^{e(a_i)} ≤ ω^{β+j}` (`ℓ = c.length`, `a_i` the block sizes), because
`e(a) ≥ a - 1` and `Σ a_i = j`.

Main results: `lc2_step` (one induction step, analogue of `fc_step`) and `lc2_induction` (analogue of
`fc_induction`): `‖D^iΞ(x₀)‖ ≤ C Bt^P ω^{e(i)}` for `1 ≤ i ≤ m+1`, with `C, P` depending only on
`m, T, Λ` and `Bt ≥ 1` the constant of `htay`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.Lc

open HRS.MS.FlowB HRS.MS.FlowC

/-- The decay exponent of an `a`-th variation of the flow: `0` for `a = 1`, `σ + a` for `a ≥ 2`. -/
def lc2_e (σ : ℝ) (a : ℕ) : ℝ := if a = 1 then 0 else σ + a

theorem lc2_e_ge {σ : ℝ} (hσ : 0 ≤ σ) {a : ℕ} (ha : 1 ≤ a) : (a : ℝ) - 1 ≤ lc2_e σ a := by
  unfold lc2_e
  split_ifs with h
  · subst h; simp
  · linarith

theorem lc2_e_one (σ : ℝ) : lc2_e σ 1 = 0 := by simp [lc2_e]

theorem lc2_e_of_ne {σ : ℝ} {a : ℕ} (ha : a ≠ 1) : lc2_e σ a = σ + a := by simp [lc2_e, ha]

/-- The exponent count: `ω^{β+ℓ} ∏_i ω^{e(a_i)} ≤ ω^{β+j}` for every ordered finpartition. -/
theorem lc2_comb {j : ℕ} (c : OrderedFinpartition j) {σ ω : ℝ} (β : ℝ) (hσ : 0 ≤ σ) (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) :
    ω ^ (β + (c.length : ℝ)) * ∏ i, ω ^ (lc2_e σ (c.partSize i)) ≤ ω ^ (β + (j : ℝ)) := by
  rw [← Real.rpow_sum_of_pos hω0, ← Real.rpow_add hω0]
  apply Real.rpow_le_rpow_of_exponent_ge hω0 hω1
  have hsum : ∑ i : Fin c.length, ((c.partSize i : ℕ) : ℝ) = (j : ℝ) := by
    have h := c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    exact_mod_cast h
  have h1 : ∑ i : Fin c.length, (((c.partSize i : ℕ) : ℝ) - 1) ≤
      ∑ i : Fin c.length, lc2_e σ (c.partSize i) :=
    Finset.sum_le_sum fun i _ => lc2_e_ge hσ (c.partSize_pos i)
  rw [Finset.sum_sub_distrib, hsum] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
  linarith

section Fdb

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem lc2_length_ge_two {n : ℕ} (hn : 2 ≤ n) (c : OrderedFinpartition n)
    (hc : c ≠ fc_single n (by omega)) : 2 ≤ c.length := by
  by_contra hlt
  have h1 : c.length = 1 := le_antisymm (by omega) (c.length_pos (by omega))
  have hi : c.partSize ⟨0, by omega⟩ = n := by
    refine le_antisymm (c.partSize_le _) ?_
    have := c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    have h2 : ∑ i : Fin c.length, c.partSize i = n := this
    have h3 : (Finset.univ : Finset (Fin c.length)) = {⟨0, by omega⟩} := by
      ext i; simp [Fin.ext_iff]; omega
    rw [h3] at h2
    simpa using h2.ge
  exact hc (fc_eq_single (by omega) c hi)

/-- Faà di Bruno with the top-order term separated, with the weighted bound of the remainder. -/
theorem lc2_fdb_split {n : ℕ} (hn : 2 ≤ n) (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) :
    ∃ R : E [×n]→L[ℝ] G,
      q.taylorComp p n =
        (continuousMultilinearCurryFin1 ℝ F G (q 1)).compContinuousMultilinearMap (p n) + R ∧
      ∀ (Bt K σ ω : ℝ), 1 ≤ K → 0 ≤ σ → 0 < ω → ω ≤ 1 → 0 ≤ Bt →
        (∀ k : ℕ, 2 ≤ k → k ≤ n → ‖q k‖ ≤ Bt * ω ^ (σ + (k : ℝ))) →
        (∀ a : ℕ, 1 ≤ a → a < n → ‖p a‖ ≤ K * ω ^ (lc2_e σ a)) →
        ‖R‖ ≤ Fintype.card (OrderedFinpartition n) * (Bt * K ^ n * ω ^ (σ + (n : ℝ))) := by
  classical
  have hn' : 0 < n := by omega
  refine ⟨∑ c ∈ Finset.univ.erase (fc_single n hn'), q.compAlongOrderedFinpartition p c, ?_, ?_⟩
  · unfold FormalMultilinearSeries.taylorComp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fc_single n hn'))]
    congr 1
  · intro Bt K σ ω hK hσ hω0 hω1 hBt hq hp
    have hK0 : 0 ≤ K := by linarith
    have hterm : ∀ c ∈ Finset.univ.erase (fc_single n hn'),
        ‖q.compAlongOrderedFinpartition p c‖ ≤ Bt * K ^ n * ω ^ (σ + (n : ℝ)) := by
      intro c hc
      have hcne : c ≠ fc_single n hn' := Finset.ne_of_mem_erase hc
      have hl2 := lc2_length_ge_two hn c hcne
      have hlenn : c.length ≤ n := c.length_le
      have hcomb := lc2_comb c σ hσ hω0 hω1
      have hprod : ∏ i, ‖p (c.partSize i)‖ ≤ ∏ i : Fin c.length,
          (K * ω ^ (lc2_e σ (c.partSize i))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => hp _ (c.partSize_pos i) (fc_partSize_lt hn' c hcne i))
      have hpe : ∏ i : Fin c.length, (K * ω ^ (lc2_e σ (c.partSize i))) =
          K ^ c.length * ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i)) := by
        rw [Finset.prod_mul_distrib]; simp
      have hqb := hq c.length hl2 hlenn
      calc ‖q.compAlongOrderedFinpartition p c‖ ≤ ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ :=
            c.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ (Bt * ω ^ (σ + (c.length : ℝ))) *
              (K ^ c.length * ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i))) := by
            rw [← hpe]
            exact mul_le_mul hqb hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
              (mul_nonneg hBt (Real.rpow_nonneg hω0.le _))
        _ = Bt * K ^ c.length * (ω ^ (σ + (c.length : ℝ)) *
              ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i))) := by ring
        _ ≤ Bt * K ^ n * ω ^ (σ + (n : ℝ)) := by
            have h1 : Bt * K ^ c.length ≤ Bt * K ^ n :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hlenn) hBt
            have h2 : 0 ≤ ω ^ (σ + (c.length : ℝ)) *
                ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i)) :=
              mul_nonneg (Real.rpow_nonneg hω0.le _)
                (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg hω0.le _)
            exact mul_le_mul h1 hcomb h2 (mul_nonneg hBt (pow_nonneg hK0 _))
    refine (norm_sum_le _ _).trans ?_
    have hB0 : 0 ≤ Bt * K ^ n * ω ^ (σ + (n : ℝ)) := by positivity
    calc ∑ c ∈ Finset.univ.erase (fc_single n hn'), ‖q.compAlongOrderedFinpartition p c‖
        ≤ ∑ _c ∈ Finset.univ.erase (fc_single n hn'), Bt * K ^ n * ω ^ (σ + (n : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.univ.erase (fc_single n hn')).card : ℝ) *
            (Bt * K ^ n * ω ^ (σ + (n : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) * (Bt * K ^ n * ω ^ (σ + (n : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          exact_mod_cast (Finset.card_erase_le).trans (by simp)

end Fdb

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {S : ℝ} {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} {Ξ : E → (ℝ →ᵇ E)}

/-- The `k`-th derivative of the Nemytskii operator at `α` is bounded by `S` times a pointwise bound
of `D^k b_s` along `α`. -/
theorem lc2_tay_norm {S : ℝ} (hS : 0 ≤ S) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB S m Λ b)
    (α : ℝ →ᵇ E) {k : ℕ} (hkm : k ≤ m + 1) {D : ℝ}
    (hD : ∀ s ∈ Icc (0 : ℝ) S, ‖iteratedFDeriv ℝ k (b s) (α s)‖ ≤ D) : ‖tay S b α k‖ ≤ D * S := by
  have hB : HasB (fun s => iteratedFDeriv ℝ k (bt S b s) (α s)) := (hb.good hS hkm).hasB α
  unfold tay
  refine (norm_Vop_le hS hB).trans ?_
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S) (C := D)
    (f := fun s => ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖) (fun s hs => by
      rw [norm_norm]
      have hs' : s ∈ Icc (0 : ℝ) S := by
        rw [uIoc_of_le hS] at hs; exact ⟨hs.1.le, hs.2⟩
      have e : bt S b s = b s := by unfold bt; rw [FlowB.clampT_of_mem hs']
      rw [e]
      exact hD s hs')
  calc _ ≤ ‖∫ s in (0 : ℝ)..S, ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖‖ := Real.le_norm_self _
    _ ≤ D * |S - 0| := h
    _ = D * S := by rw [sub_zero, abs_of_nonneg hS]

/-- One weighted induction step (analogue of `fc_step`). -/
theorem lc2_step (hS : 0 ≤ S) (hb : DB S m Λ b)
    (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) (hG : ∀ x, Gmap S b (Ξ x) = constCLM E x)
    {j : ℕ} (hj2 : 2 ≤ j) (hjm : j ≤ m + 1) (x0 : E) {K Bt σ ω : ℝ} (hK : 1 ≤ K) (hBt : 0 ≤ Bt)
    (hσ : 0 ≤ σ) (hω0 : 0 < ω) (hω1 : ω ≤ 1)
    (hlow : ∀ i : ℕ, 1 ≤ i → i < j → ‖iteratedFDeriv ℝ i Ξ x0‖ ≤ K * ω ^ (lc2_e σ i))
    (htay : ∀ k : ℕ, 2 ≤ k → k ≤ j → ‖tay S b (Ξ x0) k‖ ≤ Bt * ω ^ (σ + (k : ℝ))) :
    ‖iteratedFDeriv ℝ j Ξ x0‖ ≤
      Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) *
        (Bt * K ^ j * ω ^ (σ + (j : ℝ)))) := by
  have hΛ := hb.Λ_nonneg hS
  set n : WithTop ℕ∞ := ((m + 1 : ℕ) : WithTop ℕ∞) with hn_def
  have hnem : HasFTaylorSeriesUpTo n (nem S b) (tay S b) := by
    have := hasFTaylor hS hb
    exact_mod_cast this
  have hjn : (j : WithTop ℕ∞) ≤ n := by rw [hn_def]; exact_mod_cast hjm
  have hcomp : HasFTaylorSeriesUpTo n (nem S b ∘ Ξ)
      (fun x => (tay S b (Ξ x)).taylorComp (ftaylorSeries ℝ Ξ x)) :=
    hasFTaylorSeriesUpToOn_univ_iff.1
      (HasFTaylorSeriesUpToOn.comp (hasFTaylorSeriesUpToOn_univ_iff.2 hnem)
        (hasFTaylorSeriesUpToOn_univ_iff.2 hΞ.ftaylorSeries) (mapsTo_univ _ _))
  have hD := hcomp.eq_iteratedFDeriv hjn x0
  have hident : (fun x => Ξ x + nem S b (Ξ x)) = ⇑(constCLM E) := funext fun x => hG x
  have hΞj : ContDiffAt ℝ (j : ℕ) Ξ x0 := (hΞ.of_le hjn).contDiffAt
  have hNj : ContDiffAt ℝ (j : ℕ) (nem S b ∘ Ξ) x0 :=
    (((contDiff_nem hS hb).comp hΞ).of_le hjn).contDiffAt
  have hdiff : iteratedFDeriv ℝ j (fun x => Ξ x + nem S b (Ξ x)) x0 =
      iteratedFDeriv ℝ j Ξ x0 + iteratedFDeriv ℝ j (nem S b ∘ Ξ) x0 :=
    iteratedFDeriv_add_apply hΞj hNj
  rw [hident, fc_ccl_zero hj2] at hdiff
  have hsum : iteratedFDeriv ℝ j Ξ x0 +
      (tay S b (Ξ x0)).taylorComp (ftaylorSeries ℝ Ξ x0) j = 0 := by
    rw [hD, ← hdiff]
  obtain ⟨R, hR, hRb⟩ := lc2_fdb_split (n := j) hj2 (tay S b (Ξ x0)) (ftaylorSeries ℝ Ξ x0)
  have hRn := hRb Bt K σ ω hK hσ hω0 hω1 hBt (fun k hk1 hkj => htay k hk1 hkj)
    (fun a ha1 haj => hlow a ha1 haj)
  set M : ℝ := Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) *
    (Bt * K ^ j * ω ^ (σ + (j : ℝ)))) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound hM0 fun v => ?_
  have hv := congrArg (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) (ℝ →ᵇ E) => M v) hsum
  rw [hR] at hv
  simp only [add_apply, zero_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at hv
  set η := iteratedFDeriv ℝ j Ξ x0 v with hη
  have h2 : η + continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η =
      -(R v) := by
    have : η + (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η + R v) = 0 :=
      hv
    rw [← add_assoc] at this
    exact eq_neg_of_add_eq_zero_left this
  have h3 := sup_gronwall hS hΛ
    (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1))
    (fc_V_bound hS hb (Ξ x0)) η (-(R v)) h2
  rw [norm_neg] at h3
  refine h3.trans ?_
  calc Real.exp (Λ * S) * ‖R v‖ ≤ Real.exp (Λ * S) * (‖R‖ * ∏ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm v) (Real.exp_pos _).le
    _ ≤ Real.exp (Λ * S) * ((Fintype.card (OrderedFinpartition j) *
          (Bt * K ^ j * ω ^ (σ + (j : ℝ)))) * ∏ i, ‖v i‖) := by
        gcongr
    _ = M * ∏ i, ‖v i‖ := by rw [hM]; ring

/-- The weighted induction (analogue of `fc_induction`): `‖D^iΞ(x₀)‖ ≤ C Bt^P ω^{e(i)}` for
`1 ≤ i ≤ n ≤ m+1`, with `C, P` depending only on `m, T, Λ`; `Bt ≥ 1` is the constant of `htay`. -/
theorem lc2_induction (m : ℕ) (T Λ : ℝ) :
    ∀ n : ℕ, n ≤ m + 1 → ∃ C : ℝ, 1 ≤ C ∧ ∃ P : ℕ, ∀ S : ℝ, 0 ≤ S → S ≤ T → ∀ b : ℝ → E → E,
      DB S m Λ b → ∀ Ξ : E → (ℝ →ᵇ E), ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ →
      (∀ x, Gmap S b (Ξ x) = constCLM E x) → ∀ (x0 : E) (σ ω Bt : ℝ), 0 ≤ σ → 0 < ω → ω ≤ 1 →
      1 ≤ Bt → (∀ k : ℕ, 2 ≤ k → k ≤ m + 1 → ‖tay S b (Ξ x0) k‖ ≤ Bt * ω ^ (σ + (k : ℝ))) →
      ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Ξ x0‖ ≤ C * Bt ^ P * ω ^ (lc2_e σ i) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨1, le_rfl, 0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ i h1 h2 => by omega⟩
  | succ n ih =>
    intro hn
    obtain ⟨C, hC1, P, hCP⟩ := ih (by omega)
    set C' : ℝ := max (max C (Real.exp (Λ * T)))
      (Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) * C ^ (n + 1))) with hC'
    set P' : ℕ := 1 + P * (n + 1) with hP'
    have hC'1 : 1 ≤ C' := hC1.trans ((le_max_left _ _).trans (le_max_left _ _))
    refine ⟨C', hC'1, P', ?_⟩
    intro S hS0 hST b hb Ξ hΞ hG x0 σ ω Bt hσ hω0 hω1 hBt htay i hi1 hi2
    have hΛ := hb.Λ_nonneg hS0
    have hexp : Real.exp (Λ * S) ≤ Real.exp (Λ * T) := Real.exp_le_exp.2 (by gcongr)
    have hωe : 0 ≤ ω ^ (lc2_e σ i) := Real.rpow_nonneg hω0.le _
    have hPP : P ≤ P * (n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
    have hBtP : Bt ^ P ≤ Bt ^ P' := pow_le_pow_right₀ hBt (by omega)
    have hBt1 : 1 ≤ Bt ^ P' := one_le_pow₀ hBt
    by_cases hin : i ≤ n
    · have := hCP S hS0 hST b hb Ξ hΞ hG x0 σ ω Bt hσ hω0 hω1 hBt htay i hi1 hin
      refine this.trans ?_
      have hCC : C ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
      gcongr
    · have hi : i = n + 1 := by omega
      subst hi
      by_cases hn0 : n = 0
      · subst hn0
        rw [norm_iteratedFDeriv_one (𝕜 := ℝ), lc2_e_one, Real.rpow_zero, mul_one]
        refine ((fc_base hS0 hb hΞ hG x0).trans hexp).trans ?_
        have : Real.exp (Λ * T) ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
        calc Real.exp (Λ * T) ≤ C' * 1 := by linarith
          _ ≤ C' * Bt ^ P' := by gcongr
      · set K : ℝ := C * Bt ^ P with hK
        have hK1 : 1 ≤ K := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hBt)
        have hlow : ∀ i : ℕ, 1 ≤ i → i < n + 1 → ‖iteratedFDeriv ℝ i Ξ x0‖ ≤ K * ω ^ (lc2_e σ i) :=
          fun i h1 h2 => hCP S hS0 hST b hb Ξ hΞ hG x0 σ ω Bt hσ hω0 hω1 hBt htay i h1 (by omega)
        have hstep := lc2_step hS0 hb hΞ hG (j := n + 1) (by omega) hn x0 hK1 (by linarith) hσ hω0
          hω1 hlow (fun k hk1 hkj => htay k hk1 (hkj.trans hn))
        refine hstep.trans ?_
        have hne : n + 1 ≠ 1 := by omega
        rw [lc2_e_of_ne hne]
        have hcard : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition (n + 1)) := by positivity
        have hω' : 0 ≤ ω ^ (σ + ((n + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hω0.le _
        have hKpow : K ^ (n + 1) = C ^ (n + 1) * Bt ^ (P * (n + 1)) := by
          rw [hK, mul_pow, ← pow_mul]
        have hCC : Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) * C ^ (n + 1)) ≤
            C' := le_max_right _ _
        calc Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition (n + 1)) *
              (Bt * K ^ (n + 1) * ω ^ (σ + ((n + 1 : ℕ) : ℝ))))
            ≤ Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) *
              (Bt * K ^ (n + 1) * ω ^ (σ + ((n + 1 : ℕ) : ℝ)))) := by gcongr
          _ = (Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) * C ^ (n + 1))) *
              Bt ^ P' * ω ^ (σ + ((n + 1 : ℕ) : ℝ)) := by
              rw [hKpow, hP', pow_add, pow_one]; ring
          _ ≤ C' * Bt ^ P' * ω ^ (σ + ((n + 1 : ℕ) : ℝ)) := by gcongr

end Step

end HRS.MS.Lc
