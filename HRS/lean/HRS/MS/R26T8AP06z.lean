import HRS.MS.R26T8AP06y

/-!
# S8.2 Taylor split (T), step C1: bounds for the nested jets of the polynomial part
`r26t8a_diag_jet_bound`: `‖D^q (w ↦ B(w,…,w)) z‖ <= n!/(n-q)! ‖B‖ ‖z‖^(n-q)`.
`r26t8a_nest_Pfull_bound`: for `|z| <= 2`, `‖nest p q Pfull X z‖ <= (m+1) 2^m BX` if `‖D^p c ℓ X‖ <= BX` for `ℓ <= m`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_diag_jet_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (q : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ q (fun w : E => B (fun _ => w)) z‖ ≤ (n.descFactorial q : ℝ) * ‖B‖ * ‖z‖ ^ (n - q) := by
  set g : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E) with hg
  have hfun : (fun w : E => B (fun _ => w)) = B ∘ g := by funext w; rfl
  have hgn : ∀ w : E, ‖g w‖ ≤ ‖w‖ := fun w => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => le_rfl
  have hg1 : ‖g‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    simpa using hgn w
  rw [hfun]
  refine (r26t8a_norm_comp_clm g (B.contDiff (n := (q : WithTop ℕ∞))) z le_rfl).trans ?_
  have h1 := B.norm_iteratedFDeriv_le q (g z)
  rw [Fintype.card_fin] at h1
  have h2 : ‖g z‖ ^ (n - q) ≤ ‖z‖ ^ (n - q) := pow_le_pow_left₀ (norm_nonneg _) (hgn z) _
  have h3 : ‖g‖ ^ q ≤ 1 := pow_le_one₀ (norm_nonneg _) hg1
  have h0 : 0 ≤ ((n.descFactorial q : ℕ) : ℝ) * ‖B‖ := by positivity
  calc ‖iteratedFDeriv ℝ q B (g z)‖ * ‖g‖ ^ q ≤ ‖iteratedFDeriv ℝ q B (g z)‖ * 1 :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ (n.descFactorial q : ℝ) * ‖B‖ * ‖g z‖ ^ (n - q) := by rw [mul_one]; exact h1
    _ ≤ (n.descFactorial q : ℝ) * ‖B‖ * ‖z‖ ^ (n - q) := mul_le_mul_of_nonneg_left h2 h0

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_nest_Pfull_bound {d : ℕ} (m k : ℕ)
    (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    (hc : ∀ ℓ ≤ m, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (c ℓ)) (p q : ℕ) (hpq : p + q ≤ k + 1)
    (X z : Euc d) (hz : ‖z‖ ≤ 2) (BX : ℝ) (hBX : ∀ ℓ ≤ m, ‖iteratedFDeriv ℝ p (c ℓ) X‖ ≤ BX) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z‖ ≤ (m + 1) * 2 ^ m * BX := by
  have hB0 : 0 ≤ BX := (norm_nonneg _).trans (hBX 0 (Nat.zero_le _))
  have hPf : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) :=
    r26t8a_Pfull_contDiff m c hc
  have hPf' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) :=
    hPf.of_le (by exact_mod_cast hpq)
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun u => ?_
  set Λ : (ℓ : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ :=
    fun ℓ => iteratedFDeriv ℝ p (c ℓ) X u with hΛ
  set hP : Euc d → ℝ := fun w => ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w) with hhP
  have hnestP : (r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z) u =
      iteratedFDeriv ℝ q hP z := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [r26t8a_nest_swap p q hPf' X z u v]
    have hfun : (fun z' : Euc d => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
        (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) (X, z')) = hP := by
      funext z'
      have hlen : ContDiff ℝ (((List.ofFn u).length : ℕ) : WithTop ℕ∞)
          (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) := by
        rw [List.length_ofFn]; exact hPf.of_le (by exact_mod_cast (by omega : p ≤ k + 1))
      rw [r26t8a_iterDir_inl (List.ofFn u) hlen X z']
      have hcdY : ContDiff ℝ (p : WithTop ℕ∞) (fun Y : Euc d => r26t8a_Pfull m c Y z') :=
        (hPf.comp (contDiff_id.prodMk contDiff_const : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          fun Y : Euc d => (Y, z'))).of_le (by exact_mod_cast (by omega : p ≤ k + 1))
      rw [← r26t8a_iteratedFDeriv_eq_iterDir p _ hcdY X u,
        r26t8a_Pfull_word m c (fun ℓ hℓ => (hc ℓ hℓ).of_le (by exact_mod_cast (by omega : p ≤ k + 1))) X z' u]
    rw [hfun]
  rw [hnestP]
  have hcdℓ : ∀ ℓ, ContDiff ℝ (q : WithTop ℕ∞) (fun w : Euc d => (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) := fun ℓ =>
    contDiff_const.mul (r26t8a_cmm_diag_contDiff (X := Euc d) ℓ (fun _ => Λ ℓ) (fun w => w) contDiff_const contDiff_id)
  have hsum : iteratedFDeriv ℝ q hP z = ∑ ℓ ∈ Finset.range (m + 1),
      iteratedFDeriv ℝ q (fun w : Euc d => (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) z :=
    iteratedFDeriv_fun_sum_apply (fun ℓ _ => (hcdℓ ℓ).contDiffAt)
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hprod : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hterm : ∀ ℓ ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ q (fun w : Euc d => (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) z‖ ≤ 2 ^ m * BX * ∏ i, ‖u i‖ := by
    intro ℓ hℓ
    have hℓm : ℓ ≤ m := by rw [Finset.mem_range] at hℓ; omega
    have hcdΛ : ContDiff ℝ (q : WithTop ℕ∞) (fun w : Euc d => Λ ℓ (fun _ => w)) :=
      r26t8a_cmm_diag_contDiff (X := Euc d) ℓ (fun _ => Λ ℓ) (fun w => w) contDiff_const contDiff_id
    have e : iteratedFDeriv ℝ q (fun w : Euc d => (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) z =
        (1 / (ℓ.factorial : ℝ)) • iteratedFDeriv ℝ q (fun w : Euc d => Λ ℓ (fun _ => w)) z :=
      iteratedFDeriv_const_smul_apply' (a := 1 / (ℓ.factorial : ℝ)) hcdΛ.contDiffAt
    rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := r26t8a_diag_jet_bound (Λ ℓ) q z
    have hΛn : ‖Λ ℓ‖ ≤ BX * ∏ i, ‖u i‖ :=
      ((iteratedFDeriv ℝ p (c ℓ) X).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hBX ℓ hℓm) hprod)
    have hdf : (ℓ.descFactorial q : ℝ) ≤ ℓ.factorial := by
      have : ℓ.descFactorial q ≤ ℓ.factorial := by
        by_cases hqℓ : q ≤ ℓ
        · rw [← Nat.factorial_mul_descFactorial hqℓ]
          exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
        · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]; exact Nat.zero_le _
      exact_mod_cast this
    have hfpos : (0 : ℝ) < ℓ.factorial := by positivity
    have hz2 : ‖z‖ ^ (ℓ - q) ≤ 2 ^ m :=
      (pow_le_pow_left₀ (norm_nonneg _) hz _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hΛ0 : 0 ≤ ‖Λ ℓ‖ := norm_nonneg _
    calc 1 / (ℓ.factorial : ℝ) * ‖iteratedFDeriv ℝ q (fun w : Euc d => Λ ℓ (fun _ => w)) z‖
        ≤ 1 / (ℓ.factorial : ℝ) * ((ℓ.descFactorial q : ℝ) * ‖Λ ℓ‖ * ‖z‖ ^ (ℓ - q)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / (ℓ.factorial : ℝ) * ((ℓ.factorial : ℝ) * ‖Λ ℓ‖ * 2 ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hdf hΛ0) hz2 (by positivity) (by positivity)
      _ = ‖Λ ℓ‖ * 2 ^ m := by field_simp
      _ ≤ (BX * ∏ i, ‖u i‖) * 2 ^ m := mul_le_mul_of_nonneg_right hΛn (by positivity)
      _ = 2 ^ m * BX * ∏ i, ‖u i‖ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linarith

end HRS.MS.R26T8A
