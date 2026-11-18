import HRS.MS.WhoAux4
import HRS.MS.UlNl

/-!
# S54 part 5: the splitting `N φ = ∑_k ∂_k G_k φ + G_0 φ` of the perturbation `ulPert` into zeroth order operators
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- component `j` of the cancellation convolution `∇g * h` -/
def Kc (s : ℝ) (j : Fin d) (h : Euc d → ℝ) : Euc d → ℝ := ultK (u2_kap d s j) h

/-- `G_k φ = c_k φ - ∑_j M_{kj} K_j(ρ φ)` -/
def Gk (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d) (k : Fin d)
    (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  c x k * φ x - ∑ j, M k j * Kc s j (fun y => ρ y * φ y) x

/-- `G_0 φ = -(div c) φ + ∑_j K_j((∂_{w_j} ρ) φ)` -/
def G0 (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d)
    (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(∑ k, fderiv ℝ (fun y => c y k) x (EuclideanSpace.single k 1)) * φ x +
    ∑ j, Kc s j (fun y => fderiv ℝ ρ y (ul1w M j) * φ y) x

theorem who_dir_cb {n : ℕ} {φ : Euc d → ℝ} (hφ : CbCls (n + 1) φ) (v : Euc d) :
    CbCls n (fun y => fderiv ℝ φ y v) := by
  obtain ⟨hc, B, hB⟩ := hφ
  have hd1 : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ φ) :=
    hc.fderiv_right (by exact_mod_cast le_refl (n + 1))
  refine ⟨hd1.clm_apply contDiff_const, B * ‖v‖, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := (n : WithTop ℕ∞)) (c := v) (n := m)
    hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) φ y‖ ≤ ‖v‖ * B :=
        mul_le_mul_of_nonneg_left (hB (m + 1) (by omega) y) (norm_nonneg _)
    _ = _ := by ring

/-- derivative of the cancellation convolution in a direction -/
theorem who_K_fderiv (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec 2 L A h) (v x : Euc d) :
    DifferentiableAt ℝ (ultK κ h) x ∧
      fderiv ℝ (ultK κ h) x v = ultK κ (fun y => fderiv ℝ h y v) x := by
  obtain ⟨-, hcd⟩ := ult_K_iter hd hK hL hA (k := 1) hdec
  refine ⟨(hcd.differentiable (by norm_num)) x, ?_⟩
  have := ult_K_iter_apply hd hK hL hA (k := 1) hdec (m := 1) le_rfl (fun _ => v) x
  simpa only [iteratedFDeriv_one_apply] using this


theorem who_dec_prod (ψ : SchwartzMap (Euc d) ℝ) {n : ℕ} {φ : Euc d → ℝ} (hφ : CbCls n φ) (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ U2Dec n L A (fun y => ψ y * φ y) := by
  obtain ⟨hc, B, hB⟩ := hφ
  obtain ⟨A0, hA0, hψ⟩ := who_schwartz_u2dec ψ n L
  refine ⟨A0 * B * 2 ^ n, ?_, who_u2dec_mul hψ hc hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  positivity

theorem who_dec_dirprod (ψ : SchwartzMap (Euc d) ℝ) {n : ℕ} {φ : Euc d → ℝ} (hφ : CbCls n φ) (L : ℝ)
    (w : Euc d) : ∃ A : ℝ, 0 ≤ A ∧ U2Dec n L A (fun y => fderiv ℝ ψ y w * φ y) := by
  obtain ⟨hc, B, hB⟩ := hφ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  obtain ⟨A0, hA0, hψ⟩ := who_schwartz_u2dec ψ (n + 1) L
  refine ⟨A0 * ‖w‖ * B * 2 ^ n, by positivity, who_u2dec_mul (who_u2dec_dir hψ w) hc hB⟩

theorem who_dec_prod_dir (ψ : SchwartzMap (Euc d) ℝ) {n : ℕ} {φ : Euc d → ℝ} (hφ : CbCls (n + 1) φ)
    (L : ℝ) (w : Euc d) :
    ∃ A : ℝ, 0 ≤ A ∧ U2Dec n L A (fun y => ψ y * fderiv ℝ φ y w) :=
  who_dec_prod ψ (who_dir_cb hφ w) L


theorem who_u2dec_add {n : ℕ} {L A A' : ℝ} {f g : Euc d → ℝ} (hf : U2Dec n L A f) (hg : U2Dec n L A' g) :
    U2Dec n L (A + A') (fun y => f y + g y) := by
  refine ⟨hf.1.add hg.1, fun m hm y => ?_⟩
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := m) (f := f) (g := g) (x := y)
    ((hf.1.of_le (by exact_mod_cast hm)).contDiffAt) ((hg.1.of_le (by exact_mod_cast hm)).contDiffAt)
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, this]
  calc ‖iteratedFDeriv ℝ m f y + iteratedFDeriv ℝ m g y‖ ≤ ‖iteratedFDeriv ℝ m f y‖ + ‖iteratedFDeriv ℝ m g y‖ :=
        norm_add_le _ _
    _ ≤ A * u2Wt L y + A' * u2Wt L y := add_le_add (hf.2 m hm y) (hg.2 m hm y)
    _ = _ := by ring

/-- the splitting of the perturbation -/
theorem who_decomp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {φ : Euc d → ℝ}
    (hφ : CbCls 3 φ) (x : Euc d) :
    ulPert s M ψ c φ x =
      ∑ k, fderiv ℝ (Gk s M ψ c k φ) x (EuclideanSpace.single k 1) + G0 s M ψ c φ x := by
  have hL : (d : ℝ) < (d : ℝ) + 1 := by linarith
  set L : ℝ := (d : ℝ) + 1 with hLdef
  have hker := fun j : Fin d => ult_ker_kap (d := d) hs0 hsd j
  have hφ3 : ContDiff ℝ 3 φ := by simpa using hφ.1
  have hφ1 : ContDiff ℝ 1 φ := hφ3.of_le (by norm_num)
  have hdφ : DifferentiableAt ℝ φ x := hφ1.differentiable one_ne_zero x
  -- decay data
  obtain ⟨A1, hA1, hdec1⟩ := who_dec_prod ψ hφ L
  have hdec1' : U2Dec 2 L A1 (fun y => ψ y * φ y) := ult_U2Dec_mono hdec1 (by norm_num)
  -- (a) the nonlocal term
  have ha : ulNL s M ψ φ x = ∑ j, Kc s j (fun y => ψ y * fderiv ℝ φ y (ul1w M j)) x := by
    unfold ulNL Kc
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfun : (fun y => ψ y * (Torus.matVec M.transpose (gradient φ y)) j) =
        fun y => ψ y * fderiv ℝ φ y (ul1w M j) := by
      funext y; rw [ul1_matVec]
    rw [show (fun y => (⇑ψ) y * (Torus.matVec M.transpose (gradient φ y)) j) =
        fun y => ψ y * fderiv ℝ φ y (ul1w M j) from hfun]
    obtain ⟨A, hA, hdec⟩ := who_dec_prod_dir ψ (n := 1) (φ := φ) (by
      refine ⟨hφ3.of_le (by norm_num), ?_⟩
      obtain ⟨-, B, hB⟩ := hφ
      exact ⟨B, fun i hi => hB i (by omega)⟩) L (ul1w M j)
    exact (ult_conv_comp hd hs0 hsd hL hA hdec x).2 j
  -- (b) the splitting of each term
  have hb : ∀ j : Fin d, Kc s j (fun y => ψ y * fderiv ℝ φ y (ul1w M j)) x =
      fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x (ul1w M j) -
        Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y) x := by
    intro j
    obtain ⟨A2, hA2, hdec2⟩ := who_dec_dirprod ψ hφ L (ul1w M j)
    have hdec2' : U2Dec 1 L A2 (fun y => fderiv ℝ ψ y (ul1w M j) * φ y) := ult_U2Dec_mono hdec2 (by norm_num)
    have hdec1'' : U2Dec 1 L A1 (fun y => ψ y * φ y) := ult_U2Dec_mono hdec1 (by norm_num)
    have hpd : (fun y => fderiv ℝ (fun y => ψ y * φ y) y (ul1w M j)) =
        fun y => (fderiv ℝ ψ y (ul1w M j) * φ y + ψ y * fderiv ℝ φ y (ul1w M j)) := by
      funext y
      have hψd : DifferentiableAt ℝ ψ y := (ψ.smooth 1).differentiable one_ne_zero y
      have hφd : DifferentiableAt ℝ φ y := hφ1.differentiable one_ne_zero y
      have h' : HasFDerivAt (fun y => ψ y * φ y) _ y := hψd.hasFDerivAt.mul hφd.hasFDerivAt
      rw [h'.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have hK := (who_K_fderiv hd (hker j) hL hA1 hdec1' (ul1w M j) x).2
    unfold Kc
    rw [hK, hpd]
    have hsub : (fun y => ψ y * fderiv ℝ φ y (ul1w M j)) = fun y =>
        (fderiv ℝ ψ y (ul1w M j) * φ y + ψ y * fderiv ℝ φ y (ul1w M j)) - fderiv ℝ ψ y (ul1w M j) * φ y := by
      funext y; ring
    rw [hsub]
    obtain ⟨A3, hA3, hdec3⟩ := who_dec_prod_dir ψ (n := 1) (φ := φ) (by
      refine ⟨hφ3.of_le (by norm_num), ?_⟩
      obtain ⟨-, B, hB⟩ := hφ
      exact ⟨B, fun i hi => hB i (by omega)⟩) L (ul1w M j)
    have hsum : U2Dec 1 L (A2 + A3) (fun y => fderiv ℝ ψ y (ul1w M j) * φ y + ψ y * fderiv ℝ φ y (ul1w M j)) :=
      who_u2dec_add hdec2' (ult_U2Dec_mono hdec3 (by norm_num))
    exact ult_K_sub hd (hker j) hL (by positivity) hA2 hsum hdec2' x
  -- (c) derivative of `G_k φ`
  have hKd : ∀ j : Fin d, DifferentiableAt ℝ (Kc s j (fun y => ψ y * φ y)) x := fun j =>
    (who_K_fderiv hd (hker j) hL hA1 hdec1' 0 x).1
  have hck : ∀ k : Fin d, DifferentiableAt ℝ (fun y => c y k) x := fun k =>
    ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff.comp (hc.1.of_le (by exact_mod_cast le_top))).differentiable
      one_ne_zero x
  have hGk : ∀ k : Fin d, fderiv ℝ (Gk s M ψ c k φ) x (EuclideanSpace.single k 1) =
      fderiv ℝ (fun y => c y k) x (EuclideanSpace.single k 1) * φ x + c x k * fderiv ℝ φ x (EuclideanSpace.single k 1) -
        ∑ j, M k j * fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x (EuclideanSpace.single k 1) := by
    intro k
    have h1 : HasFDerivAt (fun y => c y k * φ y)
        (c x k • fderiv ℝ φ x + φ x • fderiv ℝ (fun y => c y k) x) x :=
      (hck k).hasFDerivAt.mul hdφ.hasFDerivAt
    have h2 : HasFDerivAt (fun y => ∑ j, M k j * Kc s j (fun y => ψ y * φ y) y)
        (∑ j, M k j • fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x) x :=
      HasFDerivAt.fun_sum fun j _ => ((hKd j).hasFDerivAt).const_mul (M k j)
    have h3 : HasFDerivAt (fun y => c y k * φ y - ∑ j, M k j * Kc s j (fun y => ψ y * φ y) y)
        ((c x k • fderiv ℝ φ x + φ x • fderiv ℝ (fun y => c y k) x) -
          ∑ j, M k j • fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x) x := h1.sub h2
    have e : Gk s M ψ c k φ = fun y => c y k * φ y - ∑ j, M k j * Kc s j (fun y => ψ y * φ y) y := rfl
    rw [e, h3.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]
    ring
  have hw : ∀ (f : Euc d → ℝ) (j : Fin d), ∑ k, M k j * fderiv ℝ f x (EuclideanSpace.single k 1) =
      fderiv ℝ f x (ul1w M j) := by
    intro f j
    unfold ul1w
    simp [map_sum, map_smul]
  -- assemble
  unfold ulPert G0
  rw [ha, ul4_inner_grad]
  simp only [hb, hGk, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ k, ∑ j, M k j * fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x (EuclideanSpace.single k 1) =
      ∑ j, fderiv ℝ (Kc s j (fun y => ψ y * φ y)) x (ul1w M j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hw _ j
  rw [hswap]
  simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
  ring


/-- weighted bound for the derivatives of `K(fφ)` -/
theorem who_Kprod (hd : 1 ≤ d) {P : ℝ} (hP : 0 ≤ P) (hPd : (d : ℝ) / 2 < P) {κ : Euc d → ℝ} {s : ℝ}
    (hK : UlKer κ s) (hs1 : s + 1 < d) (r : ℕ) {L : ℝ} (hLP : (d : ℝ) / 2 < L - P) (hLd : (d : ℝ) < L)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f φ : Euc d → ℝ}, U2Dec (r + 1) L A f → CbCls (r + 1) φ → ∀ {i : ℕ}, i ≤ r →
      wSq P (fun x => ‖iteratedFDeriv ℝ i (ultK κ (fun y => f y * φ y)) x‖) ≤
        ENNReal.ofReal C * Nsq r P φ := by
  have hL0 : (0 : ℝ) ≤ L := by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
  have hMρ := who_rhoMass_lt_top (d := d) hP hLP
  have hWm := who_wtMass_lt_top (d := d) hPd
  choose C0 hC00 hC0 using fun i : ℕ => who_K_deriv_wSq hd hP hPd hK hs1 i
  set Mρ := ∫⁻ y : Euc d, ENNReal.ofReal (u2Wt L y ^ 2 * jbracket y ^ (2 * P)) with hMρdef
  set a1 : ℝ := ((r : ℝ) + 1) ^ 2 * (2 ^ r * A) ^ 2 with ha1
  set a2 : ℝ := ((r : ℝ) + 1) * 2 ^ (r + 1) * (2 ^ r * A) ^ 2 with ha2
  set Γ : ℝ≥0∞ := ENNReal.ofReal a1 + ENNReal.ofReal a2 * Mρ * wtMass (d := d) P with hΓ
  have hΓt : Γ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMρ) hWm⟩
  refine ⟨(∑ i ∈ Finset.range (r + 1), C0 i) * Γ.toReal,
    mul_nonneg (Finset.sum_nonneg fun i _ => hC00 i) ENNReal.toReal_nonneg, fun {f φ} hf hφ i hi => ?_⟩
  obtain ⟨hφc, B, hB⟩ := hφ
  have hdec : U2Dec (r + 1) L (A * B * 2 ^ (r + 1)) (fun y => f y * φ y) := who_u2dec_mul hf hφc hB
  have hA' : 0 ≤ A * B * 2 ^ (r + 1) := by
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
    positivity
  refine (hC0 i hLd hA' hdec hi).trans ?_
  have hX : wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => f y * φ y) x‖) ≤ ENNReal.ofReal a1 * Nsq r P φ :=
    who_wSq_leibniz hi (Nat.le_succ r) hf.1 hφc (Af := A) (fun l hl y =>
      (hf.2 l hl y).trans (by
        have := u2Wt_le_one hL0 y
        have hA0 : 0 ≤ A := by
          have := (norm_nonneg _).trans (hf.2 0 (Nat.zero_le _) 0)
          exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
        nlinarith))
  have hY : (∫⁻ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => f y * φ y) y‖) ^ 2 ≤
      ENNReal.ofReal a2 * Mρ * Nsq r P φ := by
    refine (who_L1_leibniz hP hLP hf hφc (by omega)).trans ?_
    have hA0 : 0 ≤ A := by
      have := (norm_nonneg _).trans (hf.2 0 (Nat.zero_le _) 0)
      exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
    have hc : ((i : ℝ) + 1) * 2 ^ (i + 1) * (2 ^ i * A) ^ 2 ≤ a2 := by
      have h1 : ((i : ℝ) + 1) ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hi
      have h2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ i * A ≤ 2 ^ r * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hA0
      have h4 : (2 ^ i * A) ^ 2 ≤ (2 ^ r * A) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      rw [ha2]
      gcongr
    calc ENNReal.ofReal (((i : ℝ) + 1) * 2 ^ (i + 1) * (2 ^ i * A) ^ 2) * Mρ * Nsq i P φ
        ≤ ENNReal.ofReal a2 * Mρ * Nsq r P φ :=
          mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl) (who_Nsq_mono hi P φ)
      _ = _ := rfl
  have hCi : ENNReal.ofReal (C0 i) ≤ ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), C0 i) :=
    ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := C0) (fun i _ => hC00 i)
      (Finset.mem_range.2 (by omega)))
  calc ENNReal.ofReal (C0 i) * (wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => f y * φ y) x‖) +
        (∫⁻ y, ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun y => f y * φ y) y‖) ^ 2 * wtMass (d := d) P)
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), C0 i) *
        (ENNReal.ofReal a1 * Nsq r P φ + (ENNReal.ofReal a2 * Mρ * Nsq r P φ) * wtMass (d := d) P) :=
        mul_le_mul' hCi (add_le_add hX (mul_le_mul' hY le_rfl))
    _ = ENNReal.ofReal ((∑ i ∈ Finset.range (r + 1), C0 i) * Γ.toReal) * Nsq r P φ := by
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hC00 i), ENNReal.ofReal_toReal hΓt.ne, hΓ]
        ring

end HRS.MS.Who
