import HRS.MS.WhoAux5

/-!
# S54 part 6: regularity and weighted bounds of the zeroth order operators `G_k`, `G_0`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem who_cb_add {n : ℕ} {f g : Euc d → ℝ} (hf : CbCls n f) (hg : CbCls n g) :
    CbCls n (fun y => f y + g y) := by
  obtain ⟨hfc, Bf, hBf⟩ := hf
  obtain ⟨hgc, Bg, hBg⟩ := hg
  refine ⟨hfc.add hgc, Bf + Bg, fun i hi y => ?_⟩
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := i) (f := f) (g := g) (x := y)
    ((hfc.of_le (by exact_mod_cast hi)).contDiffAt) ((hgc.of_le (by exact_mod_cast hi)).contDiffAt)
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, this]
  exact (norm_add_le _ _).trans (add_le_add (hBf i hi y) (hBg i hi y))

theorem who_cb_smul {n : ℕ} {f : Euc d → ℝ} (hf : CbCls n f) (a : ℝ) : CbCls n (fun y => a * f y) := by
  obtain ⟨hfc, Bf, hBf⟩ := hf
  refine ⟨contDiff_const.mul hfc, |a| * Bf, fun i hi y => ?_⟩
  rw [who_iter_const_mul (hfc.of_le (by exact_mod_cast hi)) a y, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hBf i hi y) (abs_nonneg _)

theorem who_cb_sum {ι : Type*} (S : Finset ι) {n : ℕ} {f : ι → Euc d → ℝ} (hf : ∀ i ∈ S, CbCls n (f i)) :
    CbCls n (fun y => ∑ i ∈ S, f i y) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨contDiff_const, 0, fun i hi y => by simp [iteratedFDeriv_const_of_ne]⟩
  | insert a S ha ih =>
    have := who_cb_add (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem who_cb_mul {n : ℕ} {f φ : Euc d → ℝ} (hf : CbCls n f) (hφ : CbCls n φ) :
    CbCls n (fun y => f y * φ y) := by
  obtain ⟨hfc, Bf, hBf⟩ := hf
  obtain ⟨hφc, Bφ, hBφ⟩ := hφ
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 0 (Nat.zero_le _) 0)
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0 (Nat.zero_le _) 0)
  refine ⟨hfc.mul hφc, Bf * Bφ * 2 ^ n, fun i hi y => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hfc hφc y (by exact_mod_cast hi)).trans ?_
  calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l f y‖ * ‖iteratedFDeriv ℝ (i - l) φ y‖
      ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * Bf * Bφ := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hl' : l ≤ n := by have := Finset.mem_range.1 hl; omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hBf l hl' y) (by positivity)) (hBφ (i - l) (by omega) y)
          (norm_nonneg _) (by positivity)
    _ = Bf * Bφ * 2 ^ i := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    _ ≤ Bf * Bφ * 2 ^ n := by
        gcongr; norm_num

/-- the components of a smooth bounded vector field are in `CbCls` -/
theorem who_cb_comp {c : Euc d → Euc d} (hc : IsSmoothBounded c) (n : ℕ) (k : Fin d) :
    CbCls n (fun y => c y k) := by
  have hcd : ContDiff ℝ n c := hc.1.of_le (by exact_mod_cast le_top)
  refine ⟨(EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff.comp hcd, ?_⟩
  choose Bc hBc using hc.2
  refine ⟨∑ j ∈ Finset.range (n + 1), |Bc j|, fun i hi y => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun y => c y k) y =
      (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).compContinuousMultilinearMap (iteratedFDeriv ℝ i c y) :=
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).iteratedFDeriv_comp_left (hc.1.contDiffAt)
      (by exact_mod_cast le_top)
  rw [h1]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hp : ‖(EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simpa using PiLp.norm_apply_le v k
  calc ‖(EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ i c y‖
      ≤ 1 * |Bc i| := mul_le_mul hp ((hBc i y).trans (le_abs_self _)) (norm_nonneg _) zero_le_one
    _ ≤ _ := by
        rw [one_mul]
        exact Finset.single_le_sum (f := fun j => |Bc j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))


theorem who_cb_mono {n m : ℕ} (h : m ≤ n) {f : Euc d → ℝ} (hf : CbCls n f) : CbCls m f := by
  obtain ⟨hc, B, hB⟩ := hf
  exact ⟨hc.of_le (by exact_mod_cast h), B, fun i hi => hB i (hi.trans h)⟩

theorem who_cb_K (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + s + 3 < L) {A : ℝ} (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h) :
    CbCls k (ultK κ h) := by
  obtain ⟨C, hC0, hC⟩ := ult_core hd hK k hL
  obtain ⟨hcd, hb⟩ := hC A h hA hdec
  refine ⟨hcd, C * A, fun j hj y => (hb j hj y).trans ?_⟩
  have h1 : (1 + ‖y‖) ^ (-(s + 1 + (j : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have := hK.hs0
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  calc C * A * (1 + ‖y‖) ^ (-(s + 1 + (j : ℝ))) ≤ C * A * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * A := mul_one _

/-- the derivatives of `f₀ + ∑_j m_j f_j` in the weighted norm -/
theorem who_wSq_lin {P : ℝ} {n i : ℕ} (hi : i ≤ n) {f0 : Euc d → ℝ} (h0 : ContDiff ℝ n f0)
    {f : Fin d → Euc d → ℝ} (hf : ∀ j, ContDiff ℝ n (f j)) (m : Fin d → ℝ) :
    wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => f0 y + ∑ j, m j * f j y) x‖) ≤
      2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i f0 x‖) +
        (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal (m j ^ 2) * wSq P (fun x => ‖iteratedFDeriv ℝ i (f j) x‖)) := by
  have hmeas : ∀ j, Measurable fun x => |m j| * ‖iteratedFDeriv ℝ i (f j) x‖ := fun j =>
    measurable_const.mul ((hf j).continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.measurable
  have hpt : ∀ x, ‖iteratedFDeriv ℝ i (fun y => f0 y + ∑ j, m j * f j y) x‖ ≤
      ‖iteratedFDeriv ℝ i f0 x‖ + ∑ j, |m j| * ‖iteratedFDeriv ℝ i (f j) x‖ := by
    intro x
    have hs : (fun y => f0 y + ∑ j, m j * f j y) = f0 + ∑ j, fun y => m j * f j y := by
      funext y; simp [Finset.sum_apply]
    have hconst : ∀ j, ContDiffAt ℝ i (fun y => m j * f j y) x := fun j =>
      (contDiff_const.mul ((hf j).of_le (by exact_mod_cast hi))).contDiffAt
    have hsd : ContDiffAt ℝ i (∑ j, fun y => m j * f j y) x := by
      have := ContDiffAt.sum (s := Finset.univ) fun j _ => hconst j
      simpa only [Finset.sum_fn] using this
    rw [hs, iteratedFDeriv_add_apply (h0.of_le (by exact_mod_cast hi)).contDiffAt hsd,
      iteratedFDeriv_sum_apply (fun j _ => hconst j)]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)))
    rw [who_iter_const_mul (hf j |>.of_le (by exact_mod_cast hi)) (m j) x, norm_smul, Real.norm_eq_abs]
  have h0m : Measurable fun x => ‖iteratedFDeriv ℝ i f0 x‖ :=
    (h0.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.measurable
  calc wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => f0 y + ∑ j, m j * f j y) x‖)
      ≤ wSq P (fun x => ‖iteratedFDeriv ℝ i f0 x‖ + ∑ j, |m j| * ‖iteratedFDeriv ℝ i (f j) x‖) :=
        who_wSq_mono fun x => pow_le_pow_left₀ (norm_nonneg _) (hpt x) 2
    _ ≤ 2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i f0 x‖) +
          wSq P (fun x => ∑ j, |m j| * ‖iteratedFDeriv ℝ i (f j) x‖)) := who_wSq_add_le h0m
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (add_le_add le_rfl ?_)
        refine (who_wSq_sum_le (Finset.univ : Finset (Fin d)) hmeas).trans ?_
        rw [Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => le_of_eq ?_)
        rw [who_wSq_smul, sq_abs]


theorem who_cterm {r : ℕ} {P : ℝ} {f : Euc d → ℝ} (hf : CbCls r f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : Euc d → ℝ}, ContDiff ℝ r φ → ∀ {i : ℕ}, i ≤ r →
      wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => f y * φ y) x‖) ≤ ENNReal.ofReal C * Nsq r P φ := by
  obtain ⟨hfc, B, hB⟩ := hf
  exact ⟨(r + 1) ^ 2 * (2 ^ r * B) ^ 2, by
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
    positivity, fun {φ} hφ i hi => who_wSq_leibniz hi le_rfl hfc hφ (fun l hl y => hB l hl y)⟩

theorem who_comb_bound {a : ℝ} (hA : 0 ≤ a) (b : Fin d → ℝ) (hb : ∀ j, 0 ≤ b j) (m : Fin d → ℝ) (N : ℝ≥0∞) :
    2 * (ENNReal.ofReal a * N + (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal (m j ^ 2) * (ENNReal.ofReal (b j) * N)) =
      ENNReal.ofReal (2 * (a + d * ∑ j, m j ^ 2 * b j)) * N := by
  have h1 : ∀ j, 0 ≤ m j ^ 2 * b j := fun j => mul_nonneg (sq_nonneg _) (hb j)
  have h2 : 0 ≤ ∑ j, m j ^ 2 * b j := Finset.sum_nonneg fun j _ => h1 j
  have key : ∑ j, ENNReal.ofReal (m j ^ 2) * (ENNReal.ofReal (b j) * N) =
      (∑ j, ENNReal.ofReal (m j ^ 2) * ENNReal.ofReal (b j)) * N := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  have key2 : ENNReal.ofReal (∑ j, m j ^ 2 * b j) = ∑ j, ENNReal.ofReal (m j ^ 2) * ENNReal.ofReal (b j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => h1 j)]
    exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (sq_nonneg _)
  rw [key, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hA (by positivity),
    ENNReal.ofReal_mul (Nat.cast_nonneg d), key2, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  ring

/-- the main bounds for `G_k`, `G_0` -/
theorem who_G_main (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : Euc d → ℝ}, CbCls (r + 2) φ →
      (∀ k, CbCls (r + 1) (Gk s M ψ c k φ)) ∧ CbCls r (G0 s M ψ c φ) ∧
      (∀ k : Fin d, ∀ {i : ℕ}, i ≤ r →
        wSq P (fun x => ‖iteratedFDeriv ℝ i (Gk s M ψ c k φ) x‖) ≤ ENNReal.ofReal C * Nsq r P φ) ∧
      (∀ {i : ℕ}, i ≤ r →
        wSq P (fun x => ‖iteratedFDeriv ℝ i (G0 s M ψ c φ) x‖) ≤ ENNReal.ofReal C * Nsq r P φ) := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  have hsd : s < (d : ℝ) := by linarith
  set L : ℝ := (d : ℝ) + r + s + 5 + P with hLdef
  have hLd : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hLP : (d : ℝ) / 2 < L - P := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hLk : (d : ℝ) + (r + 1 : ℕ) + s + 3 < L := by
    push_cast
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hLk' : (d : ℝ) + (r : ℕ) + s + 3 < L := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hker := fun j : Fin d => ult_ker_kap (d := d) hs0 hsd j
  obtain ⟨A0, hA0, hψ⟩ := who_schwartz_u2dec ψ (r + 2) L
  have hψ1 : U2Dec (r + 1) L A0 (⇑ψ) := ult_U2Dec_mono hψ (by omega)
  -- constants of the K-terms
  choose CK1 hCK1 hK1 using fun j : Fin d => who_Kprod hd hP0 hP (hker j) hs1 r hLP hLd hA0
  choose CK2 hCK2 hK2 using fun j : Fin d => who_Kprod hd hP0 hP (hker j) hs1 r hLP hLd
    (A := A0 * ‖ul1w M j‖) (by positivity)
  -- the c-terms
  have hcomp : ∀ k : Fin d, CbCls (r + 1) (fun y => c y k) := fun k => who_cb_comp hc (r + 1) k
  have hdivcb : CbCls r (fun x => ∑ k : Fin d, fderiv ℝ (fun y => c y k) x (EuclideanSpace.single k 1)) :=
    who_cb_sum _ fun k _ => who_dir_cb (hcomp k) _
  have hneg : CbCls r (fun x => -(∑ k : Fin d, fderiv ℝ (fun y => c y k) x (EuclideanSpace.single k 1))) := by
    have := who_cb_smul hdivcb (-1)
    simpa using this
  choose Cc hCc hcterm using fun k : Fin d => who_cterm (P := P) (who_cb_mono (Nat.le_succ r) (hcomp k))
  obtain ⟨Cdv, hCdv, hdvterm⟩ := who_cterm (P := P) hneg
  set CGk : ℝ := 2 * ((∑ k, Cc k) + d * ∑ j, ((∑ k, M k j ^ 2) * CK1 j)) with hCGk
  set CG0 : ℝ := 2 * (Cdv + d * ∑ j, CK2 j) with hCG0
  have hCGk0 : 0 ≤ CGk := by
    have h1 : 0 ≤ ∑ k, Cc k := Finset.sum_nonneg fun k _ => hCc k
    have h2 : 0 ≤ ∑ j, ((∑ k, M k j ^ 2) * CK1 j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (hCK1 j)
    rw [hCGk]; positivity
  have hCG00 : 0 ≤ CG0 := by
    have h2 : 0 ≤ ∑ j, CK2 j := Finset.sum_nonneg fun j _ => hCK2 j
    rw [hCG0]; positivity
  refine ⟨CGk + CG0, add_nonneg hCGk0 hCG00, fun {φ} hφ => ?_⟩
  have hφ1 : CbCls (r + 1) φ := who_cb_mono (by omega) hφ
  have hφ0 : CbCls r φ := who_cb_mono (by omega) hφ
  obtain ⟨Aφ, hAφ, hdecA⟩ := who_dec_prod ψ hφ L
  have hKreg : ∀ j, CbCls (r + 1) (Kc s j (fun y => ψ y * φ y)) := fun j =>
    who_cb_K hd (hker j) (r + 1) hLk hAφ hdecA
  have hKreg0 : ∀ j, CbCls r (Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y)) := fun j => by
    obtain ⟨A', hA', hdec'⟩ := who_dec_dirprod ψ hφ1 L (ul1w M j)
    exact who_cb_K hd (hker j) r hLk' hA' hdec'
  have hGk_eq : ∀ k, Gk s M ψ c k φ =
      fun y => c y k * φ y + ∑ j, (-(M k j)) * Kc s j (fun y => ψ y * φ y) y := by
    intro k; funext y; unfold Gk
    simp [sub_eq_add_neg, Finset.sum_neg_distrib, neg_mul]
  have hG0_eq : G0 s M ψ c φ = fun y => (-(∑ k : Fin d, fderiv ℝ (fun y => c y k) y (EuclideanSpace.single k 1))) * φ y +
      ∑ j, (1 : ℝ) * Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y) y := by
    funext y; unfold G0; simp
  refine ⟨fun k => ?_, ?_, fun k {i} hi => ?_, fun {i} hi => ?_⟩
  · rw [hGk_eq k]
    exact who_cb_add (who_cb_mul (hcomp k) hφ1 |> who_cb_mono le_rfl)
      (who_cb_sum _ fun j _ => who_cb_smul (hKreg j) _)
  · rw [hG0_eq]
    exact who_cb_add (who_cb_mul hneg hφ0) (who_cb_sum _ fun j _ => who_cb_smul (hKreg0 j) _)
  · rw [hGk_eq k]
    have hlin := who_wSq_lin (P := P) (n := r) (i := i) hi
      ((who_cb_mul (who_cb_mono (Nat.le_succ r) (hcomp k)) hφ0).1)
      (f := fun j y => Kc s j (fun y => ψ y * φ y) y)
      (fun j => ((hKreg j).1.of_le (by exact_mod_cast Nat.le_succ r))) (fun j => -(M k j))
    refine hlin.trans ?_
    have hterm0 := (hcterm k) hφ0.1 hi
    have hK : ∀ j, wSq P (fun x => ‖iteratedFDeriv ℝ i (Kc s j (fun y => ψ y * φ y)) x‖) ≤
        ENNReal.ofReal (CK1 j) * Nsq r P φ := fun j => hK1 j hψ1 hφ1 hi
    calc 2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => c y k * φ y) x‖) +
          (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((-(M k j)) ^ 2) *
            wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => Kc s j (fun y => ψ y * φ y) y) x‖))
        ≤ 2 * (ENNReal.ofReal (Cc k) * Nsq r P φ + (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((-(M k j)) ^ 2) *
            (ENNReal.ofReal (CK1 j) * Nsq r P φ)) := by
          gcongr with j
          exact hK j
      _ = ENNReal.ofReal (2 * (Cc k + d * ∑ j, (-(M k j)) ^ 2 * CK1 j)) * Nsq r P φ :=
          who_comb_bound (hCc k) CK1 hCK1 _ _
      _ ≤ ENNReal.ofReal (CGk + CG0) * Nsq r P φ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have h1 : Cc k ≤ ∑ k, Cc k :=
            Finset.single_le_sum (f := Cc) (fun k _ => hCc k) (Finset.mem_univ k)
          have h2 : ∑ j, (-(M k j)) ^ 2 * CK1 j ≤ ∑ j, ((∑ k, M k j ^ 2) * CK1 j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [neg_sq]
            exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun k => M k j ^ 2)
              (fun k _ => sq_nonneg _) (Finset.mem_univ k)) (hCK1 j)
          have : 2 * (Cc k + d * ∑ j, (-(M k j)) ^ 2 * CK1 j) ≤ CGk := by
            rw [hCGk]; gcongr
          linarith
  · rw [hG0_eq]
    have hlin := who_wSq_lin (P := P) (n := r) (i := i) hi
      ((who_cb_mul hneg hφ0).1)
      (f := fun j y => Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y) y)
      (fun j => (hKreg0 j).1) (fun j => 1)
    refine hlin.trans ?_
    have hterm0 := hdvterm hφ0.1 hi
    have hK : ∀ j, wSq P (fun x => ‖iteratedFDeriv ℝ i (Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y)) x‖) ≤
        ENNReal.ofReal (CK2 j) * Nsq r P φ := fun j =>
      hK2 j (who_u2dec_dir hψ (ul1w M j)) hφ1 hi
    calc 2 * (wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => (-(∑ k : Fin d, fderiv ℝ (fun y => c y k) y
              (EuclideanSpace.single k 1))) * φ y) x‖) +
          (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((1 : ℝ) ^ 2) *
            wSq P (fun x => ‖iteratedFDeriv ℝ i (fun y => Kc s j (fun y => fderiv ℝ ψ y (ul1w M j) * φ y) y) x‖))
        ≤ 2 * (ENNReal.ofReal Cdv * Nsq r P φ + (d : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((1 : ℝ) ^ 2) *
            (ENNReal.ofReal (CK2 j) * Nsq r P φ)) := by
          gcongr with j
          exact hK j
      _ = ENNReal.ofReal (2 * (Cdv + d * ∑ j, (1 : ℝ) ^ 2 * CK2 j)) * Nsq r P φ :=
          who_comb_bound hCdv CK2 hCK2 (fun _ => 1) _
      _ ≤ ENNReal.ofReal (CGk + CG0) * Nsq r P φ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have : 2 * (Cdv + d * ∑ j, (1 : ℝ) ^ 2 * CK2 j) = CG0 := by
            rw [hCG0]; simp
          linarith

end HRS.MS.Who
