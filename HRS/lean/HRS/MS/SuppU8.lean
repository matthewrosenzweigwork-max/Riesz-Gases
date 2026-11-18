import HRS.MS.SuppU8Aux16
import HRS.MS.SuppU8Aux18
import HRS.MS.SuppU8Aux19

/-!
# Worker U8: proofs of `HRS.Whole.fractional_decay` and `HRS.Whole.sharp_tail_bound`

Route: for `α > 0` and `ℓ = ⌊α⌋ + 1` the multiplier `(2π|ξ|)^α` is a constant multiple of
`∫ (2 - 2 cos (2π ⟪y, ξ⟫))^ℓ ‖y‖^{-d-α} dy`, i.e. `|D|^α` is the singular integral of the `ℓ`-th
central difference.  For a function with decay norm `‖v‖_{k,b}` (`k > α`, `b > 0`), the near/far
splitting of that integral gives `| |D|^α v (x) | ≲ ‖v‖_{k,b} ⟨x⟩^{-(b + α)}` pointwise (this uses only the
orders `0` and `ℓ` of the derivatives), whence the `L^p` bound for `b + α > d/p`.  The identity
`∫ v |D|^α φ = ∫ w φ` is the symmetry of the central difference (Fubini).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.Whole

variable {d : ℕ}

/-- `L^p` conclusion from a pointwise decay bound. -/
theorem u8_frac_Lp (hd1 : 1 ≤ d) (bexp α p : ℝ) (k : ℕ) (hb : 0 < bexp) (hα : 0 < α)
    (hp : 1 < p) (hk : α < k) (hbα : (d : ℝ) / p < bexp + α) :
    ∃ C : ℝ, ∀ v : Euc d → ℝ, ContDiff ℝ k v → decayNormE k bexp v < ⊤ →
      ∃ w : Euc d → ℝ, IsFracDerivRep α v w ∧ MemLp w (ENNReal.ofReal p) volume ∧
        eLpNorm w (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * decayNormE k bexp v := by
  have hp0 : 0 < p := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨b', hb'0, hb'd, hb'b, hb'α⟩ : ∃ b' : ℝ, 0 < b' ∧ b' < d ∧ b' ≤ bexp ∧
      (d : ℝ) / p < b' + α := by
    have h1 : (d : ℝ) / p < d := div_lt_self (by linarith) hp
    refine ⟨(max ((d : ℝ) / p - α) 0 + min bexp d) / 2, ?_, ?_, ?_, ?_⟩ <;>
    · have e1 : max ((d : ℝ) / p - α) 0 < min bexp d := by
        apply max_lt
        · exact lt_min (by linarith) (by linarith)
        · exact lt_min hb (by linarith)
      have e2 := le_max_left ((d : ℝ) / p - α) 0
      have e3 := le_max_right ((d : ℝ) / p - α) 0
      have e4 := min_le_left bexp (d : ℝ)
      have e5 := min_le_right bexp (d : ℝ)
      linarith
  obtain ⟨C, hC0, hcore⟩ := HRS.U8.u8_core hd1 α b' hα hb'0 hb'd
  have hγp : (d : ℝ) < (b' + α) * p := by
    have := (div_lt_iff₀ hp0).1 hb'α
    linarith
  have hmem := HRS.U8.u8_decay_memLp (d := d) (b' + α) p hp0 hγp
  have hEfin : eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-(b' + α))) (ENNReal.ofReal p) volume < ⊤ :=
    hmem.eLpNorm_lt_top
  obtain ⟨Eh, hEh⟩ : ∃ Eh : ℝ≥0∞, Eh =
      eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-(b' + α))) (ENNReal.ofReal p) volume := ⟨_, rfl⟩
  rw [← hEh] at hEfin
  refine ⟨C * u8_Cconv d k bexp * Eh.toReal, ?_⟩
  intro v hv hfin
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (decayNormE k bexp v).toReal := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact ENNReal.toReal_nonneg
  have hdN : decayNormE k bexp v = ENNReal.ofReal N := by
    rw [hN]; exact (ENNReal.ofReal_toReal hfin.ne).symm
  have hℓk : ⌊α⌋₊ + 1 ≤ k := (Nat.floor_lt hα.le).2 hk
  have hvl : ContDiff ℝ ((⌊α⌋₊ + 1 : ℕ) : WithTop ℕ∞) v := hv.of_le (by exact_mod_cast hℓk)
  have hconv := u8_conv hd1 k bexp hb.le v hfin
  have hB0 : 0 ≤ N * u8_Cconv d k bexp := mul_nonneg hN0 (u8_Cconv_nonneg _ _ _)
  have h0 : ∀ z, |v z| ≤ N * u8_Cconv d k bexp * (1 + ‖z‖) ^ (-b') := by
    intro z
    have h1 := hconv 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero, ← hN] at h1
    have h2 : (1 + ‖z‖) ^ (-(bexp + ((0 : ℕ) : ℝ))) ≤ (1 + ‖z‖) ^ (-b') :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by simp; linarith)
    rw [← Real.norm_eq_abs]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
  have h1 : ∀ z, ‖iteratedFDeriv ℝ (⌊α⌋₊ + 1) v z‖ ≤
      N * u8_Cconv d k bexp * (1 + ‖z‖) ^ (-(b' + ((⌊α⌋₊ + 1 : ℕ) : ℝ))) := by
    intro z
    have h1 := hconv (⌊α⌋₊ + 1) hℓk z
    rw [← hN] at h1
    have h2 : (1 + ‖z‖) ^ (-(bexp + (((⌊α⌋₊ + 1 : ℕ)) : ℝ))) ≤
        (1 + ‖z‖) ^ (-(b' + ((⌊α⌋₊ + 1 : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
  obtain ⟨w, hwm, hwb, hrep⟩ := hcore v (N * u8_Cconv d k bexp) hB0 hvl h0 h1
  have hCB : 0 ≤ C * (N * u8_Cconv d k bexp) := mul_nonneg hC0 hB0
  have hLp := HRS.U8.u8_decay_bound (d := d) (b' + α) p hp0 hγp (C * (N * u8_Cconv d k bexp)) hCB
    w hwm (fun x => by simpa [mul_assoc] using hwb x)
  refine ⟨w, fun φ => hrep φ, hLp.1, ?_⟩
  rw [hdN]
  calc eLpNorm w (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (C * (N * u8_Cconv d k bexp)) * Eh := by rw [hEh]; exact hLp.2
    _ = ENNReal.ofReal (C * (N * u8_Cconv d k bexp)) * ENNReal.ofReal Eh.toReal := by
        rw [ENNReal.ofReal_toReal hEfin.ne]
    _ = ENNReal.ofReal (C * (N * u8_Cconv d k bexp) * Eh.toReal) :=
        (ENNReal.ofReal_mul hCB).symm
    _ = ENNReal.ofReal (C * u8_Cconv d k bexp * Eh.toReal * N) := by congr 1; ring
    _ = ENNReal.ofReal (C * u8_Cconv d k bexp * Eh.toReal) * ENNReal.ofReal N :=
        ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC0 (u8_Cconv_nonneg _ _ _)) ENNReal.toReal_nonneg)

theorem fractional_decay_proof : type_of% @HRS.Whole.fractional_decay := by
  intro d hd bexp α p k hb hα hp hk hbα
  exact u8_frac_Lp (by omega) bexp α p k hb hα hp hk hbα

theorem u8_grad_apply (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i (1 : ℝ))
    (y := fderiv ℝ f x)
  rw [EuclideanSpace.inner_single_right] at h1
  simpa [gradient] using h1

theorem u8_grad_smooth (f : Euc d → ℝ) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiff ℝ k f) (i : Fin d) :
    ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun y => gradient f y i) := by
  have e : (fun y => gradient f y i) = fun y => fderiv ℝ f y (EuclideanSpace.single i 1) :=
    funext (fun y => u8_grad_apply f y i)
  rw [e]
  have h1 : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by
      have : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 = (k : WithTop ℕ∞) := by
        norm_cast; omega
      exact this.le)
  exact h1.clm_apply contDiff_const

theorem u8_grad_bound (f : Euc d → ℝ) (k : ℕ) (hf : ContDiff ℝ k f) (i : Fin d) (j : ℕ)
    (hj : j + 1 ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => gradient f y i) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f x‖ := by
  have e : (fun y => gradient f y i) = fun y => fderiv ℝ f y (EuclideanSpace.single i 1) :=
    funext (fun y => u8_grad_apply f y i)
  rw [e]
  have h1 : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by
      have : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 = (k : WithTop ℕ∞) := by
        norm_cast; omega
      exact this.le)
  have h2 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ f)
    (c := (EuclideanSpace.single i (1 : ℝ) : Euc d)) (x := x) (n := j)
    h1.contDiffAt (by exact_mod_cast (by omega : j ≤ k - 1))
  rw [norm_iteratedFDeriv_fderiv] at h2
  simpa using h2

theorem u8_sharp_tail (hd : 2 ≤ d) (a s : ℝ) (k : ℕ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hk : a / 2 + 1 < k) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ k f → decayNormE k (s + 1) f < ⊤ →
      ∃ w : Fin d → Euc d → ℝ, (∀ i, IsFracDerivRep (a / 2) (fun x => gradient f x i) (w i)) ∧
        (∀ i, MemLp (w i) (ENNReal.ofReal (2 * d / (a - 2))) volume) ∧
        (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
          ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (a - 2))) volume ≤
            ENNReal.ofReal C * decayNormE k (s + 1) f := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha2 : 0 < a - 2 := by linarith [ha.1]
  have hα : 0 < a / 2 := by linarith [ha.1]
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 * d / (a - 2) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hpa : p * (a - 2) = 2 * d := by rw [hpdef]; field_simp
  obtain ⟨b', hb'def⟩ : ∃ b' : ℝ, b' = min (s + 2) ((d : ℝ) / 2) := ⟨_, rfl⟩
  have hb'0 : 0 < b' := by rw [hb'def]; exact lt_min (by linarith) (by linarith)
  have hb'd : b' < d := by
    have := min_le_right (s + 2) ((d : ℝ) / 2); linarith
  have hb's : b' ≤ s + 2 := by rw [hb'def]; exact min_le_left _ _
  obtain ⟨C, hC0, hcore⟩ := HRS.U8.u8_core hd1 (a / 2) b' hα hb'0 hb'd
  have hγp : (d : ℝ) < (b' + a / 2) * p := by
    have h1 : (d : ℝ) * (a - 2) < (a / 2 * p) * (a - 2) := by nlinarith
    have h2 : (d : ℝ) < a / 2 * p := lt_of_mul_lt_mul_right h1 ha2.le
    nlinarith
  have hmem := HRS.U8.u8_decay_memLp (d := d) (b' + a / 2) p hp0 hγp
  have hEfin : eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-(b' + a / 2))) (ENNReal.ofReal p) volume
      < ⊤ := hmem.eLpNorm_lt_top
  obtain ⟨Eh, hEh⟩ : ∃ Eh : ℝ≥0∞, Eh =
      eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-(b' + a / 2))) (ENNReal.ofReal p) volume :=
    ⟨_, rfl⟩
  rw [← hEh] at hEfin
  refine ⟨u8_Cconv d k (s + 1) + d * (C * u8_Cconv d k (s + 1) * Eh.toReal), ?_⟩
  intro f hf hfin
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (decayNormE k (s + 1) f).toReal := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact ENNReal.toReal_nonneg
  have hdN : decayNormE k (s + 1) f = ENNReal.ofReal N := by
    rw [hN]; exact (ENNReal.ofReal_toReal hfin.ne).symm
  have hconv := u8_conv hd1 k (s + 1) (by linarith) f hfin
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = u8_Cconv d k (s + 1) := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by rw [hCc]; exact u8_Cconv_nonneg _ _ _
  rw [← hCc] at hconv ⊢
  rw [← hN] at hconv
  have hB0 : 0 ≤ N * Cc := mul_nonneg hN0 hCc0
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  have hkR : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
  have hℓ : ⌊a / 2⌋₊ + 1 ≤ k - 1 := by
    have : ⌊a / 2⌋₊ < k - 1 := (Nat.floor_lt hα.le).2 (by rw [hkR]; linarith)
    omega
  have hvl : ∀ i : Fin d, ContDiff ℝ ((⌊a / 2⌋₊ + 1 : ℕ) : WithTop ℕ∞) (fun y => gradient f y i) :=
    fun i => (u8_grad_smooth f k hk1 hf i).of_le (by exact_mod_cast hℓ)
  have hmono : ∀ (e : ℕ) (z : Euc d), (1 + ‖z‖) ^ (-((s + 1) + ((e + 1 : ℕ) : ℝ))) ≤
      (1 + ‖z‖) ^ (-(b' + (e : ℝ))) := by
    intro e z
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z])
    push_cast; linarith
  have h0 : ∀ i : Fin d, ∀ z, |(fun y => gradient f y i) z| ≤ N * Cc * (1 + ‖z‖) ^ (-b') := by
    intro i z
    have h1 := u8_grad_bound f k hf i 0 (by omega) z
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 := hconv 1 (by omega) z
    have h3 := hmono 0 z
    simp only [Nat.cast_zero, add_zero] at h3
    rw [← Real.norm_eq_abs]
    refine h1.trans (h2.trans ?_)
    apply mul_le_mul_of_nonneg_left _ hB0
    simpa using h3
  have h1 : ∀ i : Fin d, ∀ z, ‖iteratedFDeriv ℝ (⌊a / 2⌋₊ + 1) (fun y => gradient f y i) z‖ ≤
      N * Cc * (1 + ‖z‖) ^ (-(b' + ((⌊a / 2⌋₊ + 1 : ℕ) : ℝ))) := by
    intro i z
    have h1 := u8_grad_bound f k hf i (⌊a / 2⌋₊ + 1) (by omega) z
    have h2 := hconv (⌊a / 2⌋₊ + 1 + 1) (by omega) z
    refine h1.trans (h2.trans ?_)
    apply mul_le_mul_of_nonneg_left _ hB0
    exact hmono (⌊a / 2⌋₊ + 1) z
  have hw := fun i : Fin d => hcore (fun y => gradient f y i) (N * Cc) hB0 (hvl i) (h0 i) (h1 i)
  choose w hwm hwb hrep using hw
  have hCB : 0 ≤ C * (N * Cc) := mul_nonneg hC0 hB0
  have hLp := fun i : Fin d => HRS.U8.u8_decay_bound (d := d) (b' + a / 2) p hp0 hγp
    (C * (N * Cc)) hCB (w i) (hwm i) (fun x => by simpa [mul_assoc] using hwb i x)
  refine ⟨w, fun i φ => hrep i φ, fun i => by rw [← hpdef]; exact (hLp i).1, ?_⟩
  rw [← hpdef, hdN]
  have hterm : ∀ i : Fin d, eLpNorm (w i) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C * (N * Cc) * Eh.toReal) := by
    intro i
    calc eLpNorm (w i) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal (C * (N * Cc)) * Eh := by rw [hEh]; exact (hLp i).2
      _ = ENNReal.ofReal (C * (N * Cc)) * ENNReal.ofReal Eh.toReal := by
          rw [ENNReal.ofReal_toReal hEfin.ne]
      _ = ENNReal.ofReal (C * (N * Cc) * Eh.toReal) := (ENNReal.ofReal_mul hCB).symm
  have hsup : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) ≤ ENNReal.ofReal (N * Cc) := by
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    have h2 := hconv 2 (by
      have : (2 : ℝ) < k := by
        have : (d : ℝ) / 2 + 1 ≤ a / 2 + 1 := by linarith [ha.1]
        linarith
      exact_mod_cast this.le) x
    refine h2.trans ?_
    exact mul_le_of_le_one_right hB0 (HRS.U8.u8_rpow_le_one _ (norm_nonneg x) _ (by positivity))
  calc (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
        ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (N * Cc) + ∑ _i : Fin d, ENNReal.ofReal (C * (N * Cc) * Eh.toReal) :=
        add_le_add hsup (Finset.sum_le_sum (fun i _ => hterm i))
    _ = ENNReal.ofReal (N * Cc + d * (C * (N * Cc) * Eh.toReal)) := by
        have hE0 : 0 ≤ C * (N * Cc) * Eh.toReal := mul_nonneg hCB ENNReal.toReal_nonneg
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add hB0 (mul_nonneg (Nat.cast_nonneg _) hE0)]
    _ = ENNReal.ofReal ((Cc + d * (C * Cc * Eh.toReal)) * N) := by congr 1; ring
    _ = ENNReal.ofReal (Cc + d * (C * Cc * Eh.toReal)) * ENNReal.ofReal N :=
        ENNReal.ofReal_mul (add_nonneg hCc0 (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg hC0 hCc0) ENNReal.toReal_nonneg)))

theorem sharp_tail_bound_proof : type_of% @HRS.Whole.sharp_tail_bound := by
  intro d hd a s k ha hk hs
  exact u8_sharp_tail hd a s k ha hk hs

end HRS.Whole
