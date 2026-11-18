import HRS.MS.Mov63BAux5
import HRS.MS.Mov63Aux3
import HRS.MH.DualityRdC1b
import HRS.MS.MovThermAux2
import HRS.MS.MovLinAux8

/-!
# S6.3, packets N2b/N3a/N3b/N4 (uniqueness chain), part 1: plan and Gaussian/`RgW` infrastructure

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  Infrastructure for S6.3 (`mov_nonlinear`); not manuscript rows.
Target: `mov_nl_unique` (file `Mov63CAux7`), the uniqueness conjunct of `MovNonlinearConclusion`: two members of
`MovInSmallClass d s q β ρ₀ m r c₀ f0 ·` (any radius `r`, any `c₀ ≥ 0`, `m : ℕ` with `d/2 + 3 < m`) agree for `t ≥ 0`.

## Checks against the real definitions (all done before any proof)

* `MovInSmallClass` fields `solution` (all `T`), `init` (pointwise at `t = 0`), `weighted` (`MemOsc m` and the bound for
  `t ≥ 0`), `cont` (`OscSpace.ofFun m (movV ρ₀ ρ ·)` continuous on `[0,∞)`), `regular` (`ρ t` continuous, `t ≥ 0`).
  Both solutions have the SAME `u(0) = ofFun m (movV ρ₀ ρ 0)` since `movV` at `t = 0` is `f0 √ρ₀`.
* `IsWholeMeanFieldSolution.weak` tests with `ψ ∈ C_b²` and a Bochner integral over `Icc 0 t`; we only use `ψ = φ/√ρ₀`
  with `φ ∈ C_c^∞`; the integrand is identified POINTWISE in `r ∈ [0,t]` with a continuous function of
  `u_r = ofFun m (movV ρ₀ ρ r)`, so no Bochner junk enters.
* Reusable inputs found (merged, fully proved): `HRS.MH.DualityRd.self_pairing_rd_proof` (symmetrised
  `interactionPairingW D ψ ρ ρ = ∫ ρ ⟨∇ψ, M F[ρ]⟩` for `RegSliceRd ρ`, the whole Fubini symmetrisation with the cancellation
  convention, valid for all `s ∈ [0,d)`; this is exactly the reviewer's remark that the symmetrised pairing is controlled
  by `|z|^{-s}`), `dc1a_force_eq/_bound/_kernel_int` (cancellation-convention force of an `RgW` function), N1 (`mn_repFun`,
  `mn_sobolev_emb_gen`), N2a (`mov_B_ext`, `mov_B_ext_hs`, `mov_B_ext_bound`), `mov2d_R`, `mov2d_Sm` with `mov2d_hyp'`,
  `mov2c_integral_norm_le`.
* `D.M = -1`, `D.V = confinement q`, `D.invβ = β⁻¹` for `quadraticGradientDyn`; Euler `mv0_thermal_force`.
* Statements checked true/non-vacuous: nothing false found.  The planned statement of N2b (pointwise identification of
  `B_ext`, `R`, `S` on `Σ^m ∩ C^N`) is NOT needed in that form: it is replaced by a density argument (below), which
  proves the same content where it is used, with weaker hypotheses (no `C^N` regularity beyond `C^3`).

## Route and packets (deviation from SC63_REPORT 2.4: N2b is absorbed into N3a by density)

* `Mov63CAux1` (this file): Gaussian/`RgW` bookkeeping (Leibniz with Gaussian factor, `RgW` of `ρ₀` and of `√ρ₀ · g`,
  `RegSliceRd` from Gaussian bounds).
* `Mov63CAux2` (N3a, part 1): integration by parts for the divergence, ground-state flux, linearity/bounds of the
  cancellation force on `RgW`, and `mnc_decomp`: for `ρ_t = ρ₀ + h` with `RegSliceRd ρ_t`, `ψ = φ/√ρ₀`, `φ ∈ C_c^∞`:
  `pair(ρ_t)(νΔψ - ⟨qx,∇ψ⟩) + I(ρ_t) = ∫ v D_φ + A_ψ(h) + Q_ψ(h,h)`, `v = h/√ρ₀`.
* `Mov63CAux3`: `Phi` (bi)linearity and the continuous (bi)linear functionals `L, A, Q` on `OscSpace d m`.
* `Mov63CAux4` (N2b/N3a part 2): identification on Schwartz inputs and, by density of the Hermite span, on all of `Σ^m`
  (`mnc_lin_osc`, `mnc_quad_osc`).
* `Mov63CAux5` (N3a final): `mnc_weak_linear`, weak ⇒ `⟨φ,u_t⟩ - ⟨φ,u_0⟩ = ∫_{[0,t]} (-⟨S_0φ,u⟩ - ⟨φ,Ru⟩ + ⟨φ,B(u,u)⟩)`.
* `Mov63CAux6`–`Aux9` (N3b, part 1): pointwise representation of the pairing, the defect functional `Ψ`, cutoffs, and the
  extension to non-compactly supported good tests (`mnc_Psi_good_zero`).
* `Mov63CAux10`–`Aux13` (N3b, part 2): dilated Hermite tests, coefficient identity for the difference of two
  solutions, scalar variation of constants, the `S_0`-Duhamel formula `mnc_duhamel` in `OscSpace d m`.
* `Mov63CAux14` (N4): singular Gronwall (Mittag-Leffler iteration), `mnc_w_zero`.
* `Mov63CAux15`: `mov_nl_unique` and `mov_nl_unique_conjunct`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### Gaussians against polynomial weights -/

lemma mnc_gauss_poly {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ K := by
  refine ⟨(N.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)), by positivity, fun r hr => ?_⟩
  have h := HRS.MS.Mov0.mov0_pow_exp_bound (a := 2 * c) (M := 0) (by linarith) N r hr
  have e1 : -(2 * c * r ^ 2 / 2) + 0 * r = -c * r ^ 2 := by ring
  rw [e1] at h
  refine h.trans ?_
  have h2 : Real.exp (-(2 * c / 4) * r ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
  have h3 : 0 ≤ (N.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h3]

lemma mnc_gauss_le_w {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) ≤ K * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := mnc_gauss_poly hc (d + 1)
  refine ⟨K, hK0, fun x => ?_⟩
  have hpos : 0 < (1 + ‖x‖) := by positivity
  have h := hK ‖x‖ (norm_nonneg _)
  have e : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) = ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- A `C¹` function with Gaussian bounds on `f, Df` belongs to the weighted class `RgW` (decay weight `(1+|x|)^{-(d+1)}`);
the constant is linear in the Gaussian constant. -/
lemma mnc_rgW_of_gauss {c : ℝ} (hc : 0 < c) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ {f : Euc d → ℝ} {K : ℝ}, 0 ≤ K → ContDiff ℝ 1 f →
      (∀ n ≤ 1, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2)) →
      HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 (K0 * K) f := by
  obtain ⟨K0, hK0, h⟩ := mnc_gauss_le_w (d := d) hc
  refine ⟨K0, hK0, fun {f K} hK hf hb => ⟨hf, fun n hn x => ?_⟩⟩
  calc ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := hb n hn x
    _ ≤ K * (K0 * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := mul_le_mul_of_nonneg_left (h x) hK
    _ = K0 * K * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by ring

/-! ### Leibniz with a Gaussian factor -/

lemma mnc_gauss_mul {f g : Euc d → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) {K c M : ℝ}
    (hM : 0 ≤ M) (hfb : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2))
    (hgb : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (2 ^ k * K * M) * Real.exp (-c * ‖x‖ ^ 2) := by
  intro n hn x
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hfb 0 (Nat.zero_le _) 0)
    simpa using this
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (k : WithTop ℕ∞)) hf hg x (n := n) (by exact_mod_cast hn)
  refine h1.trans ?_
  have hE : 0 ≤ Real.exp (-c * ‖x‖ ^ 2) := (Real.exp_pos _).le
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (K * Real.exp (-c * ‖x‖ ^ 2) * M) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
        have a1 := hfb i (hik.trans hn) x
        have a2 := hgb (n - i) ((Nat.sub_le n i).trans hn) x
        have : ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤
            K * Real.exp (-c * ‖x‖ ^ 2) * M :=
          mul_le_mul a1 a2 (norm_nonneg _) (mul_nonneg hK hE)
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
            = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = (2 ^ n : ℝ) * (K * Real.exp (-c * ‖x‖ ^ 2) * M) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
    _ ≤ (2 ^ k : ℝ) * (K * Real.exp (-c * ‖x‖ ^ 2) * M) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hK hE) hM)
        exact pow_le_pow_right₀ (by norm_num) hn
    _ = _ := by ring


/-! ### `RegSliceRd` from Gaussian bounds -/

lemma mnc_jbracket_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg x]

lemma mnc_partialDeriv_le {j : ℕ} (i : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv i f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
  have hn : ∀ l, ‖(EuclideanSpace.single (i l) (1 : ℝ) : Euc d)‖ = 1 := fun l => by simp
  simp only [hn, Finset.prod_const_one, mul_one] at h
  rwa [Real.norm_eq_abs] at h

lemma mnc_regSlice_of_gauss {f : Euc d → ℝ} {K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hf : ContDiff ℝ 3 f)
    (hb : ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2))
    (hp : Whole.IsProbDensity f) : RegSliceRd f := by
  refine ⟨hp, ⟨hf, fun j hj => ⟨K, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine (hb j hj x).trans ?_
    exact mul_le_of_le_one_right hK (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖]))
  · obtain ⟨K1, hK1, h1⟩ := mnc_gauss_poly hc (d + 3)
    refine lt_of_le_of_lt (b := ENNReal.ofReal (K * K1)) ?_ ENNReal.ofReal_lt_top
    unfold weightedSupE derivSupE
    refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hj : (j : ℕ) ≤ 3 := Nat.lt_succ_iff.1 j.2
    have e1 : |partialDeriv i f x| ≤ K * Real.exp (-c * ‖x‖ ^ 2) :=
      (mnc_partialDeriv_le i f x).trans (hb j hj x)
    have e2 : jbracket x ^ ((d : ℝ) + 3) ≤ (1 + ‖x‖) ^ (d + 3) := by
      have h0 : 0 ≤ jbracket x := Real.sqrt_nonneg _
      calc jbracket x ^ ((d : ℝ) + 3) ≤ (1 + ‖x‖) ^ ((d : ℝ) + 3) :=
            Real.rpow_le_rpow h0 (mnc_jbracket_le x) (by positivity)
        _ = (1 + ‖x‖) ^ (d + 3) := by
            rw [← Real.rpow_natCast]; push_cast; rfl
    have e3 := h1 ‖x‖ (norm_nonneg _)
    have hE : 0 ≤ Real.exp (-c * ‖x‖ ^ 2) := (Real.exp_pos _).le
    have hJ : 0 ≤ jbracket x ^ ((d : ℝ) + 3) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc jbracket x ^ ((d : ℝ) + 3) * |partialDeriv i f x|
        ≤ (1 + ‖x‖) ^ (d + 3) * (K * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul e2 e1 (abs_nonneg _) (by positivity)
      _ = K * ((1 + ‖x‖) ^ (d + 3) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
      _ ≤ K * K1 := mul_le_mul_of_nonneg_left e3 hK

/-! ### The Gaussian class of `√ρ`, `ρ` and of `√ρ · g` -/

section Class

variable {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mnc_sqrt_gauss (hρ : MovRhoData d ρ) (k : ℕ) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ n ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => Real.sqrt (ρ y)) x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨c, hc, hj⟩ := mv1_gauss_common hρ.sqrt_gauss k
  choose! C hC using hj
  refine ⟨c, ∑ j ∈ Finset.range (k + 1), |C j|, hc, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n hn x => ?_⟩
  refine (hC n hn x).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega)))

lemma mnc_rho_gauss (H : Mov2dTh d s β q ρ) (k : ℕ) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ n ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ n ρ x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨-, hg⟩ := HRS.MS.Mov0.mv0_hgauss H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hg' : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := hg
  obtain ⟨c, hc, hj⟩ := mv1_gauss_common hg' k
  choose! C hC using hj
  refine ⟨c, ∑ j ∈ Finset.range (k + 1), |C j|, hc, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n hn x => ?_⟩
  refine (hC n hn x).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega)))

lemma mnc_rho_smooth (H : Mov2dTh d s β q ρ) : ContDiff ℝ ∞ ρ :=
  (HRS.MS.Mov0.mv0_hgauss H.hd H.hs0 H.hsd H.hq H.hβ H.hρ).1

lemma mnc_rgW_rho (H : Mov2dTh d s β q ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 K ρ := by
  obtain ⟨c, K, hc, hK, hb⟩ := mnc_rho_gauss H 1
  obtain ⟨K0, hK0, h⟩ := mnc_rgW_of_gauss (d := d) hc
  exact ⟨K0 * K, mul_nonneg hK0 hK,
    h hK ((mnc_rho_smooth H).of_le (by exact_mod_cast le_top)) hb⟩

/-- `√ρ · g` for `g = rep u`: smoothness and Gaussian bounds, linear in `‖u‖`. -/
lemma mnc_h_gauss (H : Mov2dTh d s β q ρ) {i m : ℕ} (hn : (i : ℝ) + d / 2 < m) :
    ∃ c K0 : ℝ, 0 < c ∧ 0 ≤ K0 ∧ ∀ u : OscSpace d (m : ℝ),
      ContDiff ℝ (i : WithTop ℕ∞) (fun y => Real.sqrt (ρ y) * mn_repFun i m hn u y) ∧
      ∀ n ≤ i, ∀ x, ‖iteratedFDeriv ℝ n (fun y => Real.sqrt (ρ y) * mn_repFun i m hn u y) x‖ ≤
        (K0 * ‖u‖) * Real.exp (-c * ‖x‖ ^ 2) := by
  have hρ := mnb_rhoData H
  obtain ⟨c, K, hc, hK, hb⟩ := mnc_sqrt_gauss hρ i
  obtain ⟨Cs, hCs0, hCs⟩ := mn_repFun_bound i m hn
  refine ⟨c, 2 ^ i * K * Cs, hc, by positivity, fun u => ⟨?_, ?_⟩⟩
  · exact (hρ.sqrt_smooth.of_le (by exact_mod_cast le_top)).mul (mn_repFun_contDiff i m hn u)
  · intro n hn' x
    have := mnc_gauss_mul (f := fun y => Real.sqrt (ρ y)) (g := mn_repFun i m hn u) (k := i) (K := K) (c := c)
      (M := Cs * ‖u‖) (hρ.sqrt_smooth.of_le (by exact_mod_cast le_top)) (mn_repFun_contDiff i m hn u)
      (by positivity) hb (fun n hn' x => hCs u n hn' x) n hn' x
    calc _ ≤ (2 ^ i * K * (Cs * ‖u‖)) * Real.exp (-c * ‖x‖ ^ 2) := this
      _ = _ := by ring

lemma mnc_rgW_h (H : Mov2dTh d s β q ρ) {i m : ℕ} (hn : (i : ℝ) + d / 2 < m) (hi : 1 ≤ i) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ u : OscSpace d (m : ℝ),
      HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 (K1 * ‖u‖)
        (fun y => Real.sqrt (ρ y) * mn_repFun i m hn u y) := by
  obtain ⟨c, K0, hc, hK0, h⟩ := mnc_h_gauss H hn
  obtain ⟨K2, hK2, h2⟩ := mnc_rgW_of_gauss (d := d) hc
  refine ⟨K2 * K0, mul_nonneg hK2 hK0, fun u => ?_⟩
  have := h2 (f := fun y => Real.sqrt (ρ y) * mn_repFun i m hn u y) (K := K0 * ‖u‖)
    (mul_nonneg hK0 (norm_nonneg _)) ((h u).1.of_le (by exact_mod_cast hi))
    (fun n hn' x => (h u).2 n (by omega) x)
  rwa [← mul_assoc] at this

end Class

end HRS.MS.Mov63
