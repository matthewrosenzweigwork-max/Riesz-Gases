import HRS.MS.UlTailAux1

/-!
# UL-T (S5.1 convolution tails), part 2: decay of the derivatives of `ultK κ h`

Infrastructure packet UL-T (supplement `W:r2:convolution-tail`, S L3300-3320); not a manuscript row.
For a kernel `κ` with `UlKer κ s` (`0 ≤ s < d`) and `h` with the weighted bounds `U2Dec (k+1) L A h`,
`L > d + k + s + 3`:

* `ult_K_crude`: `‖ultK κ g x‖ ≤ C_N Lip(g) + C_F ‖g‖_{weighted}` (no decay needed);
* `ult_K_eq_conv`: far from the support of `g` the cancellation operator is the plain convolution;
* `ult_far`: `‖D^j (ultK κ h)(x)‖ ≤ C A ‖x‖^{-(s+1+j)}` for `‖x‖ ≥ 2`, `j ≤ k`
  (the proof of `u2_far` of `SuppU2Aux8` with the cancellation operator: `h = h₁ + h₂`, `h₂ = ν(·/R) h`
  vanishing near `0`; the derivatives of `ultK κ h₁` go on the kernel (`u2_kernel_side_norm`), those of
  `ultK κ h₂` go on `h₂` (`ult_K_iter`) and `h₂` is `O(R^{-N})`);
* `ult_core`: `ultK κ h` is `C^k` and `‖D^j (ultK κ h)(x)‖ ≤ C A (1+‖x‖)^{-(s+1+j)}` for all `x`;
* `UlRapid`: smooth functions all of whose derivatives decay faster than every power; Schwartz functions
  are such, and `UlRapid h` gives `U2Dec (k+1) L A h` for all `k, L`.

Helper lemmas carry the prefix `ult_`; namespace `HRS.MS.Ul`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole

variable {d : ℕ}

/-- No Bochner junk and a crude bound for the cancellation operator. -/
lemma ult_K_crude (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L : ℝ}
    (hL : (d : ℝ) < L) :
    ∃ CN CF : ℝ, 0 ≤ CN ∧ 0 ≤ CF ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : Euc d → F), Continuous g → ∀ (B1 A0 : ℝ), 0 ≤ B1 → 0 ≤ A0 →
      (∀ a b, ‖g a - g b‖ ≤ B1 * ‖a - b‖) → (∀ y, ‖g y‖ ≤ A0 * u2Wt L y) →
      ∀ x, ‖ultK κ g x‖ ≤ CN * B1 + CF * A0 := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  obtain ⟨Cu, hCu0, hCu⟩ := u2_conv_norm_le (ult_far_U2Ker hd hK) hL
  have hΦ := ult_Phi_int hd hK
  have hΦ0 : 0 ≤ ∫ z, (ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s)) z :=
    integral_nonneg fun z => Set.indicator_nonneg
      (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  refine ⟨C0 * ∫ z, (ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s)) z, Cu,
    mul_nonneg hC0 hΦ0, hCu0, ?_⟩
  intro F _ _ g hg B1 A0 hB1 hA0 hLip hw x
  unfold ultK
  refine (norm_add_le _ _).trans (add_le_add ?_ (hCu F g A0 hA0 hw x))
  unfold ultNear
  calc ‖∫ z, ultKN κ z • (g (x - z) - g x)‖
      ≤ ∫ z, C0 * B1 * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z := by
        refine norm_integral_le_of_norm_le (hΦ.const_mul (C0 * B1)) ?_
        filter_upwards [u2_ae_ne_zero hd] with z hz
        refine ult_near_dom hC0 hb hB1 hz ?_
        have := hLip (x - z) x
        simpa using this
    _ = (C0 * ∫ z, (ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s)) z) * B1 := by
        rw [integral_const_mul]; ring

/-- Far from the support of `g` the cancellation operator is the plain convolution. -/
lemma ult_K_eq_conv {κ : Euc d → ℝ} {g : Euc d → ℝ} {r : ℝ} (hr : 1 / 2 ≤ r)
    (hsupp : ∀ y : Euc d, r < ‖y‖ → g y = 0) {x : Euc d} (hx : 3 * r / 2 < ‖x‖) :
    ultK κ g x = u2Conv κ g x := by
  have hgx : g x = 0 := hsupp x (by linarith)
  have hnear : ultNear κ g x = 0 := by
    unfold ultNear
    have : (fun z : Euc d => ultKN κ z • (g (x - z) - g x)) = fun _ => 0 := by
      funext z
      by_cases hz : ‖z‖ ≤ 1 / 4
      · have h1 : r < ‖x - z‖ := by
          have := norm_sub_norm_le x z
          linarith
        rw [hsupp _ h1, hgx]; simp
      · rw [ultKN, if_neg hz, zero_smul]
    rw [this]; simp
  have hfar : u2Conv (ultKF κ) g x = u2Conv κ g x := by
    unfold u2Conv
    congr 1
    funext z
    by_cases hgz : g (x - z) = 0
    · rw [hgz]; simp
    · have h1 : ‖x - z‖ ≤ r := by
        by_contra hc
        exact hgz (hsupp _ (not_le.mp hc))
      have h2 : ¬ ‖z‖ ≤ 1 / 4 := by
        have := norm_sub_norm_le x (x - z)
        simp only [sub_sub_cancel] at this
        intro hz
        linarith
      rw [ultKF, if_neg h2]
  unfold ultK
  rw [hnear, hfar, zero_add]

lemma ult_U2Dec_mono {L A : ℝ} {k j : ℕ} {h : Euc d → ℝ} (hdec : U2Dec k L A h) (hj : j ≤ k) :
    U2Dec j L A h :=
  ⟨hdec.1.of_le (by exact_mod_cast hj), fun m hm => hdec.2 m (by omega)⟩

lemma ult_K_sub (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A1 A2 : ℝ}
    (hL : (d : ℝ) < L) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) {g1 g2 : Euc d → ℝ}
    (h1 : U2Dec 1 L A1 g1) (h2 : U2Dec 1 L A2 g2) (x : Euc d) :
    ultK κ (fun y => g1 y - g2 y) x = ultK κ g1 x - ultK κ g2 x := by
  obtain ⟨n1, f1⟩ := ult_K_integrable hd hK hL hA1 h1 x
  obtain ⟨n2, f2⟩ := ult_K_integrable hd hK hL hA2 h2 x
  unfold ultK ultNear u2Conv
  have e1 : (fun z : Euc d => ultKN κ z • ((g1 (x - z) - g2 (x - z)) - (g1 x - g2 x))) =
      fun z => ultKN κ z • (g1 (x - z) - g1 x) - ultKN κ z • (g2 (x - z) - g2 x) := by
    funext z; rw [← smul_sub]; congr 1; ring
  have e2 : (fun z : Euc d => ultKF κ z • (g1 (x - z) - g2 (x - z))) =
      fun z => ultKF κ z • g1 (x - z) - ultKF κ z • g2 (x - z) := by
    funext z; rw [smul_sub]
  simp only [e1, e2]
  rw [integral_sub n1 n2, integral_sub f1 f2]
  abel

lemma ult_wt_ratio {L : ℝ} {q : ℝ} (hq : q = L - d - 1) (y : Euc d) :
    u2Wt (d := d) L y ≤ (1 + ‖y‖) ^ (-q) * u2Wt (d := d) ((d : ℝ) + 1) y := by
  unfold u2Wt
  have h1y : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have : (1 + ‖y‖) ^ (-L) = (1 + ‖y‖) ^ (-q) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    rw [← Real.rpow_add h1y]; congr 1; rw [hq]; ring
  rw [this]

/-- The decay at infinity (`‖x‖ ≥ 2`), the analogue of `u2_far` for the cancellation operator. -/
theorem ult_far (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec (k + 1) L A h →
      ∀ x0 : Euc d, 2 ≤ ‖x0‖ → ∀ j ≤ k,
        ‖iteratedFDeriv ℝ j (ultK κ h) x0‖ ≤ Cf * A * ‖x0‖ ^ (-(s + 1 + j)) := by
  have hs0 := hK.hs0
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := u2_wt_L0 hdL
  have hd1 : (d : ℝ) < (d : ℝ) + 1 := by linarith
  obtain ⟨ν, hν⟩ := u2_exists_cutoff d
  obtain ⟨BB, hBB0, hBB⟩ := u2_h2_dec hν (k + 1)
  choose Cj hCj0 hCj using hK.hD
  obtain ⟨CN, CF, hCN0, hCF0, hcr⟩ := ult_K_crude hd hK hd1
  set IL : ℝ := ∫ y, u2Wt (d := d) L y with hIL
  have hIL0 : 0 ≤ IL := u2_integral_nonneg (fun y => (u2Wt_pos L y).le)
  set q : ℝ := L - d - 1 with hq
  have hq0 : 0 ≤ q := by
    simp only [hq]
    linarith
  set Cj' : ℕ → ℝ := fun j => Cj j * 2 ^ (s + 1 + j) * (1 + BB) * IL +
    (CN + CF) * BB * 4 ^ q with hCj'
  have hCj'0 : ∀ j, 0 ≤ Cj' j := fun j => by
    have := hCj0 j
    simp only [hCj']
    positivity
  refine ⟨∑ j ∈ Finset.range (k + 1), Cj' j, Finset.sum_nonneg fun j _ => hCj'0 j, ?_⟩
  intro A h hA hdec x0 hx0 j hj
  set R : ℝ := ‖x0‖ with hR
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨hh2cd, hh2b⟩ := hBB L A h hA hdec R hR1
  set h2 : Euc d → ℝ := u2_h2 ν R h with hh2
  have hBA : 0 ≤ BB * A := mul_nonneg hBB0 hA
  have hdec2 : U2Dec (k + 1) L (BB * A) h2 := by
    refine ⟨hh2cd, fun m hm y => ?_⟩
    refine (hh2b m hm y).trans ?_
    have := u2Wt_pos (d := d) L y
    split_ifs
    · exact le_refl _
    · positivity
  set h1 : Euc d → ℝ := fun y => h y - h2 y with hh1
  have hhc : Continuous h := hdec.1.continuous
  have hh2c : Continuous h2 := hh2cd.continuous
  have hh1c : Continuous h1 := hhc.sub hh2c
  have hh1supp : ∀ y : Euc d, R / 2 < ‖y‖ → h1 y = 0 := by
    intro y hy
    have : ν (R⁻¹ • y) = 1 := by
      apply hν.one
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
      calc (1 : ℝ) / 2 = R⁻¹ * (R / 2) := by field_simp
        _ < R⁻¹ * ‖y‖ := mul_lt_mul_of_pos_left hy (inv_pos.mpr hR0)
    simp only [hh1, hh2, u2_h2, this, one_mul, sub_self]
  have hh0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y := fun y => by
    simpa using hdec.2 0 (Nat.zero_le _) y
  have hh20 : ∀ y, ‖h2 y‖ ≤ (BB * A) * u2Wt L y := fun y => by
    simpa using hdec2.2 0 (Nat.zero_le _) y
  have hh10 : ∀ y, ‖h1 y‖ ≤ ((1 + BB) * A) * u2Wt L y := fun y => by
    calc ‖h1 y‖ ≤ ‖h y‖ + ‖h2 y‖ := norm_sub_le _ _
      _ ≤ A * u2Wt L y + (BB * A) * u2Wt L y := add_le_add (hh0 y) (hh20 y)
      _ = ((1 + BB) * A) * u2Wt L y := by ring
  have hA1 : 0 ≤ (1 + BB) * A := mul_nonneg (by linarith) hA
  -- the iteration formulas and `C^k` regularity
  obtain ⟨hF_iter, hF_cd⟩ := ult_K_iter hd hK hdL hA hdec
  obtain ⟨hF2_iter, hF2_cd⟩ := ult_K_iter hd hK hdL hBA hdec2
  have hdecm : U2Dec 1 L A h := ult_U2Dec_mono hdec (by omega)
  have hdec2m : U2Dec 1 L (BB * A) h2 := ult_U2Dec_mono hdec2 (by omega)
  have hF1 : ultK κ h1 = fun x => ultK κ h x - ultK κ h2 x := by
    funext x
    exact ult_K_sub hd hK hdL hA hBA hdecm hdec2m x
  have hF1cd : ContDiff ℝ k (ultK κ h1) := by
    rw [hF1]; exact hF_cd.sub hF2_cd
  have hjk : (j : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hj
  have hsplit : iteratedFDeriv ℝ j (ultK κ h) x0 =
      iteratedFDeriv ℝ j (ultK κ h1) x0 + iteratedFDeriv ℝ j (ultK κ h2) x0 := by
    have : ultK κ h = ultK κ h1 + ultK κ h2 := by
      funext x
      have := congrFun hF1 x
      simp only [Pi.add_apply]
      rw [this]; ring
    rw [this]
    exact iteratedFDeriv_add_apply ((hF1cd.of_le hjk).contDiffAt) ((hF2_cd.of_le hjk).contDiffAt)
  have hr2 : 0 < R / 2 := by linarith
  -- Term 1: kernel-side
  have hev : ultK κ h1 =ᶠ[𝓝 x0] u2Conv κ h1 := by
    filter_upwards [IsOpen.mem_nhds isOpen_ball (mem_ball_self (by linarith : 0 < (R / 2) / 2))]
      with x hx
    refine ult_K_eq_conv (by linarith) hh1supp ?_
    have := mem_ball_iff_norm.mp hx
    have h3 : ‖x0‖ ≤ ‖x‖ + ‖x - x0‖ := by
      calc ‖x0‖ = ‖x - (x - x0)‖ := by simp
        _ ≤ ‖x‖ + ‖x - x0‖ := norm_sub_le _ _
    linarith
  have hT1 := u2_kernel_side_norm (κ := κ) (a := s + 1) (by linarith) hK.hsm (hCj0 j) j (hCj j)
    hK.hD hr2 hh1c hh1supp (x0 := x0) (by linarith)
  have hint1 : ∫ y, ‖h1 y‖ ≤ ((1 + BB) * A) * IL := by
    have hgi : Integrable h1 volume := u2_integrable_of_support hh1c hh1supp
    calc ∫ y, ‖h1 y‖ ≤ ∫ y, ((1 + BB) * A) * u2Wt L y :=
          integral_mono hgi.norm ((u2_integrable_wt hdL).const_mul _) hh10
      _ = ((1 + BB) * A) * IL := by rw [integral_const_mul]
  have hT1' : ‖iteratedFDeriv ℝ j (ultK κ h1) x0‖ ≤
      (Cj j * (R / 2) ^ (-(s + 1) - j)) * (((1 + BB) * A) * IL) := by
    rw [hev.iteratedFDeriv ℝ j |>.eq_of_nhds]
    exact hT1.trans (mul_le_mul_of_nonneg_left hint1
      (mul_nonneg (hCj0 j) (Real.rpow_nonneg hr2.le _)))
  -- Term 2: h-side
  set W : ℝ := (1 + R / 4) ^ (-q) with hW
  have hW0 : 0 ≤ W := (Real.rpow_nonneg (by positivity) _)
  have hD2 : ∀ m ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ m h2 y‖ ≤
      (BB * A) * (W * u2Wt (d := d) ((d : ℝ) + 1) y) := by
    intro m hm y
    have hy := hh2b m hm y
    by_cases hyR : R / 4 ≤ ‖y‖
    · rw [if_pos hyR] at hy
      refine hy.trans ?_
      have : u2Wt L y ≤ W * u2Wt ((d : ℝ) + 1) y := by
        refine (ult_wt_ratio hq y).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (u2Wt_pos _ y).le
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      calc BB * A * u2Wt L y ≤ BB * A * (W * u2Wt ((d : ℝ) + 1) y) :=
            mul_le_mul_of_nonneg_left this hBA
        _ = _ := rfl
    · rw [if_neg hyR] at hy
      refine hy.trans ?_
      have := u2Wt_pos (d := d) ((d : ℝ) + 1) y
      positivity
  have hwle : ∀ y : Euc d, u2Wt (d := d) ((d : ℝ) + 1) y ≤ 1 := fun y =>
    u2Wt_le_one (by positivity) y
  have hGc : Continuous (iteratedFDeriv ℝ j h2) :=
    hdec2.1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j ≤ k + 1))
  have hGlip : ∀ a b, ‖iteratedFDeriv ℝ j h2 a - iteratedFDeriv ℝ j h2 b‖ ≤
      (BB * A * W) * ‖a - b‖ := by
    refine ult_lip_of_fderiv ((ult_iter_contDiff1 hdec2 (m := j) (by omega)).differentiable
      one_ne_zero) (fun y => ?_)
    rw [u2_norm_fderiv_iteratedFDeriv]
    refine (hD2 (j + 1) (by omega) y).trans ?_
    calc BB * A * (W * u2Wt (d := d) ((d : ℝ) + 1) y) ≤ BB * A * (W * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hwle y) hW0) hBA
      _ = BB * A * W := by ring
  have hBAW : 0 ≤ BB * A * W := mul_nonneg hBA hW0
  have hT2 : ‖iteratedFDeriv ℝ j (ultK κ h2) x0‖ ≤ (CN + CF) * (BB * A * W) := by
    rw [hF2_iter j hj x0]
    have := hcr _ (iteratedFDeriv ℝ j h2) hGc (BB * A * W) (BB * A * W) hBAW hBAW hGlip
      (fun y => by
        have := hD2 j (by omega) y
        calc _ ≤ _ := this
          _ = (BB * A * W) * u2Wt (d := d) ((d : ℝ) + 1) y := by ring) x0
    calc _ ≤ CN * (BB * A * W) + CF * (BB * A * W) := this
      _ = (CN + CF) * (BB * A * W) := by ring
  -- final assembly
  have hjq : s + 1 + (j : ℝ) ≤ q := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    simp only [hq]
    linarith
  have hWle2 : W ≤ 4 ^ q * R ^ (-(s + 1 + (j : ℝ))) :=
    (u2_quarter_rpow hR0 q hq0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (by positivity))
  have e1 : (R / 2) ^ (-(s + 1) - (j : ℝ)) = 2 ^ (s + 1 + (j : ℝ)) * R ^ (-(s + 1 + (j : ℝ))) := by
    rw [show -(s + 1) - (j : ℝ) = -(s + 1 + (j : ℝ)) by ring]
    exact u2_half_rpow hR0 _
  have hjle : Cj' j ≤ ∑ j' ∈ Finset.range (k + 1), Cj' j' :=
    Finset.single_le_sum (f := Cj') (fun j' _ => hCj'0 j') (Finset.mem_range.mpr (by omega))
  have hRp : 0 ≤ R ^ (-(s + 1 + (j : ℝ))) := Real.rpow_nonneg hR0.le _
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ j (ultK κ h1) x0‖ + ‖iteratedFDeriv ℝ j (ultK κ h2) x0‖
      ≤ (Cj j * (R / 2) ^ (-(s + 1) - (j : ℝ))) * (((1 + BB) * A) * IL) +
          (CN + CF) * (BB * A * W) := add_le_add hT1' hT2
    _ ≤ (Cj j * (R / 2) ^ (-(s + 1) - (j : ℝ))) * (((1 + BB) * A) * IL) +
          (CN + CF) * (BB * A * (4 ^ q * R ^ (-(s + 1 + (j : ℝ))))) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact mul_le_mul_of_nonneg_left hWle2 hBA
    _ = Cj' j * A * R ^ (-(s + 1 + (j : ℝ))) := by
        simp only [hCj']
        rw [e1]
        ring
    _ ≤ (∑ j' ∈ Finset.range (k + 1), Cj' j') * A * R ^ (-(s + 1 + (j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjle hA) hRp

/-- The global statement: `C^k` regularity and the decay `(1+‖x‖)^{-(s+1+j)}` of `D^j (ultK κ h)`. -/
theorem ult_core (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec (k + 1) L A h →
      ContDiff ℝ k (ultK κ h) ∧ ∀ j ≤ k, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (ultK κ h) x‖ ≤ C * A * (1 + ‖x‖) ^ (-(s + 1 + j)) := by
  have hs0 := hK.hs0
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 := u2_wt_L0 hdL
  obtain ⟨Cf, hCf0, hCf⟩ := ult_far hd hK k hL
  obtain ⟨CN, CF, hCN0, hCF0, hcr⟩ := ult_K_crude hd hK hdL
  set P : ℝ := s + 1 + (k : ℝ) with hP
  have hP0 : 0 ≤ P := by simp only [hP]; linarith
  have h3P : (0 : ℝ) ≤ 3 ^ P := by positivity
  refine ⟨(Cf + CN + CF) * 3 ^ P, by positivity, ?_⟩
  intro A h hA hdec
  obtain ⟨hF_iter, hF_cd⟩ := ult_K_iter hd hK hdL hA hdec
  refine ⟨hF_cd, fun j hj x => ?_⟩
  have hjP : s + 1 + (j : ℝ) ≤ P := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    simp only [hP]; linarith
  have hp : 0 ≤ s + 1 + (j : ℝ) := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have h3 : (3 : ℝ) ^ (s + 1 + (j : ℝ)) ≤ 3 ^ P :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hjP
  have hv : 0 < 1 + ‖x‖ := by positivity
  have hvp : 0 ≤ (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := Real.rpow_nonneg hv.le _
  by_cases hx : 2 ≤ ‖x‖
  · have h1 := hCf A h hA hdec x hx j hj
    have h2 := u2_cmp (by linarith : 0 < ‖x‖) hv (by linarith) hp
    have h22 : (2 : ℝ) ^ (s + 1 + (j : ℝ)) ≤ 3 ^ P :=
      (Real.rpow_le_rpow (by norm_num) (by norm_num) hp).trans h3
    calc ‖iteratedFDeriv ℝ j (ultK κ h) x‖ ≤ Cf * A * ‖x‖ ^ (-(s + 1 + (j : ℝ))) := h1
      _ ≤ Cf * A * (2 ^ (s + 1 + (j : ℝ)) * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCf0 hA)
      _ ≤ Cf * A * (3 ^ P * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h22 hvp) (mul_nonneg hCf0 hA)
      _ = Cf * 3 ^ P * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := by ring
      _ ≤ (Cf + CN + CF) * 3 ^ P * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hA) hvp
          exact mul_le_mul_of_nonneg_right (by linarith) h3P
  · push Not at hx
    rw [hF_iter j hj x]
    have hjk1 : j + 1 ≤ k + 1 := by omega
    have hGc : Continuous (iteratedFDeriv ℝ j h) :=
      hdec.1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j ≤ k + 1))
    have hb := hcr _ (iteratedFDeriv ℝ j h) hGc A A hA hA (ult_iter_lip hL0 hA hdec hjk1)
      (fun y => hdec.2 j (by omega) y) x
    have h4 : (3 : ℝ) ^ (-(s + 1 + (j : ℝ))) ≤ (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos hv (by linarith) (by linarith)
    have h5 : (1 : ℝ) ≤ 3 ^ P * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := by
      have : (3 : ℝ) ^ (s + 1 + (j : ℝ)) * 3 ^ (-(s + 1 + (j : ℝ))) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc (1 : ℝ) = 3 ^ (s + 1 + (j : ℝ)) * 3 ^ (-(s + 1 + (j : ℝ))) := this.symm
        _ ≤ 3 ^ P * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) :=
            mul_le_mul h3 h4 (Real.rpow_nonneg (by norm_num) _) h3P
    calc ‖ultK κ (iteratedFDeriv ℝ j h) x‖ ≤ CN * A + CF * A := hb
      _ = (CN + CF) * A * 1 := by ring
      _ ≤ (CN + CF) * A * (3 ^ P * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg (by positivity) hA)
      _ = (CN + CF) * 3 ^ P * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := by ring
      _ ≤ (Cf + CN + CF) * 3 ^ P * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hA) hvp
          exact mul_le_mul_of_nonneg_right (by linarith) h3P

/-- Smooth functions all of whose derivatives decay faster than every power. -/
def UlRapid (h : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧ ∀ m N : ℕ, ∃ C : ℝ, ∀ x : Euc d, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ m h x‖ ≤ C

lemma ult_rapid_U2Dec {h : Euc d → ℝ} (hh : UlRapid h) (k : ℕ) (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ U2Dec k L A h := by
  choose C hC using fun m : ℕ => hh.2 m ⌈L⌉₊
  refine ⟨∑ m ∈ Finset.range (k + 1), max (C m) 0,
    Finset.sum_nonneg fun m _ => le_max_right _ _, ⟨hh.1.of_le (by exact_mod_cast le_top), ?_⟩⟩
  intro m hm y
  have hy : 0 < 1 + ‖y‖ := by positivity
  have h1 : ‖iteratedFDeriv ℝ m h y‖ ≤ max (C m) 0 * (1 + ‖y‖) ^ (-(⌈L⌉₊ : ℝ)) := by
    rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ m h y‖ * (1 + ‖y‖) ^ ⌈L⌉₊ =
        (1 + ‖y‖) ^ ⌈L⌉₊ * ‖iteratedFDeriv ℝ m h y‖ := by ring
      _ ≤ C m := hC m y
      _ ≤ max (C m) 0 := le_max_left _ _
  have h2 : (1 + ‖y‖) ^ (-(⌈L⌉₊ : ℝ)) ≤ u2Wt (d := d) L y := by
    unfold u2Wt
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y])
      (by have := Nat.le_ceil L; linarith)
  have h3 : max (C m) 0 ≤ ∑ m ∈ Finset.range (k + 1), max (C m) 0 :=
    Finset.single_le_sum (f := fun m => max (C m) 0) (fun m _ => le_max_right _ _)
      (Finset.mem_range.mpr (by omega))
  calc _ ≤ max (C m) 0 * (1 + ‖y‖) ^ (-(⌈L⌉₊ : ℝ)) := h1
    _ ≤ max (C m) 0 * u2Wt (d := d) L y := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ ≤ (∑ m ∈ Finset.range (k + 1), max (C m) 0) * u2Wt (d := d) L y :=
        mul_le_mul_of_nonneg_right h3 (u2Wt_pos L y).le

end HRS.MS.Ul
