import HRS.MS.UniqQAux7

/-!
# UNIQ-Q, part 8: closing the argument (uniqueness for the abstract solution class)

`uniqq_zero`: a `UqSol` with `S = ⟨c,∇u⟩ - N u`, `c` bounded, and `u(t) = 0`, vanishes identically.
The window step: `|S| ≤ m` on `(r₀,t₁)`, `t₁ - r₀ ≤ δ` ⇒ `|S| ≤ m/2`; hence `S = 0`; hence `u = 0` (`uniqq_step`, `M = 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem uniqq_grad_norm (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

/-- `C_b²` functions: gradient bounded, `∇f` Hölder of every exponent `β ∈ [0,1]` -/
theorem uniqq_hold_of_cb2 {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {B β : ℝ}
    (h1 : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ B) (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ B)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∀ x, ‖gradient f x‖ ≤ B) ∧ ∀ x a, ‖gradient f (x + a) - gradient f x‖ ≤ 2 * B * ‖a‖ ^ β := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h1 0)
  have hg : ∀ x, ‖gradient f x‖ ≤ B := fun x => by
    rw [uniqq_grad_norm, ← norm_iteratedFDeriv_one]; exact h1 x
  refine ⟨hg, fun x a => ?_⟩
  have hsub : ∀ y z : Euc d, ‖gradient f y - gradient f z‖ = ‖fderiv ℝ f y - fderiv ℝ f z‖ := by
    intro y z
    unfold gradient
    rw [← map_sub]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
  have hd : ∀ z, DifferentiableAt ℝ (fderiv ℝ f) z := fun z =>
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z
  have hlip : ∀ y z : Euc d, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ B * ‖y - z‖ := by
    intro y z
    have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ f) (C := B) (x := z) (y := y) (fun w _ => hd w) (fun w _ => by
        have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := w) (n := 1)
        rw [norm_iteratedFDeriv_one] at e
        rw [e]; exact h2 w) (mem_univ _) (mem_univ _)
    exact this
  rw [hsub]
  have hs : ‖fderiv ℝ f (x + a) - fderiv ℝ f x‖ ≤ 2 * B := by
    have := (norm_sub_le (fderiv ℝ f (x + a)) (fderiv ℝ f x))
    have e1 := hg (x + a)
    have e2 := hg x
    rw [uniqq_grad_norm] at e1 e2
    linarith
  rcases le_total ‖a‖ 1 with ha | ha
  · have h3 := hlip (x + a) x
    rw [add_sub_cancel_left] at h3
    have h4 := uniqq_self_le_rpow (norm_nonneg a) ha hβ1
    calc _ ≤ B * ‖a‖ := h3
      _ ≤ B * ‖a‖ ^ β := mul_le_mul_of_nonneg_left h4 hB
      _ ≤ 2 * B * ‖a‖ ^ β := by
          have : 0 ≤ B * ‖a‖ ^ β := by positivity
          nlinarith
  · have h5 : 1 ≤ ‖a‖ ^ β := Real.one_le_rpow ha hβ0
    calc _ ≤ 2 * B := hs
      _ ≤ 2 * B * ‖a‖ ^ β := by nlinarith

/-- the abstract window estimate: `|S| ≤ m` on `(r₀,t₁)` implies `|S| ≤ m/2` there -/
theorem uniqq_halve {s β C1 C2 KN δ Λ t : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ψ : SchwartzMap (Euc d) ℝ}
    {c : Euc d → Euc d} {u S : ℝ → Euc d → ℝ}
    (hwin : ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
      (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
      (∀ x, ‖gradient (u r) x‖ ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ)) ∧
      (∀ x a, ‖gradient (u r) (x + a) - gradient (u r) x‖ ≤
        C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β))
    (hNL : ∀ {v : Euc d → ℝ}, ContDiff ℝ 2 v → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient v y‖ ≤ G) → (∀ x a, ‖gradient v (x + a) - gradient v x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |ulNL s M ψ v x| ≤ KN * (G + H))
    (hc2 : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u r))
    (hSdef : ∀ r x, S r x = inner ℝ (c x) (gradient (u r) x) - ulNL s M ψ (u r) x)
    (hΛ : ∀ x, ‖c x‖ ≤ Λ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hKN : 0 ≤ KN) (hΛ0 : 0 ≤ Λ)
    (hδ1 : δ ≤ 1)
    (hδ : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ δ → Λ * C1 * ℓ ^ (1 / 2 : ℝ) +
      KN * (C1 * ℓ ^ (1 / 2 : ℝ) + C2 * ℓ ^ ((1 - β) / 2)) ≤ 1 / 2)
    {r0 t1 m : ℝ} (hr0 : 0 ≤ r0) (hrt : r0 < t1) (ht1 : t1 ≤ t) (hl : t1 - r0 ≤ δ)
    (hz : ∀ y, u t1 y = 0) (hm : 0 ≤ m) (hS : ∀ σ ∈ Ioo r0 t1, ∀ x, |S σ x| ≤ m) :
    ∀ σ ∈ Ioo r0 t1, ∀ x, |S σ x| ≤ m / 2 := by
  intro σ hσ x
  have hℓ : 0 < t1 - σ := by linarith [hσ.2]
  have hℓδ : t1 - σ ≤ δ := by linarith [hσ.1]
  obtain ⟨hG, hH⟩ := hwin (r := σ) (t1 := t1) (m := m) (hr0.trans hσ.1.le) hσ.2 ht1 (hℓδ.trans hδ1) hz
    (fun τ hτ y => hS τ ⟨hσ.1.trans hτ.1, hτ.2⟩ y) hm
  set G : ℝ := C1 * m * (t1 - σ) ^ (1 / 2 : ℝ) with hGdef
  set H : ℝ := C2 * m * (t1 - σ) ^ ((1 - β) / 2) with hHdef
  have hG0 : 0 ≤ G := by positivity
  have hH0 : 0 ≤ H := by positivity
  have hσI : σ ∈ Icc (0 : ℝ) t := ⟨hr0.trans hσ.1.le, hσ.2.le.trans ht1⟩
  have hnl := hNL (hc2 σ hσI) hG0 hH0 hG (fun y a => by
    have := hH y a
    calc _ ≤ _ := this
      _ = H * ‖a‖ ^ β := by rw [hHdef])
    x
  rw [hSdef]
  have h1 : |inner ℝ (c x) (gradient (u σ) x)| ≤ Λ * G :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΛ x) (hG x) (norm_nonneg _) hΛ0)
  have h2 := hδ (t1 - σ) hℓ hℓδ
  calc |inner ℝ (c x) (gradient (u σ) x) - ulNL s M ψ (u σ) x|
      ≤ |inner ℝ (c x) (gradient (u σ) x)| + |ulNL s M ψ (u σ) x| := abs_sub _ _
    _ ≤ Λ * G + KN * (G + H) := add_le_add h1 hnl
    _ = m * (Λ * C1 * (t1 - σ) ^ (1 / 2 : ℝ) +
          KN * (C1 * (t1 - σ) ^ (1 / 2 : ℝ) + C2 * (t1 - σ) ^ ((1 - β) / 2))) := by
        rw [hGdef, hHdef]; ring
    _ ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left h2 hm
    _ = m / 2 := by ring

/-- on a short window the solution vanishes -/
theorem uniqq_window_zero {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} (hν : 0 < ν)
    {s β C1 C2 KN δ Λ t : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ψ : SchwartzMap (Euc d) ℝ}
    {c : Euc d → Euc d} {u S : ℝ → Euc d → ℝ} (hu : UqSol Q ν t u S)
    (hwin : ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
      (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
      (∀ x, ‖gradient (u r) x‖ ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ)) ∧
      (∀ x a, ‖gradient (u r) (x + a) - gradient (u r) x‖ ≤
        C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β))
    (hNL : ∀ {v : Euc d → ℝ}, ContDiff ℝ 2 v → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient v y‖ ≤ G) → (∀ x a, ‖gradient v (x + a) - gradient v x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |ulNL s M ψ v x| ≤ KN * (G + H))
    (hSdef : ∀ r x, S r x = inner ℝ (c x) (gradient (u r) x) - ulNL s M ψ (u r) x)
    (hΛ : ∀ x, ‖c x‖ ≤ Λ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hKN : 0 ≤ KN) (hΛ0 : 0 ≤ Λ)
    (hδ1 : δ ≤ 1)
    (hδ : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ δ → Λ * C1 * ℓ ^ (1 / 2 : ℝ) +
      KN * (C1 * ℓ ^ (1 / 2 : ℝ) + C2 * ℓ ^ ((1 - β) / 2)) ≤ 1 / 2)
    {r0 t1 m0 : ℝ} (hr0 : 0 ≤ r0) (hrt : r0 < t1) (ht1 : t1 ≤ t) (hl : t1 - r0 ≤ δ)
    (hz : ∀ y, u t1 y = 0) (hm0 : 0 ≤ m0) (hS0 : ∀ σ ∈ Ioo r0 t1, ∀ x, |S σ x| ≤ m0) :
    ∀ r ∈ Icc r0 t1, ∀ y, u r y = 0 := by
  have hk : ∀ k : ℕ, ∀ σ ∈ Ioo r0 t1, ∀ x, |S σ x| ≤ m0 / 2 ^ k := by
    intro k
    induction k with
    | zero => simpa using hS0
    | succ k ih =>
      have := uniqq_halve hwin hNL (fun r hr => hu.c2 r hr) hSdef hΛ hC1 hC2 hKN hΛ0 hδ1 hδ hr0 hrt ht1 hl hz
        (m := m0 / 2 ^ k) (by positivity) ih
      intro σ hσ x
      calc _ ≤ m0 / 2 ^ k / 2 := this σ hσ x
        _ = m0 / 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hS00 : ∀ σ ∈ Ioo r0 t1, ∀ x, |S σ x| ≤ 0 := by
    intro σ hσ x
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk'⟩ := exists_pow_lt_of_lt_one (x := |S σ x| / (m0 + 1)) (y := (1 / 2 : ℝ))
      (by positivity) (by norm_num)
    have h1 := hk k σ hσ x
    have h2 : m0 / 2 ^ k ≤ (m0 + 1) * (1 / 2) ^ k := by
      rw [one_div, inv_pow, div_eq_mul_inv]
      have : (0 : ℝ) ≤ (2 ^ k)⁻¹ := by positivity
      nlinarith
    have h3 : (m0 + 1) * (1 / 2) ^ k < |S σ x| := by
      rw [lt_div_iff₀ (by positivity)] at hk'
      nlinarith
    linarith
  intro r hr y
  rcases hr.2.eq_or_lt with hrt1 | hrt1
  · rw [hrt1]; exact hz y
  · have hz' : u t1 = fun _ => 0 := funext hz
    have := uniqq_step hν hu (a := r) (b := t1) (m := 0) (hr0.trans hr.1) hrt1 ht1
      (fun σ hσ x => hS00 σ ⟨hr.1.trans_lt hσ.1, hσ.2⟩ x) y
    rw [hz'] at this
    simp only [ouSg, integral_zero, sub_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this

/-- propagation from `t` down to `0` -/
theorem uniqq_propagate {t δ : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) {u : ℝ → Euc d → ℝ}
    (hwindow : ∀ r0 t1 : ℝ, 0 ≤ r0 → r0 < t1 → t1 ≤ t → t1 - r0 ≤ δ → (∀ y, u t1 y = 0) →
      ∀ r ∈ Icc r0 t1, ∀ y, u r y = 0)
    (hz : ∀ y, u t y = 0) : ∀ r ∈ Icc (0 : ℝ) t, ∀ y, u r y = 0 := by
  have hk : ∀ k : ℕ, ∀ r ∈ Icc (0 : ℝ) t, t - k * δ ≤ r → ∀ y, u r y = 0 := by
    intro k
    induction k with
    | zero =>
      intro r hr hr' y
      have : r = t := le_antisymm hr.2 (by simpa using hr')
      rw [this]; exact hz y
    | succ k ih =>
      intro r hr hr' y
      by_cases h1 : t - k * δ ≤ r
      · exact ih r hr h1 y
      · push Not at h1
        set t1 : ℝ := t - k * δ with ht1
        have ht10 : 0 < t1 := lt_of_le_of_lt hr.1 h1
        have ht1t : t1 ≤ t := by rw [ht1]; have : 0 ≤ (k : ℝ) * δ := by positivity
                                 linarith
        have hz1 : ∀ y, u t1 y = 0 := fun y => ih t1 ⟨ht10.le, ht1t⟩ le_rfl y
        refine hwindow (max 0 (t1 - δ)) t1 (le_max_left _ _) ?_ ht1t ?_ hz1 r ⟨?_, h1.le⟩ y
        · exact max_lt ht10 (by linarith)
        · rw [max_def]; split_ifs <;> linarith
        · refine max_le hr.1 ?_
          rw [ht1]
          have : t - ((k + 1 : ℕ) : ℝ) * δ = t - k * δ - δ := by push_cast; ring
          linarith
  intro r hr y
  obtain ⟨k, hk'⟩ := exists_nat_ge (t / δ)
  refine hk k r hr ?_ y
  have : t ≤ k * δ := by
    rw [div_le_iff₀ hδ] at hk'; exact hk'
  linarith [hr.1]

/-- **uniqueness for the abstract class**: a bounded classical solution of `-∂_r u = L₀ u + ⟨c,∇u⟩ - N u`
with `u(t) = 0` vanishes -/
theorem uniqq_zero {Q : Matrix (Fin d) (Fin d) ℝ} {ν s : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} {Λ : ℝ}
    (hΛ : ∀ x, ‖c x‖ ≤ Λ) {t : ℝ} (ht : 0 ≤ t) {u S : ℝ → Euc d → ℝ} (hu : UqSol Q ν t u S)
    (hSdef : ∀ r x, S r x = inner ℝ (c x) (gradient (u r) x) - ulNL s M ψ (u r) x)
    (hz : ∀ y, u t y = 0) : ∀ r ∈ Icc (0 : ℝ) t, ∀ y, u r y = 0 := by
  set β : ℝ := (1 + max 0 (s + 1 - d)) / 2 with hβ
  have hm1 : max 0 (s + 1 - (d : ℝ)) < 1 := max_lt (by norm_num) (by linarith)
  have hβ0 : 0 ≤ β := by
    have := le_max_left 0 (s + 1 - (d : ℝ)); rw [hβ]; linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hβs : s + 1 - d < β := by
    have := le_max_right 0 (s + 1 - (d : ℝ)); rw [hβ]; linarith
  obtain ⟨C1, C2, hC1, hC2, hwin⟩ := uniqq_window Q hν hβ0 hβ1
  obtain ⟨KN, hKN, hNL⟩ := uniqq_nl_bound hs0 hsd hβ0 hβ1 hβs M ψ
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ0 : 0 ≤ Λ' := le_max_right _ _
  have hΛ'b : ∀ x, ‖c x‖ ≤ Λ' := fun x => (hΛ x).trans (le_max_left _ _)
  -- the window length
  set a : ℝ := Λ' * C1 + KN * C1 + KN * C2 with ha
  have ha0 : 0 ≤ a := by positivity
  set p : ℝ := (1 - β) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hev : ∀ᶠ ℓ : ℝ in 𝓝 0, a * ℓ ^ p < 1 / 2 := by
    have hc : ContinuousAt (fun ℓ : ℝ => a * ℓ ^ p) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp0.le))
    refine hc.eventually_lt continuousAt_const ?_
    simp [Real.zero_rpow hp0.ne']
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.1 hev
  set δ : ℝ := min 1 (ε / 2) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ δ → Λ' * C1 * ℓ ^ (1 / 2 : ℝ) +
      KN * (C1 * ℓ ^ (1 / 2 : ℝ) + C2 * ℓ ^ ((1 - β) / 2)) ≤ 1 / 2 := by
    intro ℓ hℓ hℓδ
    have hℓ1 : ℓ ≤ 1 := hℓδ.trans hδ1
    have hle : ℓ ^ (1 / 2 : ℝ) ≤ ℓ ^ p := by
      refine Real.rpow_le_rpow_of_exponent_ge hℓ hℓ1 ?_
      rw [hp]; linarith
    have h1 : a * ℓ ^ p < 1 / 2 := by
      refine hεp ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos hℓ]
      calc ℓ ≤ δ := hℓδ
        _ ≤ ε / 2 := min_le_right _ _
        _ < ε := by linarith
    calc _ ≤ Λ' * C1 * ℓ ^ p + KN * (C1 * ℓ ^ p + C2 * ℓ ^ p) := by
          gcongr
      _ = a * ℓ ^ p := by rw [ha]; ring
      _ ≤ 1 / 2 := h1.le
  -- a uniform bound of the source
  obtain ⟨B, hB⟩ := hu.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) 0 ⟨le_rfl, ht⟩ 0)
  set m0 : ℝ := Λ' * B + KN * (B + 2 * B) with hm0def
  have hm0 : 0 ≤ m0 := by positivity
  have hS0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |S σ x| ≤ m0 := by
    intro σ hσ x
    obtain ⟨hG, hH⟩ := uniqq_hold_of_cb2 (hu.c2 σ hσ) (β := β)
      (fun y => hB 1 (by norm_num) σ hσ y) (fun y => hB 2 (by norm_num) σ hσ y) hβ0 hβ1.le
    have hnl := hNL (hu.c2 σ hσ) hB0 (by positivity : 0 ≤ 2 * B) hG hH x
    rw [hSdef]
    have h1 : |inner ℝ (c x) (gradient (u σ) x)| ≤ Λ' * B :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΛ'b x) (hG x) (norm_nonneg _) hΛ0)
    calc _ ≤ |inner ℝ (c x) (gradient (u σ) x)| + |ulNL s M ψ (u σ) x| := abs_sub _ _
      _ ≤ Λ' * B + KN * (B + 2 * B) := add_le_add h1 hnl
  refine uniqq_propagate hδ0 ht (fun r0 t1 hr0 hrt ht1 hl hz1 => ?_) hz
  exact uniqq_window_zero hν hu (hwin hu) hNL hSdef hΛ'b hC1 hC2 hKN hΛ0 hδ1 hδ hr0 hrt ht1 hl hz1 hm0
    (fun σ hσ x => hS0 σ ⟨hr0.trans hσ.1.le, hσ.2.le.trans ht1⟩ x)

end HRS.MS.UniqQ
