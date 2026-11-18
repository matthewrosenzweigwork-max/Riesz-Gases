import HRS.MS.UniqFAux1

/-!
# UNIQ-F, part 2: uniqueness for a bounded classical solution of `-∂_r u = L₀ u + ⟨c_r,∇u⟩ - N_r(∇u)` with time-dependent `c_r`, `ρ_r`

`uniqf_zero` is the port of `uniqq_zero` (`UniqQAux8`) to a time-dependent bounded drift perturbation `c_r` and a time-dependent
nonlocal term `ulNL s M (ψ_r)`, `ψ_r` good slices with constants `(B,L,I)` independent of `r`.  The window estimate `uniqq_window` and the
propagation `uniqq_propagate` are used unchanged (they are abstract in `S`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqQ

variable {d : ℕ}

/-- the abstract window estimate: `|S| ≤ m` on `(r₀,t₁)` implies `|S| ≤ m/2` there (time-dependent data) -/
theorem uniqf_halve {β C1 C2 KN δ Λ t : ℝ} {c : ℝ → Euc d → Euc d} {NL : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    {u S : ℝ → Euc d → ℝ}
    (hwin : ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
      (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
      (∀ x, ‖gradient (u r) x‖ ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ)) ∧
      (∀ x a, ‖gradient (u r) (x + a) - gradient (u r) x‖ ≤
        C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β))
    (hNL : ∀ r ∈ Icc (0 : ℝ) t, ∀ {v : Euc d → ℝ}, ContDiff ℝ 2 v → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient v y‖ ≤ G) → (∀ x a, ‖gradient v (x + a) - gradient v x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |NL r v x| ≤ KN * (G + H))
    (hc2 : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u r))
    (hSdef : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, S r x = inner ℝ (c r x) (gradient (u r) x) - NL r (u r) x)
    (hΛ : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖c r x‖ ≤ Λ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hKN : 0 ≤ KN) (hΛ0 : 0 ≤ Λ)
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
  have hnl := hNL σ hσI (hc2 σ hσI) hG0 hH0 hG (fun y a => by
    have := hH y a
    calc _ ≤ _ := this
      _ = H * ‖a‖ ^ β := by rw [hHdef])
    x
  rw [hSdef σ hσI x]
  have h1 : |inner ℝ (c σ x) (gradient (u σ) x)| ≤ Λ * G :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΛ σ hσI x) (hG x) (norm_nonneg _) hΛ0)
  have h2 := hδ (t1 - σ) hℓ hℓδ
  calc |inner ℝ (c σ x) (gradient (u σ) x) - NL σ (u σ) x|
      ≤ |inner ℝ (c σ x) (gradient (u σ) x)| + |NL σ (u σ) x| := abs_sub _ _
    _ ≤ Λ * G + KN * (G + H) := add_le_add h1 hnl
    _ = m * (Λ * C1 * (t1 - σ) ^ (1 / 2 : ℝ) +
          KN * (C1 * (t1 - σ) ^ (1 / 2 : ℝ) + C2 * (t1 - σ) ^ ((1 - β) / 2))) := by
        rw [hGdef, hHdef]; ring
    _ ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left h2 hm
    _ = m / 2 := by ring

/-- on a short window the solution vanishes -/
theorem uniqf_window_zero {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} (hν : 0 < ν)
    {β C1 C2 KN δ Λ t : ℝ} {c : ℝ → Euc d → Euc d} {NL : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    {u S : ℝ → Euc d → ℝ} (hu : UqSol Q ν t u S)
    (hwin : ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
      (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
      (∀ x, ‖gradient (u r) x‖ ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ)) ∧
      (∀ x a, ‖gradient (u r) (x + a) - gradient (u r) x‖ ≤
        C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β))
    (hNL : ∀ r ∈ Icc (0 : ℝ) t, ∀ {v : Euc d → ℝ}, ContDiff ℝ 2 v → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient v y‖ ≤ G) → (∀ x a, ‖gradient v (x + a) - gradient v x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |NL r v x| ≤ KN * (G + H))
    (hSdef : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, S r x = inner ℝ (c r x) (gradient (u r) x) - NL r (u r) x)
    (hΛ : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖c r x‖ ≤ Λ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hKN : 0 ≤ KN) (hΛ0 : 0 ≤ Λ)
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
      have := uniqf_halve hwin hNL (fun r hr => hu.c2 r hr) hSdef hΛ hC1 hC2 hKN hΛ0 hδ1 hδ hr0 hrt ht1 hl hz
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

/-- **uniqueness for the abstract class with time-dependent data**: a bounded classical solution of
`-∂_r u = L₀ u + ⟨c_r,∇u⟩ - N_r u` with `u(t) = 0` vanishes, `N_r = ulNL s M ψ_r`, `ψ_r` good slices with uniform constants. -/
theorem uniqf_zero {Q : Matrix (Fin d) (Fin d) ℝ} {ν s : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {ψ : ℝ → Euc d → ℝ} {B L I : ℝ} {t : ℝ}
    (hψ : ∀ r ∈ Icc (0 : ℝ) t, UqfGood (ψ r) B L I)
    {c : ℝ → Euc d → Euc d} {Λ : ℝ} (hΛ : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖c r x‖ ≤ Λ)
    (ht : 0 ≤ t) {u S : ℝ → Euc d → ℝ} (hu : UqSol Q ν t u S)
    (hSdef : ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
      S r x = inner ℝ (c r x) (gradient (u r) x) - ulNL s M (ψ r) (u r) x)
    (hz : ∀ y, u t y = 0) : ∀ r ∈ Icc (0 : ℝ) t, ∀ y, u r y = 0 := by
  set β : ℝ := (1 + max 0 (s + 1 - d)) / 2 with hβ
  have hm1 : max 0 (s + 1 - (d : ℝ)) < 1 := max_lt (by norm_num) (by linarith)
  have hβ0 : 0 ≤ β := by
    have := le_max_left 0 (s + 1 - (d : ℝ)); rw [hβ]; linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hβs : s + 1 - d < β := by
    have := le_max_right 0 (s + 1 - (d : ℝ)); rw [hβ]; linarith
  obtain ⟨C1, C2, hC1, hC2, hwin⟩ := uniqq_window Q hν hβ0 hβ1
  obtain ⟨KN, hKN, hNL0⟩ := uniqf_nl_bound hs0 hsd hβ0 hβ1 hβs M B L I
  have hNL : ∀ r ∈ Icc (0 : ℝ) t, ∀ {v : Euc d → ℝ}, ContDiff ℝ 2 v → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient v y‖ ≤ G) → (∀ x a, ‖gradient v (x + a) - gradient v x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |ulNL s M (ψ r) v x| ≤ KN * (G + H) :=
    fun r hr {v} hv {G H} hG hH hGb hHb x => hNL0 (hψ r hr) hv hG hH hGb hHb x
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ0 : 0 ≤ Λ' := le_max_right _ _
  have hΛ'b : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖c r x‖ ≤ Λ' := fun r hr x => (hΛ r hr x).trans (le_max_left _ _)
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
  obtain ⟨B', hB'⟩ := hu.bdd
  have hB0 : 0 ≤ B' := (norm_nonneg _).trans (hB' 0 (by norm_num) 0 ⟨le_rfl, ht⟩ 0)
  set m0 : ℝ := Λ' * B' + KN * (B' + 2 * B') with hm0def
  have hm0 : 0 ≤ m0 := by positivity
  have hS0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |S σ x| ≤ m0 := by
    intro σ hσ x
    obtain ⟨hG, hH⟩ := uniqq_hold_of_cb2 (hu.c2 σ hσ) (β := β)
      (fun y => hB' 1 (by norm_num) σ hσ y) (fun y => hB' 2 (by norm_num) σ hσ y) hβ0 hβ1.le
    have hnl := hNL σ hσ (hu.c2 σ hσ) hB0 (by positivity : 0 ≤ 2 * B') hG hH x
    rw [hSdef σ hσ x]
    have h1 : |inner ℝ (c σ x) (gradient (u σ) x)| ≤ Λ' * B' :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΛ'b σ hσ x) (hG x) (norm_nonneg _) hΛ0)
    calc _ ≤ |inner ℝ (c σ x) (gradient (u σ) x)| + |ulNL s M (ψ σ) (u σ) x| := abs_sub _ _
      _ ≤ Λ' * B' + KN * (B' + 2 * B') := add_le_add h1 hnl
  refine uniqq_propagate hδ0 ht (fun r0 t1 hr0 hrt ht1 hl hz1 => ?_) hz
  exact uniqf_window_zero hν hu (hwin hu) hNL hSdef hΛ'b hC1 hC2 hKN hΛ0 hδ1 hδ hr0 hrt ht1 hl hz1 hm0
    (fun σ hσ x => hS0 σ ⟨hr0.trans hσ.1.le, hσ.2.le.trans ht1⟩ x)

end HRS.MS.UniqF
