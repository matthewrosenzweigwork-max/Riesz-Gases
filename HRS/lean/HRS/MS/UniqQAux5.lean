import HRS.MS.UniqQAux4

/-!
# UNIQ-Q, part 5: the window estimate (gradient and Hölder smoothing of `u` from a bound on the source)

(plan: `UniqQAux1`.)  For a bounded classical solution `u` of `-∂_r u = L₀u + S` on `[0,t]`, `u(t₁) = 0`,
`|S| ≤ m` on `(r,t₁)`, `ℓ = t₁ - r ≤ 1`:
`|u(r,x+e) - u(r,x)| ≤ C₁ m ℓ^{1/2} |e|` and the second difference
`|Δ_aΔ_e u(r,x)| ≤ C₂ m ℓ^{(1-β)/2} |a|^β |e|`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem uniqq_le_of_lim {X Y c : ℝ} (hc : 0 ≤ c) (h : ∀ n : ℕ, X ≤ c / ((n : ℝ) + 1) + Y) : X ≤ Y := by
  by_contra hXY
  push Not at hXY
  have hpos : 0 < X - Y := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (c / (X - Y))
  have h1 : c < (X - Y) * n := by
    rw [div_lt_iff₀ hpos] at hn; linarith
  have h2 : c / ((n : ℝ) + 1) < X - Y := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have := h n
  linarith

theorem uniqq_sum_bound {γ c m ℓ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hc : 0 ≤ c) (hm : 0 ≤ m) (hℓ : 0 < ℓ)
    (n' : ℕ) :
    ∑ i ∈ Finset.range n', c * ((((i + 1 : ℕ) : ℝ) * (ℓ / ((n' : ℝ) + 1))) ^ (-γ)) *
        (ℓ / ((n' : ℝ) + 1) * m) ≤ c * m * ℓ ^ (1 - γ) / (1 - γ) := by
  have hp : 0 < 1 - γ := by linarith
  set h : ℝ := ℓ / ((n' : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
  have hterm : ∀ i : ℕ, c * ((((i + 1 : ℕ) : ℝ) * h) ^ (-γ)) * (h * m) =
      c * m * h ^ (1 - γ) * (((i + 1 : ℕ) : ℝ) ^ (-γ)) := by
    intro i
    have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    rw [Real.mul_rpow hi.le hh0.le, show 1 - γ = -γ + 1 by ring, Real.rpow_add hh0, Real.rpow_one]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hs := uniqq_sum_rpow hγ0 hγ1 n'
  have hcm : 0 ≤ c * m * h ^ (1 - γ) := by positivity
  calc c * m * h ^ (1 - γ) * ∑ i ∈ Finset.range n', (((i + 1 : ℕ) : ℝ)) ^ (-γ)
      ≤ c * m * h ^ (1 - γ) * ((n' : ℝ) ^ (1 - γ) / (1 - γ)) := mul_le_mul_of_nonneg_left hs hcm
    _ = c * m * (h * n') ^ (1 - γ) / (1 - γ) := by
        rw [Real.mul_rpow hh0.le (Nat.cast_nonneg n')]; ring
    _ ≤ c * m * ℓ ^ (1 - γ) / (1 - γ) := by
        have : h * n' ≤ ℓ := by
          rw [hh, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n']
        have h2 : (h * n') ^ (1 - γ) ≤ ℓ ^ (1 - γ) :=
          Real.rpow_le_rpow (by positivity) this hp.le
        gcongr

/-- uniform `UqCB1` bounds of a solution -/
theorem uniqq_sol_cb1 {Q : Matrix (Fin d) (Fin d) ℝ} {ν t : ℝ} {u S : ℝ → Euc d → ℝ}
    (hu : UqSol Q ν t u S) : ∃ Bv Mv : ℝ, ∀ r ∈ Icc 0 t, UqCB1 (u r) Bv Mv := by
  obtain ⟨B, hB⟩ := hu.bdd
  refine ⟨B, B, fun r hr => ⟨(hu.c2 r hr).of_le (by norm_num), fun y => ?_, fun y => ?_⟩⟩
  · have := hB 0 (by norm_num) r hr y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hB 1 (by norm_num) r hr y
    rwa [norm_iteratedFDeriv_one] at this

/-- the discrete Duhamel decomposition of `u(r)` on a window -/
theorem uniqq_decomp {Q : Matrix (Fin d) (Fin d) ℝ} {ν t : ℝ} (hν : 0 < ν) {u S : ℝ → Euc d → ℝ}
    (hu : UqSol Q ν t u S) {r t1 m : ℝ} (hr0 : 0 ≤ r) (hrt : r < t1) (ht1 : t1 ≤ t)
    (hl : t1 - r ≤ 1) (hz : ∀ y, u t1 y = 0) (hS : ∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) (n' : ℕ) :
    ∃ (E : ℕ → Euc d → ℝ) (Me : ℝ),
      (∀ i, i ≤ n' → UqCB1 (E i) ((t1 - r) / ((n' : ℝ) + 1) * m) Me) ∧
      ∀ y, u r y = ∑ i ∈ Finset.range (n' + 1),
        ouSg Q ν ((i : ℝ) * ((t1 - r) / ((n' : ℝ) + 1))) (E i) y := by
  obtain ⟨Bv, Mv, hcb⟩ := uniqq_sol_cb1 hu
  obtain ⟨K, hK1, hK⟩ := ul2_exp_bound Q 1
  set h : ℝ := (t1 - r) / ((n' : ℝ) + 1) with hh
  have hn1 : (1 : ℝ) ≤ (n' : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n']
  have hh0 : 0 < h := div_pos (by linarith) (by linarith)
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_iff₀ (by linarith)]; nlinarith
  have hKh : ‖ouExp Q h‖ ≤ K := hK h (by rw [abs_of_pos hh0]; exact hh1)
  have hnh : ((n' : ℝ) + 1) * h = t1 - r := by rw [hh]; field_simp
  set v : ℕ → Euc d → ℝ := fun k => u (min (r + (k : ℝ) * h) t1) with hv
  have hmem : ∀ k : ℕ, min (r + (k : ℝ) * h) t1 ∈ Icc (0 : ℝ) t := fun k =>
    ⟨le_min (by have : 0 ≤ (k : ℝ) * h := by positivity
                linarith) (hr0.trans hrt.le), (min_le_right _ _).trans ht1⟩
  have hvcb : ∀ k, UqCB1 (v k) Bv Mv := fun k => hcb _ (hmem k)
  have hkn : ∀ i : ℕ, i ≤ n' + 1 → r + (i : ℝ) * h ≤ t1 := by
    intro i hi
    have : (i : ℝ) ≤ (n' : ℝ) + 1 := by exact_mod_cast hi
    nlinarith
  have hvi : ∀ i : ℕ, i ≤ n' + 1 → v i = u (r + (i : ℝ) * h) := fun i hi => by
    simp only [hv]; rw [min_eq_left (hkn i hi)]
  have hv0 : v 0 = u r := by simp [hv, min_eq_left hrt.le]
  have hvn : v (n' + 1) = fun _ => 0 := by
    funext y
    have := hvi (n' + 1) le_rfl
    rw [this]
    have e : r + ((n' + 1 : ℕ) : ℝ) * h = t1 := by push_cast; linarith
    rw [e]; exact hz y
  have hP : ∀ k, UqCB1 (ouSg Q ν h (v (k + 1))) Bv (Mv * K) := fun k =>
    uniqq_cb1_ouSg Q ν hKh (hvcb (k + 1))
  refine ⟨fun i z => v i z - ouSg Q ν h (v (i + 1)) z, Mv + Mv * K, fun i hi => ?_, fun y => ?_⟩
  · have hE := uniqq_cb1_sub (hvcb i) (hP i)
    refine ⟨hE.1, fun y => ?_, hE.2.2⟩
    have hi1 : i + 1 ≤ n' + 1 := by omega
    have hi0 : i ≤ n' + 1 := by omega
    have hmono : r + (i : ℝ) * h < r + ((i + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hst := uniqq_step hν hu (a := r + (i : ℝ) * h) (b := r + ((i + 1 : ℕ) : ℝ) * h) (m := m)
      (by have : 0 ≤ (i : ℝ) * h := by positivity
          linarith) hmono (le_trans (hkn _ hi1) ht1)
      (fun σ hσ x => hS σ ⟨by
          have : 0 ≤ (i : ℝ) * h := by positivity
          linarith [hσ.1], lt_of_lt_of_le hσ.2 (hkn _ hi1)⟩ x) y
    have e : r + ((i + 1 : ℕ) : ℝ) * h - (r + (i : ℝ) * h) = h := by push_cast; ring
    rw [e, ← hvi i hi0, ← hvi (i + 1) hi1] at hst
    exact hst
  · have := uniqq_tel Q hν.le hh0.le hKh hvcb y (n' + 1)
    rw [hv0, hvn] at this
    simpa [ouSg] using this

/-- **gradient smoothing on a window** -/
theorem uniqq_first (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ {t : ℝ} {u S : ℝ → Euc d → ℝ}, UqSol Q ν t u S →
      ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
        (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
        ∀ x e : Euc d, |u r (x + e) - u r x| ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ) * ‖e‖ := by
  obtain ⟨Cl, hCl0, hCl⟩ := uniqq_lip Q hν 1
  refine ⟨2 * Cl, by positivity, fun {t u S} hu {r t1 m} hr0 hrt ht1 hl hz hS hm x e => ?_⟩
  have hℓ : 0 < t1 - r := by linarith
  refine uniqq_le_of_lim (c := 2 * (t1 - r) * m) (by positivity) fun n' => ?_
  obtain ⟨E, Me, hE, hdec⟩ := uniqq_decomp hν hu hr0 hrt ht1 hl hz hS n'
  set h : ℝ := (t1 - r) / ((n' : ℝ) + 1) with hh
  have hn1 : (1 : ℝ) ≤ (n' : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n']
  have hh0 : 0 < h := div_pos hℓ (by linarith)
  have hdiff : u r (x + e) - u r x = ∑ i ∈ Finset.range n',
      (ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) (x + e) - ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) x) +
      (E 0 (x + e) - E 0 x) := by
    rw [hdec, hdec, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    simp [ouSg_zero Q hν.le]
  rw [hdiff]
  have h0 : |E 0 (x + e) - E 0 x| ≤ 2 * h * m := by
    have h1 := (hE 0 (Nat.zero_le _)).2.1 (x + e)
    have h2 := (hE 0 (Nat.zero_le _)).2.1 x
    calc _ ≤ |E 0 (x + e)| + |E 0 x| := abs_sub _ _
      _ ≤ _ := by linarith
  have hsum : ∀ i ∈ Finset.range n', |ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) (x + e) -
      ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) x| ≤
      ‖e‖ * (Cl * (((i + 1 : ℕ) : ℝ) * h) ^ (-(1 / 2 : ℝ)) * (h * m)) := by
    intro i hi
    have hi' : i + 1 ≤ n' := Finset.mem_range.1 hi
    have hτ : 0 < ((i + 1 : ℕ) : ℝ) * h := by positivity
    have hτ1 : ((i + 1 : ℕ) : ℝ) * h ≤ 1 := by
      have : ((i + 1 : ℕ) : ℝ) ≤ (n' : ℝ) + 1 := by exact_mod_cast (by omega : i + 1 ≤ n' + 1)
      have hnh : ((n' : ℝ) + 1) * h = t1 - r := by rw [hh]; field_simp
      nlinarith
    have := hCl _ hτ hτ1 (E (i + 1)) _ _ (hE (i + 1) hi') (x + e) x
    rw [add_sub_cancel_left] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  calc |∑ i ∈ Finset.range n', (ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) (x + e) -
        ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) x) + (E 0 (x + e) - E 0 x)|
      ≤ |∑ i ∈ Finset.range n', (ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) (x + e) -
        ouSg Q ν (((i + 1 : ℕ) : ℝ) * h) (E (i + 1)) x)| + |E 0 (x + e) - E 0 x| := abs_add_le _ _
    _ ≤ ∑ i ∈ Finset.range n', ‖e‖ * (Cl * (((i + 1 : ℕ) : ℝ) * h) ^ (-(1 / 2 : ℝ)) * (h * m)) + 2 * h * m :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hsum)) h0
    _ = ‖e‖ * ∑ i ∈ Finset.range n', Cl * (((i + 1 : ℕ) : ℝ) * h) ^ (-(1 / 2 : ℝ)) * (h * m) + 2 * h * m := by
        rw [Finset.mul_sum]
    _ ≤ ‖e‖ * (Cl * m * (t1 - r) ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2)) + 2 * h * m := by
        gcongr
        exact uniqq_sum_bound (γ := 1 / 2) (by norm_num) (by norm_num) hCl0 hm hℓ n'
    _ = 2 * (t1 - r) * m / ((n' : ℝ) + 1) + 2 * Cl * m * (t1 - r) ^ (1 / 2 : ℝ) * ‖e‖ := by
        rw [hh]; norm_num; ring

/-- **Hölder smoothing of the gradient on a window** (second differences) -/
theorem uniqq_second (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ {t : ℝ} {u S : ℝ → Euc d → ℝ}, UqSol Q ν t u S →
      ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
        (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
        ∀ x a e : Euc d, |u r (x + a + e) - u r (x + a) - u r (x + e) + u r x| ≤
          C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β * ‖e‖ := by
  obtain ⟨C3, hC30, hC3⟩ := uniqq_second_diff Q hν 1 hβ0 hβ1.le
  have hγ1 : (1 + β) / 2 < 1 := by linarith
  have hγ0 : 0 ≤ (1 + β) / 2 := by linarith
  refine ⟨C3 / (1 - (1 + β) / 2), by
    have : 0 < 1 - (1 + β) / 2 := by linarith
    positivity, fun {t u S} hu {r t1 m} hr0 hrt ht1 hl hz hS hm x a e => ?_⟩
  have hℓ : 0 < t1 - r := by linarith
  refine uniqq_le_of_lim (c := 4 * (t1 - r) * m) (by positivity) fun n' => ?_
  obtain ⟨E, Me, hE, hdec⟩ := uniqq_decomp hν hu hr0 hrt ht1 hl hz hS n'
  set h : ℝ := (t1 - r) / ((n' : ℝ) + 1) with hh
  have hn1 : (1 : ℝ) ≤ (n' : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n']
  have hh0 : 0 < h := div_pos hℓ (by linarith)
  set F : ℕ → Euc d → ℝ := fun i => ouSg Q ν ((i : ℝ) * h) (E i) with hF
  have hdiff : u r (x + a + e) - u r (x + a) - u r (x + e) + u r x = ∑ i ∈ Finset.range n',
      (F (i + 1) (x + a + e) - F (i + 1) (x + a) - F (i + 1) (x + e) + F (i + 1) x) +
      (E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e) + E 0 x) := by
    rw [hdec, hdec, hdec, hdec]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ']
    simp [hF, ouSg_zero Q hν.le]
  rw [hdiff]
  have h0 : |E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e) + E 0 x| ≤ 4 * h * m := by
    have b := fun y => (hE 0 (Nat.zero_le _)).2.1 y
    have := abs_sub (E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e)) (-(E 0 x))
    have h1 := abs_sub (E 0 (x + a + e) - E 0 (x + a)) (E 0 (x + e))
    have h2 := abs_sub (E 0 (x + a + e)) (E 0 (x + a))
    have h3 := b (x + a + e)
    have h4 := b (x + a)
    have h5 := b (x + e)
    have h6 := b x
    have h7 := abs_add_le (E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e)) (E 0 x)
    linarith
  have hsum : ∀ i ∈ Finset.range n',
      |F (i + 1) (x + a + e) - F (i + 1) (x + a) - F (i + 1) (x + e) + F (i + 1) x| ≤
      (‖a‖ ^ β * ‖e‖) * (C3 * (((i + 1 : ℕ) : ℝ) * h) ^ (-((1 + β) / 2)) * (h * m)) := by
    intro i hi
    have hi' : i + 1 ≤ n' := Finset.mem_range.1 hi
    have hτ : 0 < ((i + 1 : ℕ) : ℝ) * h := by positivity
    have hτ1 : ((i + 1 : ℕ) : ℝ) * h ≤ 1 := by
      have : ((i + 1 : ℕ) : ℝ) ≤ (n' : ℝ) + 1 := by exact_mod_cast (by omega : i + 1 ≤ n' + 1)
      have hnh : ((n' : ℝ) + 1) * h = t1 - r := by rw [hh]; field_simp
      nlinarith
    have := hC3 _ hτ hτ1 (E (i + 1)) _ _ (hE (i + 1) hi') x a e
    calc _ ≤ _ := this
      _ = _ := by ring
  have hmain : ∑ i ∈ Finset.range n', (‖a‖ ^ β * ‖e‖) *
      (C3 * (((i + 1 : ℕ) : ℝ) * h) ^ (-((1 + β) / 2)) * (h * m)) ≤
      (‖a‖ ^ β * ‖e‖) * (C3 * m * (t1 - r) ^ (1 - (1 + β) / 2) / (1 - (1 + β) / 2)) := by
    rw [← Finset.mul_sum]
    gcongr
    exact uniqq_sum_bound hγ0 hγ1 hC30 hm hℓ n'
  calc |∑ i ∈ Finset.range n', (F (i + 1) (x + a + e) - F (i + 1) (x + a) - F (i + 1) (x + e) + F (i + 1) x) +
        (E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e) + E 0 x)|
      ≤ |∑ i ∈ Finset.range n', (F (i + 1) (x + a + e) - F (i + 1) (x + a) - F (i + 1) (x + e) +
          F (i + 1) x)| + |E 0 (x + a + e) - E 0 (x + a) - E 0 (x + e) + E 0 x| := abs_add_le _ _
    _ ≤ ∑ i ∈ Finset.range n', (‖a‖ ^ β * ‖e‖) *
          (C3 * (((i + 1 : ℕ) : ℝ) * h) ^ (-((1 + β) / 2)) * (h * m)) + 4 * h * m :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hsum)) h0
    _ ≤ (‖a‖ ^ β * ‖e‖) * (C3 * m * (t1 - r) ^ (1 - (1 + β) / 2) / (1 - (1 + β) / 2)) + 4 * h * m :=
        add_le_add hmain le_rfl
    _ = 4 * (t1 - r) * m / ((n' : ℝ) + 1) +
          C3 / (1 - (1 + β) / 2) * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β * ‖e‖ := by
        rw [hh, show 1 - (1 + β) / 2 = (1 - β) / 2 by ring]
        ring

end HRS.MS.UniqQ
