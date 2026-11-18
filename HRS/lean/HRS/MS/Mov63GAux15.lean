import HRS.MS.Mov63GAux14

/-!
# S6.3, packet N8 (part 15): the core estimate `‖D^i Q_t‖ ≤ C K e^{-ct}`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mng_core`**: for the mild solution `v` with `‖v_t‖ ≤ C_v K e^{-c₁ t}`, `Q_t ∈ [1/2,2]` and `‖D^i Q_0‖ ≤ K`
(`1 ≤ i ≤ N`): `‖D^i Q_t(x)‖ ≤ C K e^{-ct}` for `1 ≤ i ≤ N`, `0 < c ≤ c₁`; the constants `δ₀, c, C` depend only on `(H, m, N, C_v, c₁)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Core

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

set_option maxHeartbeats 3200000 in
include H hm in
theorem mng_core {N : ℕ} (hN1 : 1 ≤ N) (hN : (d : ℝ) / 2 + N + 2 < m) (Cv c1 : ℝ) (hCv : 0 ≤ Cv) (hc1 : 0 < c1) :
    ∃ δ0 c C : ℝ, 0 < δ0 ∧ 0 < c ∧ c ≤ c1 ∧ 0 ≤ C ∧
      ∀ v : ℝ → OscSpace d (m : ℝ), MneMild H hm v → ∀ K : ℝ, 0 ≤ K → K ≤ 1 → Cv * K ≤ δ0 →
        (∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K * Real.exp (-c1 * t)) →
        (∀ t, 0 ≤ t → ∀ x, 1 / 2 ≤ mneQ ρ hm (v t) x ∧ mneQ ρ hm (v t) x ≤ 2) →
        (∀ i, 1 ≤ i → i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (mneQ ρ hm (v 0)) x‖ ≤ K) →
        ∀ t, 0 ≤ t → ∀ i, 1 ≤ i → i ≤ N → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ i (mneQ ρ hm (v t)) x‖ ≤ C * K * Real.exp (-c * t) := by
  obtain ⟨δ0, c, CL, hδ0, hc, hcc1, hCL0, hlip⟩ := mng_lip_conc H hm hN1 hN Cv c1 hCv hc1
  obtain ⟨C0, Cg, hC00, hCg0, hSys⟩ := mng_conc_sys H hm hN1 hN
  have hβ := H.hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set Mb : ℝ := β⁻¹ * Cg + C0 * Cv with hMb
  set MA : ℝ := C0 * Cv with hMA
  set D0 : ℝ := (d : ℝ) ^ N with hD0
  set C1 : ℝ := d * CL ^ 2 with hC1
  set Cx : ℝ := mngCxSeq d β⁻¹ Mb MA 2 c C1 D0 (N - 1) with hCx
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  have hMA0 : 0 ≤ MA := by rw [hMA]; positivity
  have hCx0 : 0 ≤ Cx := mngCxSeq_nonneg (D0 := D0) hν hMb0 hMA0 (by norm_num) hc (by rw [hC1]; positivity) _
  obtain ⟨M0, hM00, hM0⟩ := mnf_M0 hm H
  obtain ⟨CF, hCF0, hCF⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  refine ⟨δ0, c, Real.sqrt ((d : ℝ) ^ N * Cx), hδ0, hc, hcc1, Real.sqrt_nonneg _, ?_⟩
  intro v hmild K hK0 hK1 hCvK hvd hQ hinit t0 ht0 i hi1 hiN x0
  have hex : ∀ t, 0 ≤ t → Real.exp (-c * t) ≤ Real.exp (-c1 * t) → True := fun _ _ _ => trivial
  have hvd' : ∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K * Real.exp (-c * t) := fun t ht => by
    refine (hvd t ht).trans ?_
    have : Real.exp (-c1 * t) ≤ Real.exp (-c * t) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : 0 ≤ Cv * K := by positivity
    exact mul_le_mul_of_nonneg_left this h2
  have hvb : ∀ t, 0 ≤ t → ‖v t‖ ≤ Cv := fun t ht => by
    refine (hvd' t ht).trans ?_
    have h1 : Real.exp (-c * t) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
    have h2 : 0 ≤ K * Real.exp (-c * t) := by positivity
    nlinarith [mul_le_mul hK1 h1 (Real.exp_pos _).le zero_le_one]
  have hQb : ∀ t, 0 ≤ t → ∀ x, |mneQ ρ hm (v t) x| ≤ 2 := fun t ht x =>
    abs_le.2 ⟨by linarith [(hQ t ht x).1], (hQ t ht x).2⟩
  have hS := hSys hmild hK0 hK1 hCv hc (by norm_num : (0 : ℝ) ≤ 2) hvd' hQb
  set Qf : ℝ → Euc d → ℝ := fun t => mneQ ρ hm (v t) with hQf
  have hQcd : ∀ t, ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (Qf t) := fun t => mng_Q_cd H hm hN (v t)
  have ha : ∀ t, (fun t => K * Real.exp (-c * t)) t = K * Real.exp (-c * t) := fun t => rfl
  -- stage A
  have hlip' := hlip v hmild K hK0 hK1 hCvK hvd hQ (fun x => by
    have := hinit 1 le_rfl hN1 x
    exact this)
  have hS1 : ∀ t, 0 ≤ t → ∀ x, mngS Qf 1 t x ≤ C1 * (K * Real.exp (-c * t)) ^ 2 := by
    intro t ht x
    have h1 := mng_S_le_norm_sq (Q := Qf) (N := N + 2) hQcd (by omega : 1 ≤ N + 2) t x
    have hL0 : 0 ≤ CL * K * Real.exp (-c * t) := by positivity
    have h2 : ‖iteratedFDeriv ℝ 1 (Qf t) x‖ ≤ CL * K * Real.exp (-c * t) := by
      rw [norm_iteratedFDeriv_one]
      exact mng_fderiv_le_of_lip hL0 (fun x y => hlip' t ht x y) x
    have h3 : ‖iteratedFDeriv ℝ 1 (Qf t) x‖ ^ 2 ≤ (CL * K * Real.exp (-c * t)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc mngS Qf 1 t x ≤ (d : ℝ) ^ 1 * ‖iteratedFDeriv ℝ 1 (Qf t) x‖ ^ 2 := h1
      _ ≤ (d : ℝ) ^ 1 * (CL * K * Real.exp (-c * t)) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = C1 * (K * Real.exp (-c * t)) ^ 2 := by rw [hC1]; ring
  -- initial data
  have hinit' : ∀ m', 1 ≤ m' → m' ≤ N → ∀ x, mngS Qf m' 0 x ≤ D0 * K ^ 2 := by
    intro m' hm1 hmN x
    have h1 := mng_S_le_norm_sq (Q := Qf) (N := N + 2) hQcd (by omega : m' ≤ N + 2) 0 x
    have h2 := hinit m' hm1 hmN x
    have h3 : ‖iteratedFDeriv ℝ m' (Qf 0) x‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc mngS Qf m' 0 x ≤ (d : ℝ) ^ m' * ‖iteratedFDeriv ℝ m' (Qf 0) x‖ ^ 2 := h1
      _ ≤ (d : ℝ) ^ m' * K ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (d : ℝ) ^ N * K ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
          exact pow_le_pow_right₀ hd0 hmN
  -- dissipativity
  have hdiss : ∀ t, 0 ≤ t → ∀ x, inner ℝ (mngBv (fun k t x => (mnfb d s β ρ hm (v t) x) k) t x) x ≤
      -q * ‖x‖ ^ 2 + (M0 + CF * Cv) * ‖x‖ := by
    intro t ht x
    have e : mngBv (fun k t x => (mnfb d s β ρ hm (v t) x) k) t x = mnfb d s β ρ hm (v t) x := by
      ext k; simp [mngBv]
    rw [e]
    have hb := mnf_drift_bound hm H hM0 (fun u x => (hCF u).2.1 x) (v t) x
    refine hb.trans ?_
    have : M0 + CF * ‖v t‖ ≤ M0 + CF * Cv := by
      have := mul_le_mul_of_nonneg_left (hvb t ht) hCF0
      linarith
    nlinarith [norm_nonneg x]
  have hgrow := mng_growth_conc H hm hN Cv hvb hQb
  have hcasc := mng_cascade (d := d) hd1 hS hν H.hq hc hK0 (fun t => rfl) hdiss
    (fun T hT => by
      obtain ⟨Kp, κ0, hKp, hκ0, hg⟩ := hgrow T
      exact ⟨Kp, κ0, hKp, hκ0, hg⟩)
    (by positivity : 0 ≤ D0) hinit' (C1 := C1) (by rw [hC1]; positivity) hS1
  -- conclusion
  have hSx : mngSx Qf N t0 x0 ≤ Cx * (K * Real.exp (-c * t0)) ^ 2 := by
    have := hcasc (N - 1) (by omega) t0 ht0 x0
    rwa [show N - 1 + 1 = N by omega] at this
  have hSi : mngS Qf i t0 x0 ≤ mngSx Qf N t0 x0 := by
    unfold mngSx
    have := Finset.single_le_sum (f := fun k => mngS Qf (k + 1) t0 x0) (fun k _ => mngS_nonneg Qf (k + 1) t0 x0)
      (Finset.mem_range.2 (by omega : i - 1 < N))
    simpa [Nat.sub_add_cancel hi1] using this
  have h1 := mng_S_le_norm_sq (Q := Qf) (N := N + 2) hQcd (by omega : i ≤ N + 2) t0 x0
  have hdi : (d : ℝ) ^ i ≤ (d : ℝ) ^ N := pow_le_pow_right₀ hd0 hiN
  have hsq : ‖iteratedFDeriv ℝ i (Qf t0) x0‖ ^ 2 ≤ (d : ℝ) ^ N * Cx * (K * Real.exp (-c * t0)) ^ 2 := by
    -- ‖D^i‖² ≤ d^i S_i : we only have S_i ≥ ... ; use the bound S_i ≥ ‖D^i‖²/d^i
    have h2 := mng_norm_iter_sq_le (Q := Qf) (N := N + 2) hQcd (by omega : i ≤ N + 2) t0 x0
    calc _ ≤ (d : ℝ) ^ i * mngS Qf i t0 x0 := h2
      _ ≤ (d : ℝ) ^ N * mngS Qf i t0 x0 := mul_le_mul_of_nonneg_right hdi (mngS_nonneg _ _ _ _)
      _ ≤ (d : ℝ) ^ N * (Cx * (K * Real.exp (-c * t0)) ^ 2) :=
          mul_le_mul_of_nonneg_left (hSi.trans hSx) (by positivity)
      _ = _ := by ring
  have hsqrt : ((Real.sqrt ((d : ℝ) ^ N * Cx)) * (K * Real.exp (-c * t0))) ^ 2 =
      (d : ℝ) ^ N * Cx * (K * Real.exp (-c * t0)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hfin : ‖iteratedFDeriv ℝ i (Qf t0) x0‖ ≤ (Real.sqrt ((d : ℝ) ^ N * Cx)) * (K * Real.exp (-c * t0)) := by
    refine le_of_sq_le_sq (by rw [hsqrt]; exact hsq) (by positivity)
  calc ‖iteratedFDeriv ℝ i (mneQ ρ hm (v t0)) x0‖ ≤ _ := hfin
    _ = _ := by ring

end Core

end HRS.MS.Mov63

end
