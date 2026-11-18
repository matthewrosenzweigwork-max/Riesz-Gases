import HRS.MS.BilipVAux2
import HRS.MS.QMul
import HRS.MS.SobMul
import HRS.MS.UlocCutAux1
import HRS.MS.FlowEAux1
import HRS.Whole.AppendixA

/-!
# MS-BILIP-V, part 3: the two covering estimates for `sup_z ‖χ(Φinv · - z) F‖_{H^m}` versus `‖F‖_{H^m_uloc}`

Route and constants: `BilipVPlan.md`.  `BvData` collects the properties of a pair `(Φ, Φinv) = (Ψ τ, Ψinv τ)` used.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA

namespace HRS.MS.BilipV

variable {d : ℕ}

/-- the properties of `(Φ, Φinv) = (Ψ τ, Ψinv τ)` that are used -/
structure BvData (m : ℕ) (χ : Euc d → ℝ) (L D B : ℝ) (Φ Φinv : Euc d → Euc d) : Prop where
  inv2 : ∀ y, Φ (Φinv y) = y
  lipΦ : ∀ x x', ‖Φ x - Φ x'‖ ≤ L * ‖x - x'‖
  lipI : ∀ y y', ‖Φinv y - Φinv y'‖ ≤ L * ‖y - y'‖
  smooth : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Φinv
  der : ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i Φinv x‖ ≤ D
  cb : ∀ z, MemCb (m + 1) (fun x => χ (Φinv x - z)) ∧ cbNorm (m + 1) (fun x => χ (Φinv x - z)) ≤ B

theorem bv_cb_mono {θ : Euc d → ℝ} {m : ℕ} (h : MemCb (m + 1) θ) :
    MemCb m θ ∧ cbNorm m θ ≤ cbNorm (m + 1) θ := by
  refine ⟨⟨h.1.of_le (by exact_mod_cast Nat.le_succ m), fun j hj => h.2 j (hj.trans (Nat.le_succ m))⟩, ?_⟩
  unfold cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ (m + 1)))
    (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

/-- pointwise partition identity for the upper bound -/
theorem bv_id_up {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {ρ : Euc d → ℝ} {s r L : ℝ}
    (hLr : L * r = 1) (hL : 0 < L) (hρ0 : ∀ y, r ≤ ‖y‖ → ρ y = 0)
    (hpou : ∀ (y : Euc d) (K : Finset (Fin d → ℤ)), (∀ k, ‖y - bv_pt s k‖ < r → k ∈ K) →
      ∑ k ∈ K, ρ (y - bv_pt s k) = 1)
    {Φ Φinv : Euc d → Euc d} (hinv2 : ∀ y, Φ (Φinv y) = y)
    (hlipΦ : ∀ x x', ‖Φ x - Φ x'‖ ≤ L * ‖x - x'‖) (z : Euc d) (K : Finset (Fin d → ℤ))
    (hK : ∀ k, ‖z - bv_pt s k‖ ≤ 2 + r → k ∈ K) (F : Euc d → ℝ) (x : Euc d) :
    χ (Φinv x - z) * F x =
      ∑ k ∈ K, χ (Φinv x - z) * (ρ (Φinv x - bv_pt s k) * (χ (x - Φ (bv_pt s k)) * F x)) := by
  by_cases h0 : χ (Φinv x - z) = 0
  · simp [h0]
  have hn : ‖Φinv x - z‖ < 2 := by
    have := hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 h0))
    simpa using this
  have hsum : ∑ k ∈ K, ρ (Φinv x - bv_pt s k) = 1 := by
    refine hpou _ K fun k hk => hK k ?_
    calc ‖z - bv_pt s k‖ = ‖(z - Φinv x) + (Φinv x - bv_pt s k)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - Φinv x‖ + ‖Φinv x - bv_pt s k‖ := norm_add_le _ _
      _ ≤ 2 + r := by rw [norm_sub_rev]; linarith
  have hterm : ∀ k ∈ K, χ (Φinv x - z) * (ρ (Φinv x - bv_pt s k) * (χ (x - Φ (bv_pt s k)) * F x)) =
      χ (Φinv x - z) * (ρ (Φinv x - bv_pt s k) * F x) := by
    intro k _
    by_cases hρk : ρ (Φinv x - bv_pt s k) = 0
    · simp [hρk]
    have hlt : ‖Φinv x - bv_pt s k‖ < r := by
      by_contra h
      exact hρk (hρ0 _ (not_lt.1 h))
    have h1 : ‖x - Φ (bv_pt s k)‖ ≤ 1 := by
      have := hlipΦ (Φinv x) (bv_pt s k)
      rw [hinv2] at this
      calc ‖x - Φ (bv_pt s k)‖ ≤ L * ‖Φinv x - bv_pt s k‖ := this
        _ ≤ L * r := mul_le_mul_of_nonneg_left hlt.le hL.le
        _ = 1 := hLr
    have h2 : χ (x - Φ (bv_pt s k)) = 1 :=
      hχ.2.2.2.2 _ (by rw [mem_closedBall_zero_iff]; exact h1)
    rw [h2, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have : ∑ k ∈ K, χ (Φinv x - z) * (ρ (Φinv x - bv_pt s k) * F x) =
      χ (Φinv x - z) * (∑ k ∈ K, ρ (Φinv x - bv_pt s k)) * F x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, hsum]
  ring

/-- pointwise partition identity for the lower bound -/
theorem bv_id_low {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {ρ : Euc d → ℝ} {s r L : ℝ}
    (hr1 : r ≤ 1) (hL : 0 < L) (hρ0 : ∀ y, r ≤ ‖y‖ → ρ y = 0)
    (hpou : ∀ (y : Euc d) (K : Finset (Fin d → ℤ)), (∀ k, ‖y - bv_pt s k‖ < r → k ∈ K) →
      ∑ k ∈ K, ρ (y - bv_pt s k) = 1)
    {Φinv : Euc d → Euc d} (hlipI : ∀ y y', ‖Φinv y - Φinv y'‖ ≤ L * ‖y - y'‖)
    (w : Euc d) (K : Finset (Fin d → ℤ))
    (hK : ∀ k, ‖Φinv w - bv_pt s k‖ ≤ 2 * L + r → k ∈ K) (F : Euc d → ℝ) (x : Euc d) :
    χ (x - w) * F x =
      ∑ k ∈ K, χ (x - w) * (ρ (Φinv x - bv_pt s k) * (χ (Φinv x - bv_pt s k) * F x)) := by
  by_cases h0 : χ (x - w) = 0
  · simp [h0]
  have hn : ‖x - w‖ < 2 := by
    have := hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 h0))
    simpa using this
  have hsum : ∑ k ∈ K, ρ (Φinv x - bv_pt s k) = 1 := by
    refine hpou _ K fun k hk => hK k ?_
    calc ‖Φinv w - bv_pt s k‖ = ‖(Φinv w - Φinv x) + (Φinv x - bv_pt s k)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖Φinv w - Φinv x‖ + ‖Φinv x - bv_pt s k‖ := norm_add_le _ _
      _ ≤ L * ‖w - x‖ + r := add_le_add (hlipI w x) hk.le
      _ ≤ 2 * L + r := by
          rw [norm_sub_rev]
          nlinarith
  have hterm : ∀ k ∈ K, χ (x - w) * (ρ (Φinv x - bv_pt s k) * (χ (Φinv x - bv_pt s k) * F x)) =
      χ (x - w) * (ρ (Φinv x - bv_pt s k) * F x) := by
    intro k _
    by_cases hρk : ρ (Φinv x - bv_pt s k) = 0
    · simp [hρk]
    have hlt : ‖Φinv x - bv_pt s k‖ < r := by
      by_contra h
      exact hρk (hρ0 _ (not_lt.1 h))
    have h2 : χ (Φinv x - bv_pt s k) = 1 :=
      hχ.2.2.2.2 _ (by rw [mem_closedBall_zero_iff]; linarith)
    rw [h2, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have : ∑ k ∈ K, χ (x - w) * (ρ (Φinv x - bv_pt s k) * F x) =
      χ (x - w) * (∑ k ∈ K, ρ (Φinv x - bv_pt s k)) * F x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, hsum]
  ring

/-- bound for the multiplication by `ρ(Φinv · - s k)` -/
theorem bv_rho_mul {m : ℕ} {χ : Euc d → ℝ} {L D B : ℝ} {Φ Φinv : Euc d → Euc d}
    (hdat : BvData m χ L D B Φ Φinv) (hD : 1 ≤ D) (ρ : Euc d → ℝ) (Kρ CQ : ℝ) (hCQ : 0 < CQ)
    (hKρ : ∀ D : ℝ, 1 ≤ D → ∀ f : Euc d → Euc d,
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f →
      (∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i f x‖ ≤ D) → ∀ z : Euc d,
      MemCb (m + 1) (fun x => ρ (f x - z)) ∧
        cbNorm (m + 1) (fun x => ρ (f x - z)) ≤ Kρ * D ^ (m + 1))
    (hQ : ∀ θ : Euc d → ℝ, MemCb m θ → ∀ u : Euc d → ℝ,
      sobolevNormE (m : ℝ) (fun x => θ x * u x) ≤
        ENNReal.ofReal (CQ * cbNorm m θ) * sobolevNormE (m : ℝ) u)
    (k : Euc d) (u : Euc d → ℝ) :
    sobolevNormE (m : ℝ) (fun x => ρ (Φinv x - k) * u x) ≤
      ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * sobolevNormE (m : ℝ) u := by
  obtain ⟨hm, hc⟩ := hKρ D hD Φinv hdat.smooth hdat.der k
  obtain ⟨hm1, hc1⟩ := bv_cb_mono hm
  refine (hQ _ hm1 u).trans ?_
  gcongr
  exact hc1.trans hc

theorem bv_upper (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (L D B : ℝ) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hB : 0 ≤ B) (ρ : Euc d → ℝ) (s r : ℝ) (hs : 0 < s) (hLr : L * r = 1)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, r ≤ ‖y‖ → ρ y = 0)
    (hpou : ∀ (y : Euc d) (K : Finset (Fin d → ℤ)), (∀ k, ‖y - bv_pt s k‖ < r → k ∈ K) →
      ∑ k ∈ K, ρ (y - bv_pt s k) = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ Φ Φinv : Euc d → Euc d, BvData m χ L D B Φ Φinv → ∀ F : Euc d → ℝ,
      (⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) * F x)) ≤
        ENNReal.ofReal K * ulocNormE m χ F := by
  classical
  obtain ⟨Kρ, hKρ0, hKρ⟩ := HRS.MS.FlowE.cb_comp_bound m ρ hρ hρc
  obtain ⟨CQ, hCQ, hQ⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  obtain ⟨N, hN⟩ := bv_net (d := d) hs (2 + r)
  have hL0 : 0 < L := by linarith
  have hD0 : 0 < D := by linarith
  have hCρ0 : 0 ≤ Kρ * D ^ (m + 1) := mul_nonneg hKρ0 (by positivity)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCQB0 : 0 ≤ CQ * B := mul_nonneg hCQ.le hB
  have hCQρ0 : 0 ≤ CQ * (Kρ * D ^ (m + 1)) := mul_nonneg hCQ.le hCρ0
  refine ⟨N * (CQ * B) * (CQ * (Kρ * D ^ (m + 1))) + 1,
    by have := mul_nonneg (mul_nonneg hN0 hCQB0) hCQρ0; linarith, fun Φ Φinv hdat F => ?_⟩
  refine iSup_le fun z => ?_
  obtain ⟨K, hKcard, hKsub⟩ := hN z
  have hid : (fun x => χ (Φinv x - z) * F x) = fun x => ∑ k ∈ K,
      χ (Φinv x - z) * (ρ (Φinv x - bv_pt s k) * (χ (x - Φ (bv_pt s k)) * F x)) := by
    funext x
    exact bv_id_up hχ hLr hL0 hρ0 hpou hdat.inv2 hdat.lipΦ z K hKsub F x
  rw [hid]
  refine (HRS.MS.UlocCut.uc_sum_le (m : ℝ) K _).trans ?_
  have hterm : ∀ k ∈ K, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) *
        (ρ (Φinv x - bv_pt s k) * (χ (x - Φ (bv_pt s k)) * F x))) ≤
      ENNReal.ofReal (CQ * B) * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * ulocNormE m χ F) := by
    intro k _
    obtain ⟨hm1, hc1⟩ := bv_cb_mono (hdat.cb z).1
    have e1 : ENNReal.ofReal (CQ * cbNorm m (fun x => χ (Φinv x - z))) ≤ ENNReal.ofReal (CQ * B) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hc1.trans (hdat.cb z).2) hCQ.le)
    have e2 := bv_rho_mul hdat hD ρ Kρ CQ hCQ hKρ hQ (bv_pt s k)
      (fun x => χ (x - Φ (bv_pt s k)) * F x)
    have e3 : sobolevNormE (m : ℝ) (fun x => χ (x - Φ (bv_pt s k)) * F x) ≤ ulocNormE m χ F :=
      le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * F x) (Φ (bv_pt s k))
    calc _ ≤ ENNReal.ofReal (CQ * cbNorm m (fun x => χ (Φinv x - z))) *
          sobolevNormE (m : ℝ) (fun x => ρ (Φinv x - bv_pt s k) *
            (χ (x - Φ (bv_pt s k)) * F x)) := hQ _ hm1 _
      _ ≤ ENNReal.ofReal (CQ * B) * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) *
          sobolevNormE (m : ℝ) (fun x => χ (x - Φ (bv_pt s k)) * F x)) := by gcongr
      _ ≤ _ := by gcongr
  have hcard : (K.card : ℝ≥0∞) ≤ N := by exact_mod_cast hKcard
  have hconst : ENNReal.ofReal (N * (CQ * B) * (CQ * (Kρ * D ^ (m + 1)))) =
      (N : ℝ≥0∞) * ENNReal.ofReal (CQ * B) * ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hN0 hCQB0), ENNReal.ofReal_mul hN0, ENNReal.ofReal_natCast]
  calc _ ≤ ∑ k ∈ K, ENNReal.ofReal (CQ * B) *
        (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * ulocNormE m χ F) := Finset.sum_le_sum hterm
    _ = (K.card : ℝ≥0∞) * (ENNReal.ofReal (CQ * B) *
        (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * ulocNormE m χ F)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal (CQ * B) *
        (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * ulocNormE m χ F)) := by gcongr
    _ = ENNReal.ofReal (N * (CQ * B) * (CQ * (Kρ * D ^ (m + 1)))) * ulocNormE m χ F := by
        rw [hconst]; ring
    _ ≤ _ := by
        gcongr
        linarith

theorem bv_lower (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (L D B : ℝ) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (ρ : Euc d → ℝ) (s r : ℝ) (hs : 0 < s) (hLr : L * r = 1)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, r ≤ ‖y‖ → ρ y = 0)
    (hpou : ∀ (y : Euc d) (K : Finset (Fin d → ℤ)), (∀ k, ‖y - bv_pt s k‖ < r → k ∈ K) →
      ∑ k ∈ K, ρ (y - bv_pt s k) = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ Φ Φinv : Euc d → Euc d, BvData m χ L D B Φ Φinv → ∀ F : Euc d → ℝ,
      ulocNormE m χ F ≤ ENNReal.ofReal K *
        ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) * F x) := by
  classical
  obtain ⟨Kρ, hKρ0, hKρ⟩ := HRS.MS.FlowE.cb_comp_bound m ρ hρ hρc
  obtain ⟨CQ, hCQ, hQ⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  obtain ⟨C1, hC1, h1⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) χ hχ.1 hχ.2.1
  obtain ⟨N, hN⟩ := bv_net (d := d) hs (2 * L + r)
  have hL0 : 0 < L := by linarith
  have hD0 : 0 < D := by linarith
  have hr1 : r ≤ 1 := by
    by_contra h
    have h' := not_le.1 h
    nlinarith
  have hCρ0 : 0 ≤ Kρ * D ^ (m + 1) := mul_nonneg hKρ0 (by positivity)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCQρ0 : 0 ≤ CQ * (Kρ * D ^ (m + 1)) := mul_nonneg hCQ.le hCρ0
  refine ⟨N * C1 * (CQ * (Kρ * D ^ (m + 1))) + 1,
    by have := mul_nonneg (mul_nonneg hN0 hC1.le) hCQρ0; linarith, fun Φ Φinv hdat F => ?_⟩
  refine iSup_le fun w => ?_
  obtain ⟨K, hKcard, hKsub⟩ := hN (Φinv w)
  have hid : (fun x => χ (x - w) * F x) = fun x => ∑ k ∈ K,
      χ (x - w) * (ρ (Φinv x - bv_pt s k) * (χ (Φinv x - bv_pt s k) * F x)) := by
    funext x
    exact bv_id_low hχ hr1 hL0 hρ0 hpou hdat.lipI w K hKsub F x
  rw [hid]
  refine (HRS.MS.UlocCut.uc_sum_le (m : ℝ) K _).trans ?_
  set S : ℝ≥0∞ := ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) * F x) with hS
  have hterm : ∀ k ∈ K, sobolevNormE (m : ℝ) (fun x => χ (x - w) *
        (ρ (Φinv x - bv_pt s k) * (χ (Φinv x - bv_pt s k) * F x))) ≤
      ENNReal.ofReal C1 * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * S) := by
    intro k _
    have e2 := bv_rho_mul hdat hD ρ Kρ CQ hCQ hKρ hQ (bv_pt s k)
      (fun x => χ (Φinv x - bv_pt s k) * F x)
    have e3 : sobolevNormE (m : ℝ) (fun x => χ (Φinv x - bv_pt s k) * F x) ≤ S :=
      le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (Φinv x - z) * F x) (bv_pt s k)
    calc _ ≤ ENNReal.ofReal C1 * sobolevNormE (m : ℝ) (fun x => ρ (Φinv x - bv_pt s k) *
          (χ (Φinv x - bv_pt s k) * F x)) := h1 w _
      _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) *
          sobolevNormE (m : ℝ) (fun x => χ (Φinv x - bv_pt s k) * F x)) := by gcongr
      _ ≤ _ := by gcongr
  have hcard : (K.card : ℝ≥0∞) ≤ N := by exact_mod_cast hKcard
  have hconst : ENNReal.ofReal (N * C1 * (CQ * (Kρ * D ^ (m + 1)))) =
      (N : ℝ≥0∞) * ENNReal.ofReal C1 * ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hN0 hC1.le), ENNReal.ofReal_mul hN0, ENNReal.ofReal_natCast]
  calc _ ≤ ∑ k ∈ K, ENNReal.ofReal C1 * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * S) :=
        Finset.sum_le_sum hterm
    _ = (K.card : ℝ≥0∞) * (ENNReal.ofReal C1 * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * S)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal C1 * (ENNReal.ofReal (CQ * (Kρ * D ^ (m + 1))) * S)) := by
        gcongr
    _ = ENNReal.ofReal (N * C1 * (CQ * (Kρ * D ^ (m + 1)))) * S := by
        rw [hconst]; ring
    _ ≤ _ := by
        gcongr
        linarith

/-- the two covering estimates, with one constant -/
theorem bv_core (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (L D B : ℝ) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ Φ Φinv : Euc d → Euc d, BvData m χ L D B Φ Φinv → ∀ F : Euc d → ℝ,
      (⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) * F x)) ≤
          ENNReal.ofReal K * ulocNormE m χ F ∧
      ulocNormE m χ F ≤ ENNReal.ofReal K *
          ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Φinv x - z) * F x) := by
  have hL0 : 0 < L := by linarith
  set r : ℝ := 1 / L with hr
  have hr0 : 0 < r := by positivity
  have hLr : L * r = 1 := by rw [hr]; field_simp
  set s : ℝ := r / (d + 1) with hs
  have hs0 : 0 < s := by positivity
  have hds : (d : ℝ) * s ≤ r := by
    rw [hs, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨ρ, hρ, hρc, hρ0, -, hpou⟩ := bv_pou hs0 hr0 hds
  obtain ⟨K1, hK1, h1⟩ := bv_upper m χ hχ L D B hL hD hB ρ s r hs0 hLr hρ hρc hρ0 hpou
  obtain ⟨K2, hK2, h2⟩ := bv_lower m χ hχ L D B hL hD ρ s r hs0 hLr hρ hρc hρ0 hpou
  refine ⟨K1 + K2, by positivity, fun Φ Φinv hdat F => ⟨?_, ?_⟩⟩
  · refine (h1 Φ Φinv hdat F).trans ?_
    gcongr
    linarith
  · refine (h2 Φ Φinv hdat F).trans ?_
    gcongr
    linarith

end HRS.MS.BilipV
