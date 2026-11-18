import HRS.Sections.ScrnAux34

/-!
# Packet SCRN, part 35: the bundle `ScrnGB` of norm bounds of a decayed copy of the mesoscopic test

For `ψ = mesoTest d ℓ x₀ φ` and a `θ`-decayed copy `g` (`ScrnDecay ψ g θ`), `ℓ ≤ 1`, `ScrnGB d s ℓ θ g C`
collects: `C²`, the sup norms of `D⁰, D¹, D²`, the `ℓ¹` sum `∑ 2π|k||ĝ|`, the weighted `ℓ²` sums for the
exponents `d+4` and `2a+2` (`a = (d-s)/2`), the plain `ℓ²` sum, and the transport bound of `-∇g`.
All with one constant `C` (monotone in `C`), uniform in `ℓ ∈ (0,1]`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE

theorem scrn_tb_mono {s : ℝ} {v : Torus d → Euc d} {K K' : ℝ} (h : HasTransportBound d s v K)
    (hK : K ≤ K') : HasTransportBound d s v K' := by
  obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := h
  exact ⟨L, F, hL, hF, hlip, hfrac, hLK.trans hK⟩

structure ScrnGB (d : ℕ) (s ℓ θ : ℝ) (g : Torus d → ℝ) (C : ℝ) : Prop where
  nn : 0 ≤ C
  ck2 : Torus.IsCk 2 g
  d0 : ∀ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift g) y‖ ≤ C * ℓ ^ (-((d : ℝ) / 2))
  d1 : ∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤ θ * C * ℓ ^ (-((d : ℝ) / 2) - 1)
  d2 : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ θ * C * ℓ ^ (-((d : ℝ) / 2) - 2)
  w1 : Summable fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖
  w1b : ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ ≤
    θ * C * ℓ ^ (-((d : ℝ) / 2) - 1)
  h4 : Summable fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) *
    ‖coeffOf g k‖ ^ 2
  h4b : ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 4) * ‖coeffOf g k‖ ^ 2 ≤
    (θ * C * ℓ ^ (-((d : ℝ) + 4) / 2)) ^ 2
  hq : Summable fun k : Lattice d =>
    (2 * Real.pi * Lattice.enorm k) ^ (2 * (((d : ℝ) - s) / 2) + 2) * ‖coeffOf g k‖ ^ 2
  hqb : ∑' k : Lattice d,
    (2 * Real.pi * Lattice.enorm k) ^ (2 * (((d : ℝ) - s) / 2) + 2) * ‖coeffOf g k‖ ^ 2 ≤
    (θ * C * ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2)) ^ 2
  l2 : Summable fun k : Lattice d => ‖coeffOf g k‖ ^ 2
  l2b : ∑' k : Lattice d, ‖coeffOf g k‖ ^ 2 ≤ C ^ 2
  tb : HasTransportBound d s (scrnV g) (θ * C * ℓ ^ (-((d : ℝ) / 2) - 2))

theorem ScrnGB.mono {s ℓ θ : ℝ} {g : Torus d → ℝ} {C C' : ℝ} (hℓ : 0 < ℓ) (hθ : 0 ≤ θ)
    (h : ScrnGB d s ℓ θ g C) (hC : C ≤ C') : ScrnGB d s ℓ θ g C' := by
  have hC0 := h.nn
  have hp : ∀ e : ℝ, 0 ≤ ℓ ^ e := fun e => Real.rpow_nonneg hℓ.le e
  have m1 : ∀ e : ℝ, θ * C * ℓ ^ e ≤ θ * C' * ℓ ^ e := fun e =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hθ) (hp e)
  have m2 : ∀ e : ℝ, (θ * C * ℓ ^ e) ^ 2 ≤ (θ * C' * ℓ ^ e) ^ 2 := fun e =>
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hθ hC0) (hp e)) (m1 e) 2
  refine ⟨hC0.trans hC, h.ck2, fun y => (h.d0 y).trans ?_, fun y => (h.d1 y).trans (m1 _),
    fun y => (h.d2 y).trans (m1 _), h.w1, h.w1b.trans (m1 _), h.h4, h.h4b.trans (m2 _), h.hq,
    h.hqb.trans (m2 _), h.l2, h.l2b.trans (pow_le_pow_left₀ hC0 hC 2),
    scrn_tb_mono h.tb (m1 _)⟩
  exact mul_le_mul_of_nonneg_right hC (hp _)

theorem scrn_exists_GB (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (x₀ : Euc d)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ (g : Torus d → ℝ) (θ : ℝ),
      ScrnDecay (mesoTest d ℓ x₀ φ) g θ → ScrnGB d s ℓ θ g C := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CD, hCD, hD⟩ := scrn_decay_deriv hd0 x₀ hφ hc
  obtain ⟨C4, hC4, hW4⟩ := scrn_decay_wsum hd0 x₀ hφ hc (r := (d : ℝ) + 4) (by positivity)
  obtain ⟨Cq, hCq, hWq⟩ := scrn_decay_wsum hd0 x₀ hφ hc
    (r := 2 * (((d : ℝ) - s) / 2) + 2) (by linarith)
  obtain ⟨C2, hC2, hW2⟩ := scrn_psi_wsum hd0 x₀ hφ hc (r := 0) le_rfl (e := 2) (by norm_num)
  obtain ⟨Cs, hCs, hTr⟩ := scrn_transport hd s hs0
  refine ⟨CD + C4 + Cq + Real.sqrt C2 + d * Cs * C4, by positivity, fun ℓ hℓ hℓ1 g θ hθ => ?_⟩
  obtain ⟨hck2, hd0', hd1, hd2, hw1, hw1b⟩ := hD ℓ hℓ hℓ1 g θ hθ
  obtain ⟨hs4, hs4b⟩ := hW4 ℓ hℓ hℓ1 g θ hθ
  obtain ⟨hsq, hsqb⟩ := hWq ℓ hℓ hℓ1 g θ hθ
  obtain ⟨hs2, hs2b⟩ := hW2 ℓ hℓ hℓ1
  set C : ℝ := CD + C4 + Cq + Real.sqrt C2 + d * Cs * C4 with hCdef
  have hθ0 := hθ.nonneg
  have hp : ∀ e : ℝ, 0 ≤ ℓ ^ e := fun e => Real.rpow_nonneg hℓ.le e
  have hCn : 0 ≤ C := by positivity
  have m1 : ∀ (c : ℝ), 0 ≤ c → c ≤ C → ∀ e : ℝ, θ * c * ℓ ^ e ≤ θ * C * ℓ ^ e := fun c hc0 hcC e =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcC hθ0) (hp e)
  have hCD' : CD ≤ C := by
    have : 0 ≤ d * Cs * C4 := by positivity
    have := Real.sqrt_nonneg C2
    simp only [hCdef]; linarith
  have hC4' : C4 ≤ C := by
    have : 0 ≤ d * Cs * C4 := by positivity
    have := Real.sqrt_nonneg C2
    simp only [hCdef]; linarith
  have hCq' : Cq ≤ C := by
    have : 0 ≤ d * Cs * C4 := by positivity
    have := Real.sqrt_nonneg C2
    simp only [hCdef]; linarith
  have hC2' : Real.sqrt C2 ≤ C := by
    have : 0 ≤ d * Cs * C4 := by positivity
    simp only [hCdef]; linarith
  refine ⟨hCn, hck2, fun y => (hd0' y).trans ?_, fun y => (hd1 y).trans (m1 _ hCD hCD' _),
    fun y => (hd2 y).trans (m1 _ hCD hCD' _), hw1, hw1b.trans (m1 _ hCD hCD' _), hs4, ?_, hsq, ?_,
    ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right hCD' (hp _)
  · refine hs4b.trans ?_
    have e : (-((d : ℝ) + 4) / 2) = -((d : ℝ) + 4) / 2 := rfl
    exact pow_le_pow_left₀ (by positivity) (m1 _ hC4 hC4' _) 2
  · exact hsqb.trans (pow_le_pow_left₀ (by positivity) (m1 _ hCq hCq' _) 2)
  · -- plain ℓ² sum
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hs2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hθ.le k) 2
    simpa using h1
  · have hsum : Summable fun k : Lattice d => ‖coeffOf g k‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) (hθ.le k) 2
        simpa using h1) hs2
    have h1 : ∑' k : Lattice d, ‖coeffOf g k‖ ^ 2 ≤
        ∑' k : Lattice d, Lattice.enorm k ^ (0 : ℝ) * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 2 := by
      refine hsum.tsum_le_tsum (fun k => ?_) hs2
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hθ.le k) 2
      simpa using h1
    refine h1.trans (hs2b.trans ?_)
    have e : (d : ℝ) * (2 : ℕ) / 2 - ((d : ℝ) + 0) = 0 := by push_cast; ring
    rw [e, Real.rpow_zero, mul_one]
    have : C2 = Real.sqrt C2 ^ 2 := (Real.sq_sqrt hC2).symm
    rw [this]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hC2' 2
  · -- transport bound
    have hB2 := hd2
    have hH := hs4b
    refine scrn_tb_mono (hTr g (θ * CD * ℓ ^ (-((d : ℝ) / 2) - 2))
      (θ * C4 * ℓ ^ (-((d : ℝ) + 4) / 2)) (by positivity) (by positivity) hck2 hd2 hs4 hs4b) ?_
    have e : (-((d : ℝ) + 4) / 2) = -((d : ℝ) / 2) - 2 := by ring
    rw [e]
    have hpe := hp (-((d : ℝ) / 2) - 2)
    have : θ * CD * ℓ ^ (-((d : ℝ) / 2) - 2) + d * Cs * (θ * C4 * ℓ ^ (-((d : ℝ) / 2) - 2)) =
        θ * (CD + d * Cs * C4) * ℓ ^ (-((d : ℝ) / 2) - 2) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hθ0) hpe
    have := Real.sqrt_nonneg C2
    have : 0 ≤ C4 + Cq := by positivity
    simp only [hCdef]; linarith

end HRS
