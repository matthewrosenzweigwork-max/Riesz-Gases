import HRS.MC.S7PIH7Pair
import HRS.MC.S7PIS3Conv

/-!
# Packet piH, part 8: the pair estimate `F lo - F hi = ½ ⟨S lo - S hi, D²F(hi)⟩ + o(hi - lo)`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ} {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ}

theorem S7PIH_pair_est (hab : a ≤ b)
    (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (c : EuclideanSpace ℝ (Fin q))
    {r : ℝ} (hr : r ∈ Set.Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ lo hi : ℝ, lo ∈ Set.Icc a b → hi ∈ Set.Icc a b → lo < hi → |lo - r| < η →
      |hi - r| < η →
      |gaussHeat S G lo c - gaussHeat S G hi c - (1 / 2) * ∑ i, ∑ j, (S lo - S hi) i j *
        iteratedFDeriv ℝ 2 (gaussHeat S G hi) c
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]| ≤ ε * (hi - lo) := by
  obtain ⟨K, hKpos, hK⟩ := S7PIH_A_bound hA
  set C0 : ℝ := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖ with hC0
  set C2 : ℝ := ⨆ z, ‖iteratedFDeriv ℝ 2 G z‖ with hC2
  have hC2nn : 0 ≤ C2 := (norm_nonneg _).trans (S7PIS3_cb_bound hG (j := 2) le_rfl 0)
  set M : ℝ := 2 * C2 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set V2 : ℝ := S7PIH_V2 q with hV2
  have hV2nn : 0 ≤ V2 := integral_nonneg fun z => sq_nonneg _
  set L : ℝ := (q : ℝ) + 1 with hL
  have hLpos : 0 < L := by positivity
  have hLK : 0 < L * K := mul_pos hLpos hKpos
  set ε1 : ℝ := ε / (2 * L * K * (V2 + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  set ε2 : ℝ := ε / (2 * L * K * (M + 1)) with hε2
  have hε2pos : 0 < ε2 := by positivity
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 ((S7PIH_tail_tendsto q).eventually (gt_mem_nhds hε2pos))
  set R1 : ℝ := max R0 1 with hR1
  have hR1pos : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨δ0, hδ0, η0, hη0, hmod⟩ := S7PIH_modulus hab hA hApsd hSb hS hG c hr hε1pos
  set η : ℝ := min η0 ((δ0 / R1) ^ 2 / (2 * (L * K))) with hη
  have hηpos : 0 < η := lt_min hη0 (by positivity)
  refine ⟨η, hηpos, fun lo hi hlo hhi hlh hlr hhr => ?_⟩
  set w : ℝ := hi - lo with hw
  have hwpos : 0 < w := sub_pos.2 hlh
  have hw2 : w < 2 * η := by
    rw [hw]
    have := abs_lt.1 hlr
    have := abs_lt.1 hhr
    linarith
  set bb : ℝ := Real.sqrt (L * K * w) with hbb
  have hbbpos : 0 < bb := Real.sqrt_pos.2 (by positivity)
  have hbb2 : bb ^ 2 = L * K * w := Real.sq_sqrt (by positivity)
  -- covariance increment
  set Δ : Matrix (Fin q) (Fin q) ℝ := S lo - S hi with hΔ
  have hΔpsd : Δ.PosSemidef := S7PIH_cov_psd hA hApsd hS hlo hhi hlh.le
  have hShi : (S hi).PosSemidef := S7PIH_S_psd hA hApsd hSb hS hhi
  have hΔent : ∀ i j, |Δ i j| ≤ K * w := fun i j => by
    have := S7PIH_cov_entry_bound hA hK hS hlo hhi hlh.le i j
    simpa [hΔ, hw] using this
  have hbΔ : ∀ u : EuclideanSpace ℝ (Fin q), u.ofLp ⬝ᵥ Δ.mulVec u.ofLp ≤ bb ^ 2 * ‖u‖ ^ 2 := by
    intro u
    refine (S7PIH_quad_bound (by positivity) hΔent u).trans ?_
    rw [hbb2]
    have : (q : ℝ) * (K * w) ≤ L * K * w := by
      rw [hL]; nlinarith [mul_pos hKpos hwpos]
    nlinarith [sq_nonneg ‖u‖]
  -- the function H = F(hi)
  have hH : ContDiff ℝ 2 (gaussHeat S G hi) :=
    S7PIH_heat_contDiff (multivariateGaussian 0 (S hi)) (by norm_num) hG
  have hbd : ∀ y, |gaussHeat S G hi y| ≤ C0 := fun y =>
    (S7PIH_heat_bounds (multivariateGaussian 0 (S hi)) hG y).1
  have hD2b : ∀ y, ‖iteratedFDeriv ℝ 2 (gaussHeat S G hi) y‖ ≤ C2 := fun y =>
    (S7PIH_heat_bounds (multivariateGaussian 0 (S hi)) hG y).2
  have hMb : ∀ y, ‖iteratedFDeriv ℝ 2 (gaussHeat S G hi) y -
      iteratedFDeriv ℝ 2 (gaussHeat S G hi) c‖ ≤ M := fun y =>
    (norm_sub_le _ _).trans (by linarith [hD2b y, hD2b c])
  have hhir : |hi - r| < η0 := lt_of_lt_of_le hhr (min_le_left _ _)
  have hεb : ∀ y, ‖y - c‖ ≤ δ0 → ‖iteratedFDeriv ℝ 2 (gaussHeat S G hi) y -
      iteratedFDeriv ℝ 2 (gaussHeat S G hi) c‖ ≤ ε1 := fun y hy => hmod hi hhi hhir y hy
  have hexp := S7PIH_gauss_expand hΔpsd hbbpos hbΔ hH hbd c hδ0 hMb hεb
  have hconv := s7_PIH_gauss_conv_proof S lo hi hShi hΔpsd G (S7PIH_cb_mono hG (Nat.zero_le 2)) c
  rw [← hconv] at hexp
  refine hexp.trans ?_
  -- tail estimate
  have hbbR : R1 ≤ δ0 / bb := by
    rw [le_div_iff₀ hbbpos]
    have h1 : bb ≤ δ0 / R1 := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have : w < 2 * ((δ0 / R1) ^ 2 / (2 * (L * K))) :=
        hw2.trans_le (by gcongr; exact min_le_right _ _)
      calc L * K * w ≤ L * K * (2 * ((δ0 / R1) ^ 2 / (2 * (L * K)))) := by gcongr
        _ = (δ0 / R1) ^ 2 := by field_simp
    calc R1 * bb ≤ R1 * (δ0 / R1) := by gcongr
      _ = δ0 := by field_simp
  have htail : S7PIH_tail q (δ0 / bb) < ε2 := hR0 _ ((le_max_left R0 1).trans hbbR)
  have h1 : ε1 * V2 ≤ ε / (2 * L * K) := by
    have : ε1 * V2 = ε / (2 * L * K) * (V2 / (V2 + 1)) := by
      rw [hε1]; field_simp
    rw [this]
    have : V2 / (V2 + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    calc ε / (2 * L * K) * (V2 / (V2 + 1)) ≤ ε / (2 * L * K) * 1 := by gcongr
      _ = _ := mul_one _
  have h2 : M * S7PIH_tail q (δ0 / bb) ≤ ε / (2 * L * K) := by
    have : M * S7PIH_tail q (δ0 / bb) ≤ M * ε2 := by gcongr
    refine this.trans ?_
    have : M * ε2 = ε / (2 * L * K) * (M / (M + 1)) := by
      rw [hε2]; field_simp
    rw [this]
    have : M / (M + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    calc ε / (2 * L * K) * (M / (M + 1)) ≤ ε / (2 * L * K) * 1 := by gcongr
      _ = _ := mul_one _
  rw [hbb2]
  calc L * K * w * (ε1 * V2 + M * S7PIH_tail q (δ0 / bb))
      ≤ L * K * w * (ε / (2 * L * K) + ε / (2 * L * K)) := by gcongr
    _ = ε * w := by field_simp; ring

end HRS.MC.Sec7.S7PIH

end
