import HRS.Main.GFSpec3
import HRS.Energy.StaticLimitBasic

/-!
# Packet GFB1, part 1: relocated proofs of `gf_smooth_mem`, `gf_eval_sub`, `gf_measurable_ofMeasureDiff`

The statements are copied verbatim from `HRS/Main/GFSpec1.lean` / `GFSpec2.lean`; the spec files are not edited.
Each relocated theorem is named `<name>_proof` and is tied to its spec by an `example` (`type_of%`).
Helper lemmas carry the prefix `gfb1_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### Helpers -/

theorem gfb1_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl

theorem gfb1_fc_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [gfb1_coord_sub]
  ring

/-- For a smooth test function the weighted coefficient sum `∑ ⟨k⟩^{2m} φ̂(k)²` is finite (any `m`). -/
theorem gfb1_smooth_sq {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (m : ℝ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 := by
  have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => hφ'.of_le (by exact_mod_cast le_top)
  have hc : Continuous φ := Torus.continuous_of_continuous_lift (hd 0).continuous
  have hint : Integrable φ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set N : ℕ := ⌈|m|⌉₊ + d + 1 with hN
  have hNr : (N : ℝ) = (⌈|m|⌉₊ : ℝ) + (d : ℝ) + 1 := by
    rw [hN]; push_cast; ring
  have hceil : |m| ≤ (⌈|m|⌉₊ : ℝ) := Nat.le_ceil _
  have hNm : (d : ℝ) < 2 * ((N : ℝ) - m) := by
    have := le_abs_self m
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (hd N)
  have hsum := summable_jp_rpow ((N : ℝ) - m) hNm
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)) (fun k => ?_) (hsum.mul_left (2 * B ^ 2))
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos _
  set s := ‖Torus.fcoef φ k.1‖ with hs
  set f := Torus.funRealCoeff φ k with hf
  have hf2 : f ^ 2 ≤ 2 * s ^ 2 := by
    have h := Torus.two_mul_norm_fcoef_sq hint k
    rw [← hs, ← hf] at h
    nlinarith [sq_nonneg (Torus.funRealCoeff φ (Torus.negNZ d k))]
  have hs2 : s ^ 2 * (Lattice.jp k.1 ^ N) ^ 2 ≤ B ^ 2 := by
    have h := hB k
    have hnn : 0 ≤ s * Lattice.jp k.1 ^ N := mul_nonneg (norm_nonneg _) (pow_nonneg hj.le _)
    have := pow_le_pow_left₀ hnn h 2
    nlinarith [this]
  have hpow : Lattice.jp k.1 ^ (-(2 * ((N : ℝ) - m))) =
      Lattice.jp k.1 ^ (2 * m) / (Lattice.jp k.1 ^ N) ^ 2 := by
    rw [show -(2 * ((N : ℝ) - m)) = 2 * m - ((N * 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_sub hj, Real.rpow_natCast, pow_mul]
  have hpos : 0 < (Lattice.jp k.1 ^ N) ^ 2 := by positivity
  have hfb : f ^ 2 ≤ 2 * B ^ 2 / (Lattice.jp k.1 ^ N) ^ 2 := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_right hf2 (sq_nonneg (Lattice.jp k.1 ^ N))]
  rw [hpow]
  calc Lattice.jp k.1 ^ (2 * m) * f ^ 2
      ≤ Lattice.jp k.1 ^ (2 * m) * (2 * B ^ 2 / (Lattice.jp k.1 ^ N) ^ 2) :=
        mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hj.le _)
    _ = 2 * B ^ 2 * (Lattice.jp k.1 ^ (2 * m) / (Lattice.jp k.1 ^ N) ^ 2) := by ring

/-- Pairing of `F ∈ E_m` with `φ` against a smooth test function is an absolutely convergent
`ℓ²`-pairing, so `k ↦ F̂(k) φ_k` is summable. -/
theorem gfb1_summable_mul {m : ℝ} (F : NegSobolev d m) {φ : Torus d → ℝ}
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Summable fun k : NonzeroLattice d => NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k := by
  set y : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k with hy
  have hy2 : Summable fun k => y k ^ 2 := by
    refine hs.congr fun k => ?_
    simp only [hy]
    rw [mul_pow, Torus.jp_rpow_sq]
  have hcs := Torus.cs_tsum (fun k => |NegSobolev.coord F k|) (fun k => |y k|)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (by simpa [sq_abs] using (NegSobolev.coord_sq F).1) (by simpa [sq_abs] using hy2)
  have hs1 : Summable fun k => NegSobolev.coord F k * y k := by
    refine Summable.of_norm_bounded hcs.1 fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
  refine hs1.congr fun k => ?_
  unfold NegSobolev.fourierCoeff
  simp only [hy]
  ring

theorem gf_smooth_mem_proof {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (m : ℝ) :
    Torus.IsCk 2 φ ∧ MemSobolev m φ := by
  have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => hφ'.of_le (by exact_mod_cast le_top)
  have hc : Continuous φ := Torus.continuous_of_continuous_lift (hd 0).continuous
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift φ) := hd 2
  refine ⟨by exact_mod_cast h2, ?_, gfb1_smooth_sq hφ m⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MeasureTheory.MemLp.of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

example := (@gf_smooth_mem_proof : type_of% @HRS.GF.gf_smooth_mem)

theorem gf_eval_sub_proof {m : ℝ} (F G : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (F - G) φ = NegSobolev.eval F φ - NegSobolev.eval G φ := by
  have hs := gfb1_smooth_sq hφ m
  unfold NegSobolev.eval
  simp_rw [gfb1_fc_sub, sub_mul]
  exact Summable.tsum_sub (gfb1_summable_mul F hs) (gfb1_summable_mul G hs)

example := (@gf_eval_sub_proof : type_of% @HRS.GF.gf_eval_sub)

theorem gf_measurable_ofMeasureDiff_proof {N : ℕ} (m : ℝ) (hm : (d : ℝ) / 2 < m) (μ : Measure (Torus d)) :
    Measurable (fun x : Config d N => NegSobolev.ofMeasureDiff m (empirical x) μ) := by
  -- empirical Fourier coefficients: `a x k = N⁻¹ ∑_i e_k(x_i)`, bounded by `√2` uniformly in `x`
  set a : Config d N → NonzeroLattice d → ℝ :=
    fun x k => (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (x i) with ha
  have hcoef : ∀ x k, Torus.measureRealCoeff (empirical x) k = a x k := by
    intro x k
    unfold Torus.measureRealCoeff
    simp only [ha]
    exact integral_empirical x (continuous_realMode' k)
  have hbd : ∀ x k, |a x k| ≤ Real.sqrt 2 := by
    intro x k
    simp only [ha]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have hsum : |∑ i, Torus.realMode k (x i)| ≤ (N : ℝ) * Real.sqrt 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => Torus.abs_realMode_le k (x i)).trans ?_
        simp
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [abs_mul, abs_inv, abs_of_pos hNpos]
      calc (N : ℝ)⁻¹ * |∑ i, Torus.realMode k (x i)| ≤ (N : ℝ)⁻¹ * ((N : ℝ) * Real.sqrt 2) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Real.sqrt 2 := by field_simp
  have hmeas : ∀ k, Measurable fun x : Config d N => a x k := by
    intro k
    simp only [ha]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (continuous_realMode' k).measurable.comp (measurable_pi_apply i))
  -- `μ`-coefficients (a constant, independent of `x`)
  set c : NonzeroLattice d → ℝ := fun k => Torus.measureRealCoeff μ k with hc
  have hm' : (d : ℝ) < 2 * m := by linarith
  have h1 : ∀ x : Config d N, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * a x k) 2 := fun x =>
    NegSobolev.memℓp_of_bounded hm' _ ⟨Real.sqrt 2, fun k => hbd x k⟩
  -- the function `x ↦ ofMeasureDiff m (empirical x) μ` is `ofSeq m (a x - c)`
  have hF : ∀ x : Config d N, NegSobolev.ofMeasureDiff m (empirical x) μ =
      NegSobolev.ofSeq m (fun k => a x k - c k) := by
    intro x
    unfold NegSobolev.ofMeasureDiff
    congr 1
    funext k
    rw [hcoef]
  by_cases hP : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2
  · -- honest case: the coordinates are `ℓ²` for every `x`; use the lp-valued limit of finite sums
    have hfin : ∀ x : Config d N, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a x k - c k)) 2 := by
      intro x
      have e : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a x k - c k)) =
          (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * a x k) -
            (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) := by
        funext k; simp only [Pi.sub_apply]; ring
      rw [e]
      exact (h1 x).sub hP
    have hcoordG : ∀ x k, NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical x) μ) k =
        Lattice.jp k.1 ^ (-m) * (a x k - c k) := by
      intro x k
      rw [hF x, NegSobolev.coord_ofSeq_of_mem (fun k => a x k - c k) (hfin x) k]
    have hcm : ∀ k, Measurable fun x : Config d N =>
        NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical x) μ) k := by
      intro k
      simp only [hcoordG]
      exact measurable_const.mul ((hmeas k).sub measurable_const)
    have hlim : ∀ X : Config d N, Tendsto
        (fun s : Finset (NonzeroLattice d) => (∑ k ∈ s,
          (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
            (NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical X) μ) k))))
        atTop (𝓝 (NegSobolev.ofMeasureDiff m (empirical X) μ)) := by
      intro X
      exact lp.hasSum_single (p := 2) (by simp)
        (show lp (fun _ : NonzeroLattice d => ℝ) 2 from NegSobolev.ofMeasureDiff m (empirical X) μ)
    refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NonzeroLattice d)))
      (f := fun (s : Finset (NonzeroLattice d)) (X : Config d N) =>
        (∑ k ∈ s, (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
          (NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical X) μ) k)))) (fun s => ?_)
      (tendsto_pi_nhds.2 hlim)
    refine Finset.measurable_sum _ fun k _ => ?_
    have hcont : Continuous (fun a : ℝ => (show NegSobolev d m from
        lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k a)) :=
      (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous
    exact hcont.measurable.comp (hcm k)
  · -- the `μ`-part is not in `ℓ²`: then every `ofSeq` is the junk value `0`
    have hG0 : ∀ x : Config d N, NegSobolev.ofMeasureDiff m (empirical x) μ = 0 := by
      intro x
      have hnot : ¬ Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a x k - c k)) 2 := by
        intro h
        apply hP
        have e : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) =
            (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * a x k) -
              (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (a x k - c k)) := by
          funext k; simp only [Pi.sub_apply]; ring
        rw [e]
        exact (h1 x).sub h
      rw [hF x]
      unfold NegSobolev.ofSeq
      exact dif_neg hnot
    have e0 : (fun x : Config d N => NegSobolev.ofMeasureDiff m (empirical x) μ) = fun _ => 0 :=
      funext hG0
    rw [e0]
    exact measurable_const

example := (@gf_measurable_ofMeasureDiff_proof : type_of% @HRS.GF.gf_measurable_ofMeasureDiff)

end HRS.GF
