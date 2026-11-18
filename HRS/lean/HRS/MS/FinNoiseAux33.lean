import HRS.MS.FinNoiseAux32
import HRS.Uniform.RelativeCov

/-!
# S8.6 `finite_noise`: real-mode Fourier inversion and the Hilbert-Schmidt synthesis map (Pro FR02, FR03) (S86b)

`s86_synthesis`: for a periodic `C^r` function `G : ℝ^d → K` (`r > d`, `K` a real Hilbert space with a Hilbert basis `b`)
there is a bounded operator `R : ℓ²(ℤ^d) → K` with `R (chartFeature r (mk y)) = G y` for every `y` and
`‖R‖² ≤ ∑_{l ≤ r} C(r,l) d^l B_l²`, where `B_l ≥ sup ‖D^l G‖`.  The scalar coefficients of `⟨b n, G ·⟩` in the real modes
`chartBasis` are `a_{n,k}`, `R` has the rows `(a_{n,k}/√d_k)_k`, and the inversion is the scalar Fourier series.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Torus HRS.Uniform HRS.Uniform.ChartAux

variable {d : ℕ}

theorem s86_weighted_real (p : Lattice d → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hpe : ∀ k, p (-k) = p k)
    {φ : Torus d → ℝ} (hφ : Integrable φ)
    (hs : Summable fun k : Lattice d => p k * ‖fcoef φ k‖ ^ 2) :
    Summable (fun k : Lattice d => p k * (∫ u, chartBasis k u * φ u) ^ 2) ∧
    ∑' k : Lattice d, p k * (∫ u, chartBasis k u * φ u) ^ 2 =
      ∑' k : Lattice d, p k * ‖fcoef φ k‖ ^ 2 := by
  set a : Lattice d → ℝ := fun k => ∫ u, chartBasis k u * φ u with ha
  have ha0 : a 0 = mean φ := by
    simp [ha, chartBasis_zero, mean]
  have haNZ : ∀ k : NonzeroLattice d, a k.1 = funRealCoeff φ k := by
    intro k
    simp only [ha, funRealCoeff]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [chartBasis_ne k.1 k.2]
  have hs' := (summable_lattice_iff _).mp hs
  set A : NonzeroLattice d → ℝ := fun k => p k.1 * funRealCoeff φ k ^ 2 with hA
  have hAle : ∀ k : NonzeroLattice d, A k ≤ 2 * (p k.1 * ‖fcoef φ k.1‖ ^ 2) := by
    intro k
    have h := two_mul_norm_fcoef_sq hφ k
    have := mul_le_mul_of_nonneg_left (show funRealCoeff φ k ^ 2 ≤ 2 * ‖fcoef φ k.1‖ ^ 2 by
      rw [h]; nlinarith [sq_nonneg (funRealCoeff φ (negNZ d k))]) (hp0 k.1)
    simp only [hA]
    nlinarith
  have hAs : Summable A := Summable.of_nonneg_of_le (fun k => mul_nonneg (hp0 _) (sq_nonneg _)) hAle
    (hs'.mul_left 2)
  have hneg : Summable fun k => A (negNZ d k) := (negNZ d).summable_iff.mpr hAs
  have e : ∀ k : NonzeroLattice d, p k.1 * ‖fcoef φ k.1‖ ^ 2 = (A k + A (negNZ d k)) / 2 := by
    intro k
    have h := two_mul_norm_fcoef_sq hφ k
    have hp : p (negNZ d k).1 = p k.1 := hpe k.1
    have : ‖fcoef φ k.1‖ ^ 2 = (funRealCoeff φ k ^ 2 + funRealCoeff φ (negNZ d k) ^ 2) / 2 := by
      linarith
    simp only [hA, hp]
    rw [this]; ring
  have hNZsum : ∑' k : NonzeroLattice d, p k.1 * ‖fcoef φ k.1‖ ^ 2 = ∑' k : NonzeroLattice d, A k := by
    simp_rw [e]
    rw [tsum_div_const, hAs.tsum_add hneg, Equiv.tsum_eq (negNZ d) A]
    ring
  have hf1 : Summable (fun k : Lattice d => p k * (a k) ^ 2) := by
    rw [summable_lattice_iff]
    refine hAs.congr fun k => ?_
    simp only [hA, haNZ k]
  refine ⟨hf1, ?_⟩
  rw [tsum_lattice _ hf1, tsum_lattice _ hs]
  have h0 : ‖fcoef φ 0‖ ^ 2 = (mean φ) ^ 2 := by
    rw [fcoef_zero]; simp
  rw [h0, ha0, hNZsum]
  congr 1
  refine tsum_congr fun k => ?_
  simp only [hA, haNZ k]

theorem s86_real_inversion {g : Torus d → ℝ} (hc : Continuous g)
    (hs : Summable fun k : Lattice d => ‖fcoef g k‖) (x : Torus d) :
    Summable (fun k : Lattice d => (∫ u, chartBasis k u * g u) * chartBasis k x) ∧
    ∑' k : Lattice d, (∫ u, chartBasis k u * g u) * chartBasis k x = g x := by
  have hg : Integrable g := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hexp := hasSum_realExpansion hc hs x
  set f : Lattice d → ℝ := fun k => (∫ u, chartBasis k u * g u) * chartBasis k x with hf
  have hfNZ : ∀ k : NonzeroLattice d, f k.1 = funRealCoeff g k * realMode k x := by
    intro k
    simp only [hf, funRealCoeff, chartBasis_ne k.1 k.2]
  have hfs : Summable f := by
    rw [summable_lattice_iff]
    exact hexp.summable.congr fun k => (hfNZ k).symm
  refine ⟨hfs, ?_⟩
  rw [tsum_lattice f hfs]
  have h0 : f 0 = mean g := by
    simp [hf, chartBasis_zero, mean]
  have h1 : ∑' k : NonzeroLattice d, f k.1 = g x - mean g := by
    rw [← hexp.tsum_eq]
    exact tsum_congr hfNZ
  rw [h0, h1]; ring

theorem s86_chartWeight_inv (r : ℕ) (k : Lattice d) :
    chartWeight r k = ((1 + Lattice.enorm k ^ 2) ^ r)⁻¹ := by
  unfold chartWeight
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem s86_synthesis (r : ℕ) (hr : d < r) {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] {ι : Type*} (b : HilbertBasis ι ℝ K) (G : Euc d → K)
    (hper : ∀ (y : Euc d) (n : Lattice d), G (y + Lattice.toEuc n) = G y) (hG : ContDiff ℝ r G)
    (B : ℕ → ℝ) (hB : ∀ l ≤ r, ∀ y, ‖iteratedFDeriv ℝ l G y‖ ≤ B l) :
    ∃ R : FeatureSpace d →L[ℝ] K, (∀ y : Euc d, R (chartFeature (d := d) r (Torus.mk y)) = G y) ∧
      ‖R‖ ^ 2 ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (d : ℝ) ^ l * B l ^ 2 := by
  classical
  set Bs : ℝ := ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (d : ℝ) ^ l * B l ^ 2 with hBs
  set Gn : ι → Euc d → ℝ := fun n y => ⟪b n, G y⟫ with hGn
  have hGnper : ∀ n, Per (Gn n) := fun n y k => by simp only [hGn, hper y k]
  have hGnc : ∀ n, Continuous (Gn n) := fun n => (innerSL ℝ (b n)).continuous.comp hG.continuous
  set g : ι → Torus d → ℝ := fun n => descend (Gn n) with hg
  have hgc : ∀ n, Continuous (g n) := fun n => continuous_descend (hGnper n) (hGnc n)
  have hgI : ∀ n, Integrable (g n) := fun n =>
    (hgc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set a : ι → Lattice d → ℝ := fun n k => ∫ u, chartBasis k u * g n u with ha
  set p : Lattice d → ℝ := fun k => (1 + Lattice.enorm k ^ 2) ^ r with hp
  have hp0 : ∀ k, 0 ≤ p k := fun k => by simp only [hp]; positivity
  have hppos : ∀ k, 0 < p k := fun k => by simp only [hp]; positivity
  have hpe : ∀ k, p (-k) = p k := fun k => by
    simp only [hp, Lattice.enorm, toEuc_neg, norm_neg]
  have hbes := fun F => s86_vector_bessel r (⇑b) b.orthonormal G hper hG B hB F
  have hW : ∀ n, Summable (fun k => p k * (a n k) ^ 2) ∧
      ∑' k, p k * (a n k) ^ 2 = ∑' k, p k * ‖fcoef (g n) k‖ ^ 2 := fun n =>
    s86_weighted_real p hp0 hpe (hgI n) ((hbes {n}).1 n (Finset.mem_singleton_self n))
  have hwp : ∀ k, chartWeight r k = (p k)⁻¹ := fun k => s86_chartWeight_inv r k
  have hwpos : ∀ k : Lattice d, 0 < chartWeight r k := fun k => chartWeight_pos r k
  -- rows of the operator
  have hrow : ∀ n, Memℓp (fun k => a n k / Real.sqrt (chartWeight r k)) 2 := by
    intro n
    rw [memℓp_two_iff]
    refine (hW n).1.congr fun k => ?_
    rw [div_pow, Real.sq_sqrt (hwpos k).le, hwp k]
    field_simp
  set rv : ι → FeatureSpace d := fun n => ⟨_, hrow n⟩ with hrv
  have hrvsq : ∀ n, ‖rv n‖ ^ 2 = ∑' k, p k * (a n k) ^ 2 := by
    intro n
    rw [(lp_two_sq (rv n)).2]
    refine tsum_congr fun k => ?_
    show (a n k / Real.sqrt (chartWeight r k)) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (hwpos k).le, hwp k]
    field_simp
  have hFbound : ∀ F : Finset ι, ∑ n ∈ F, ‖rv n‖ ^ 2 ≤ Bs := by
    intro F
    calc ∑ n ∈ F, ‖rv n‖ ^ 2 = ∑ n ∈ F, ∑' k, p k * ‖fcoef (g n) k‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hrvsq, (hW n).2]
      _ ≤ Bs := (hbes F).2
  have hBs0 : 0 ≤ Bs := by simpa using hFbound ∅
  have hsum : Summable fun n => ‖rv n‖ ^ 2 :=
    summable_of_sum_le (fun n => sq_nonneg _) hFbound
  have htsum : ∑' n, ‖rv n‖ ^ 2 ≤ Bs := hsum.tsum_le_of_sum_le hFbound
  -- the operator
  have hmem : ∀ x : FeatureSpace d, Memℓp (fun n => ⟪rv n, x⟫) 2 := by
    intro x
    rw [memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hsum.mul_right (‖x‖ ^ 2))
    calc ⟪rv n, x⟫ ^ 2 = |⟪rv n, x⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖rv n‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
      _ = ‖rv n‖ ^ 2 * ‖x‖ ^ 2 := by ring
  let Rl : FeatureSpace d →ₗ[ℝ] K :=
    { toFun := fun x => b.repr.symm ⟨fun n => ⟪rv n, x⟫, hmem x⟩
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        refine Subtype.ext (funext fun n => ?_)
        show ⟪rv n, x + y⟫ = ⟪rv n, x⟫ + ⟪rv n, y⟫
        exact inner_add_right _ _ _
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        refine Subtype.ext (funext fun n => ?_)
        show ⟪rv n, c • x⟫ = c * ⟪rv n, x⟫
        exact inner_smul_right _ _ _ }
  have hRl : ∀ x, ‖Rl x‖ ^ 2 ≤ Bs * ‖x‖ ^ 2 := by
    intro x
    have h1 : ‖Rl x‖ = ‖(⟨fun n => ⟪rv n, x⟫, hmem x⟩ : lp (fun _ : ι => ℝ) 2)‖ := by
      show ‖b.repr.symm _‖ = _
      exact b.repr.symm.norm_map _
    rw [h1, (lp_two_sq _).2]
    have hs2 : Summable fun n => ‖rv n‖ ^ 2 * ‖x‖ ^ 2 := hsum.mul_right _
    calc ∑' n, ⟪rv n, x⟫ ^ 2 ≤ ∑' n, ‖rv n‖ ^ 2 * ‖x‖ ^ 2 := by
          refine ((lp_two_sq (⟨fun n => ⟪rv n, x⟫, hmem x⟩ : lp (fun _ : ι => ℝ) 2)).1).tsum_le_tsum
            (fun n => ?_) hs2
          calc ⟪rv n, x⟫ ^ 2 = |⟪rv n, x⟫| ^ 2 := (sq_abs _).symm
            _ ≤ (‖rv n‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
            _ = ‖rv n‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ = (∑' n, ‖rv n‖ ^ 2) * ‖x‖ ^ 2 := tsum_mul_right
      _ ≤ Bs * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right htsum (sq_nonneg _)
  have hRl' : ∀ x, ‖Rl x‖ ≤ Real.sqrt Bs * ‖x‖ := by
    intro x
    rw [← Real.sqrt_sq (norm_nonneg (Rl x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hBs0]
    exact Real.sqrt_le_sqrt (hRl x)
  let R : FeatureSpace d →L[ℝ] K := LinearMap.mkContinuous Rl (Real.sqrt Bs) hRl'
  have hRapp : ∀ x n, ⟪b n, R x⟫ = ⟪rv n, x⟫ := by
    intro x n
    have : b.repr (R x) = ⟨fun n => ⟪rv n, x⟫, hmem x⟩ := by
      show b.repr (b.repr.symm _) = _
      exact b.repr.apply_symm_apply _
    rw [← HilbertBasis.repr_apply_apply, this]
  refine ⟨R, fun y => ?_, ?_⟩
  · -- reconstruction
    apply b.repr.injective
    refine Subtype.ext (funext fun n => ?_)
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hRapp]
    rw [real_inner_comm, inner_chartFeature r hr (Torus.mk y) (rv n)]
    -- scalar inversion
    have hsb : Summable fun k : Lattice d => ‖fcoef (g n) k‖ := by
      have hws := summable_chartWeight (d := d) r hr
      have h1 := (hbes {n}).1 n (Finset.mem_singleton_self n)
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        ((h1.add hws).div_const 2)
      have hpk := hppos k
      have hc2 : 0 ≤ ‖fcoef (g n) k‖ := norm_nonneg _
      rw [hwp k]
      have : 0 ≤ p k * (‖fcoef (g n) k‖ - (p k)⁻¹) ^ 2 := by positivity
      have e2 : p k * (‖fcoef (g n) k‖ - (p k)⁻¹) ^ 2 =
          p k * ‖fcoef (g n) k‖ ^ 2 - 2 * ‖fcoef (g n) k‖ + (p k)⁻¹ := by
        field_simp
        ring
      simp only [hp] at this e2 ⊢
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    obtain ⟨-, hinv⟩ := s86_real_inversion (hgc n) hsb (Torus.mk y)
    have hdesc : g n (Torus.mk y) = ⟪b n, G y⟫ := descend_mk (hGnper n) y
    rw [← hdesc, ← hinv]
    refine tsum_congr fun k => ?_
    show (a n k / Real.sqrt (chartWeight r k)) * (Real.sqrt (chartWeight r k) * chartBasis k (Torus.mk y)) = _
    have := (Real.sqrt_pos.2 (hwpos k)).ne'
    field_simp
    ring
  · have hn : ‖R‖ ≤ Real.sqrt Bs := LinearMap.mkContinuous_norm_le Rl (Real.sqrt_nonneg _) hRl'
    calc ‖R‖ ^ 2 ≤ Real.sqrt Bs ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = Bs := Real.sq_sqrt hBs0

end HRS.MS.FinNoise
