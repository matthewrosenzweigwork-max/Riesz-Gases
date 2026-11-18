import HRS.MS.R2SeAux42

/-!
# S9.9 `r2_static_edgeworth`, packet 43: nested partial derivatives and the third-derivative series

Worker S99, namespace `S99`.

* `s99_iter_succ`, `s99_third_apply`: `D³f(z)[e_m,e_k,e_j] = ∂_m∂_k∂_j f(z)`;
* `ellv`: the vector `ℓ_x = (a_j(x))_j ∈ ℓ²`;
* `s99_third_series`: `∫_G ∫_μ D³Φ'(z)[ℓ_x,ℓ_x,ℓ_x] = ∑_{jkm} κ_{jkm} ∫_G D³Φ'(z)[e_m,e_k,e_j]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_iter_succ {g : SeqL2 → ℝ} {n : ℕ} (hg : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g) (y : SeqL2)
    (m : Fin (n + 1) → SeqL2) :
    iteratedFDeriv ℝ (n + 1) g y m =
      fderiv ℝ (fun y' => iteratedFDeriv ℝ n g y' (Fin.tail m)) y (m 0) := by
  rw [iteratedFDeriv_succ_apply_left]
  have hD : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => SeqL2) ℝ (Fin.tail m)).hasFDerivAt.comp y
    (hD y).hasFDerivAt
  rw [show (fun y' => iteratedFDeriv ℝ n g y' (Fin.tail m)) =
    (fun T => ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => SeqL2) ℝ (Fin.tail m) T) ∘ iteratedFDeriv ℝ n g from rfl,
    h.fderiv]
  rfl

theorem s99_third_apply {f : SeqL2 → ℝ} (hf : ContDiff ℝ 3 f) (z : SeqL2) (j k m : ℕ) :
    iteratedFDeriv ℝ 3 f z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] =
      pd (pd (pd f j) k) m z := by
  have h3 : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) f := by exact_mod_cast hf
  have h2 : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) f := hf.of_le (by norm_num)
  have h1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) f := hf.of_le (by norm_num)
  have e1 : ∀ y, iteratedFDeriv ℝ 1 f y ![s45_e1 j (1 : ℝ)] = pd f j y := fun y => by
    rw [iteratedFDeriv_one_apply]; rfl
  have e2 : ∀ y, iteratedFDeriv ℝ 2 f y ![s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] = pd (pd f j) k y := fun y => by
    rw [s99_iter_succ h2]
    have : (fun y' => iteratedFDeriv ℝ 1 f y' (Fin.tail ![s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)])) = pd f j := by
      funext y'
      have := e1 y'
      simpa [Fin.tail] using this
    rw [this]; rfl
  rw [s99_iter_succ h3]
  have : (fun y' => iteratedFDeriv ℝ 2 f y' (Fin.tail ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)])) =
      pd (pd f j) k := by
    funext y'
    have := e2 y'
    simpa [Fin.tail] using this
  rw [this]; rfl

/-- The vector `ℓ_x = (a_j(x))_j`. -/
def ellv (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) (x : Euc d) : SeqL2 :=
  SeqL2.ofSeq fun j => aRep d s a β γ (φ j) x

section Series

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU : ℝ} (hT : ThermalData d s a β C c BU)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hφ F

theorem s99_ellv_memlp (x : Euc d) : Memℓp (fun j => aRep d s a β γ (φ j) x) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hb0 : ∀ j, 0 ≤ F.K * cbNorm (J1 d) (φ j) := fun j => by
    have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (J1 d) (φ j); have := F.hK; positivity
  have hs2 : Summable fun j => (F.K * cbNorm (J1 d) (φ j)) ^ 2 := s45_summable_sq hb0 (hφ.2.mul_left _)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((s99_ua hd hs0 hs ha hβ hγ hT hφ F j).2.1 x) 2

theorem s99_ellv_coord (x : Euc d) (j : ℕ) :
    SeqL2.coord (ellv d s a β γ φ x) j = aRep d s a β γ (φ j) x :=
  s45_coord_ofSeq (s99_ellv_memlp hd hs0 hs ha hβ hγ hT hφ F x) j

end Series

section Series2

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

set_option maxHeartbeats 2000000 in
theorem s99_third_series {G : Measure SeqL2} [IsProbabilityMeasure G] {Φ' : SeqL2 → ℝ}
    (hΦ : ContDiff ℝ 3 Φ') (hb : ∀ z, ‖iteratedFDeriv ℝ 3 Φ' z‖ ≤ 1) :
    ∫ z, (∫ x, iteratedFDeriv ℝ 3 Φ' z ![ellv d s a β γ φ x, ellv d s a β γ φ x, ellv d s a β γ φ x]
        ∂(thermalMeasure d s a β)) ∂G =
      ∑' j, ∑' k, ∑' m, kap3 d s a β γ φ j k m *
        ∫ z, iteratedFDeriv ℝ 3 Φ' z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set bb : ℕ → ℝ := fun j => F.K * cbNorm (J1 d) (φ j) with hbbdef
  have hb0 : ∀ j, 0 ≤ bb j := fun j => by
    have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (J1 d) (φ j); have := F.hK; positivity
  have hbs : Summable bb := hφ.2.mul_left _
  set t : SeqL2 → ℕ → ℕ → ℕ → ℝ := fun z j k m =>
    iteratedFDeriv ℝ 3 Φ' z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] with ht
  have htb : ∀ z j k m, |t z j k m| ≤ 1 := fun z j k m => by
    simp only [ht]
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp only [Fin.prod_univ_three]
    simp [s99_e1_norm]
    exact hb z
  have htc : ∀ j k m, Continuous fun z => t z j k m := fun j k m => by
    simp only [ht]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => SeqL2) ℝ _).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by norm_num))
  have hua : ∀ j, Continuous (aRep d s a β γ (φ j)) := fun j =>
    (s99_ua hd hs0 hs ha hβ hγ hT hφ F j).1.continuous
  have hub : ∀ j x, |aRep d s a β γ (φ j) x| ≤ bb j := fun j x =>
    (s99_ua hd hs0 hs ha hβ hγ hT hφ F j).2.1 x
  -- the inner integral
  have hinner : ∀ z, ∫ x, iteratedFDeriv ℝ 3 Φ' z ![ellv d s a β γ φ x, ellv d s a β γ φ x, ellv d s a β γ φ x]
      ∂(thermalMeasure d s a β) = ∑' j, ∑' k, ∑' m, kap3 d s a β γ φ j k m * t z j k m := by
    intro z
    have hpt : ∀ x, iteratedFDeriv ℝ 3 Φ' z ![ellv d s a β γ φ x, ellv d s a β γ φ x, ellv d s a β γ φ x] =
        ∑' j, ∑' k, ∑' m, aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x * aRep d s a β γ (φ m) x * t z j k m := by
      intro x
      rw [s99_third_expand]
      simp only [s99_ellv_coord hd hs0 hs ha hβ hγ hT hφ F x, ht]
    simp_rw [hpt]
    rw [s99_int_tsum3 (fun j k m x => aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x *
      aRep d s a β γ (φ m) x * t z j k m) hbs hb0 (fun j k m x => by
        rw [abs_mul, abs_mul, abs_mul]
        calc |aRep d s a β γ (φ j) x| * |aRep d s a β γ (φ k) x| * |aRep d s a β γ (φ m) x| * |t z j k m|
            ≤ bb j * bb k * bb m * 1 :=
              mul_le_mul (mul_le_mul (mul_le_mul (hub j x) (hub k x) (abs_nonneg _) (hb0 j)) (hub m x)
                (abs_nonneg _) (mul_nonneg (hb0 j) (hb0 k))) (htb z j k m) (abs_nonneg _)
                (mul_nonneg (mul_nonneg (hb0 j) (hb0 k)) (hb0 m))
          _ = _ := mul_one _)
      (fun j k m => ((((hua j).mul (hua k)).mul (hua m)).mul continuous_const).measurable)]
    refine tsum_congr fun j => tsum_congr fun k => tsum_congr fun m => ?_
    rw [integral_mul_const]
    rfl
  simp_rw [hinner]
  rw [s99_int_tsum3 (fun j k m z => kap3 d s a β γ φ j k m * t z j k m) hbs hb0 (fun j k m z => by
      rw [abs_mul]
      have := s99_kap3_bd hd hs0 hs ha hβ hγ hT hS hφ F j k m
      calc |kap3 d s a β γ φ j k m| * |t z j k m| ≤ (bb j * bb k * bb m) * 1 :=
            mul_le_mul (this.trans (le_of_eq (by simp only [hbbdef]; ring))) (htb z j k m) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (hb0 j) (hb0 k)) (hb0 m))
        _ = _ := mul_one _)
    (fun j k m => (continuous_const.mul (htc j k m)).measurable)]
  refine tsum_congr fun j => tsum_congr fun k => tsum_congr fun m => ?_
  rw [integral_const_mul]

end Series2

end S99

end
