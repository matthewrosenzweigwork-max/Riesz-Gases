import HRS.MS.Fp81S21WeightedGenNL12

/-! Derivative identification for limits of compact-source convolutions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.Ul

/-- Convolution derivatives pass to a source limit, assuming the generic local
jet-limit and convolution-continuity lemmas. -/
theorem fp81s21_b3_ultK_iter_limit {d k : ℕ}
    (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ}
    (hκ : UlKer κ s) (hs : s + 1 < d)
    (hA : ∀ {fn : ℕ → Euc d → ℝ} {f : Euc d → ℝ}
      {H : ∀ m : ℕ, Euc d → (Euc d [×m]→L[ℝ] ℝ)},
      (∀ n, ContDiff ℝ k (fn n)) →
      (∀ m ≤ k, TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ m (fn n)) (H m) atTop) →
      (∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) →
      ContDiff ℝ k f ∧ ∀ m ≤ k, iteratedFDeriv ℝ m f = H m)
    (hB : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {gn : ℕ → Euc d → F} {g : Euc d → F},
      (∀ n, Continuous (gn n)) → Continuous g →
      (∀ n, Integrable (gn n)) → Integrable g →
      TendstoLocallyUniformly gn g atTop →
      Tendsto (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0) →
      TendstoLocallyUniformly (fun n => ultK κ (gn n)) (ultK κ g) atTop)
    {gn : ℕ → Euc d → ℝ} {g : Euc d → ℝ}
    (hdec : ∀ n, ∃ L A : ℝ, (d : ℝ) < L ∧ 0 ≤ A ∧ U2Dec (k + 1) L A (gn n))
    (hc : ContDiff ℝ k g)
    (hi : ∀ m ≤ k, Integrable (iteratedFDeriv ℝ m g))
    (ht : ∀ m ≤ k,
      TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ m (gn n)) (iteratedFDeriv ℝ m g) atTop ∧
      Tendsto (fun n => eLpNorm (iteratedFDeriv ℝ m (gn n) - iteratedFDeriv ℝ m g) 1 volume)
        atTop (𝓝 0)) :
    ContDiff ℝ k (ultK κ g) ∧
    ∀ m ≤ k, iteratedFDeriv ℝ m (ultK κ g) = ultK κ (iteratedFDeriv ℝ m g) ∧
      TendstoLocallyUniformly (fun n => iteratedFDeriv ℝ m (ultK κ (gn n)))
        (iteratedFDeriv ℝ m (ultK κ g)) atTop := by
  have hnc : ∀ n, ContDiff ℝ (k + 1) (gn n) := by
    intro n
    obtain ⟨L, A, hL, hA, h⟩ := hdec n
    exact h.1
  have hni : ∀ n m, m ≤ k → Integrable (iteratedFDeriv ℝ m (gn n)) := by
    intro n m hm
    obtain ⟨L, A, hL, hA, h⟩ := hdec n
    refine ((u2_integrable_wt hL).const_mul A).mono' ?_ ?_
    · exact (h.1.continuous_iteratedFDeriv (by exact_mod_cast (show m ≤ k + 1 by omega))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (h.2 m (by omega))
  have hconv : ∀ m ≤ k, TendstoLocallyUniformly
      (fun n => ultK κ (iteratedFDeriv ℝ m (gn n)))
      (ultK κ (iteratedFDeriv ℝ m g)) atTop := by
    intro m hm
    exact hB (fun n => (hnc n).continuous_iteratedFDeriv (by exact_mod_cast (show m ≤ k + 1 by omega)))
      (hc.continuous_iteratedFDeriv (by exact_mod_cast hm)) (fun n => hni n m hm) (hi m hm) (ht m hm).1 (ht m hm).2
  have hzloc : TendstoLocallyUniformly gn g atTop := by
    have hh := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformly (ht 0 (Nat.zero_le k)).1
    simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using hh
  have hzL1 : Tendsto (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0) := by
    have heq : ∀ n, eLpNorm (gn n - g) 1 volume =
        eLpNorm (iteratedFDeriv ℝ 0 (gn n) - iteratedFDeriv ℝ 0 g) 1 volume := by
      intro n
      have hn0 : Continuous (iteratedFDeriv ℝ 0 (gn n)) :=
        (hnc n).continuous_iteratedFDeriv (by simp)
      have hg0 : Continuous (iteratedFDeriv ℝ 0 g) :=
        hc.continuous_iteratedFDeriv (by simp)
      apply eLpNorm_congr_norm_ae ((hnc n).continuous.sub hc.continuous).aestronglyMeasurable
        (hn0.sub hg0).aestronglyMeasurable
      filter_upwards [] with x
      simp only [Pi.sub_apply, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]
    simp_rw [heq]
    exact (ht 0 (Nat.zero_le k)).2
  have hbase := hB (fun n => (hnc n).continuous) hc.continuous
    (fun n => by simpa [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ 0).integrable_comp (hni n 0 (Nat.zero_le k)))
    (by simpa [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ 0).integrable_comp (hi 0 (Nat.zero_le k)))
    hzloc hzL1
  have hiter : ∀ n m, m ≤ k → iteratedFDeriv ℝ m (ultK κ (gn n)) = ultK κ (iteratedFDeriv ℝ m (gn n)) := by
    intro n m hm
    obtain ⟨L, A, hL, hA, h⟩ := hdec n
    exact funext ((ult_K_iter hd hκ hL hA h).1 m hm)
  have hlim : ∀ m ≤ k, TendstoLocallyUniformly
      (fun n => iteratedFDeriv ℝ m (ultK κ (gn n)))
      (ultK κ (iteratedFDeriv ℝ m g)) atTop := by
    intro m hm
    exact (hconv m hm).congr (fun n x => (congrFun (hiter n m hm) x).symm)
  have hcd : ∀ n, ContDiff ℝ k (ultK κ (gn n)) := by
    intro n
    obtain ⟨L, A, hL, hA, h⟩ := hdec n
    exact (ult_K_iter hd hκ hL hA h).2
  obtain ⟨hC, hident⟩ := hA hcd hlim (fun x => hbase.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x))
  refine ⟨hC, fun m hm => ⟨hident m hm, ?_⟩⟩
  rw [hident m hm]
  exact hlim m hm

#print axioms HRS.Fp81.S21.fp81s21_b3_ultK_iter_limit
end HRS.Fp81.S21
