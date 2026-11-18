import HRS.Torus.Basic
import HRS.MS.S104eC3A

noncomputable section

open Filter Topology
open scoped ContDiff

namespace HRS.Fp81.S21

open HRS

local notation "J" => iteratedFDeriv ℝ
theorem fp81s21_b3_jets_limit_local {d k : ℕ}
    {fn : ℕ → Euc d → ℝ} {f : Euc d → ℝ}
    {H : ∀ m : ℕ, Euc d → (Euc d [×m]→L[ℝ] ℝ)}
    (hC : ∀ n, ContDiff ℝ k (fn n))
    (hlim : ∀ m ≤ k,
      TendstoLocallyUniformly (fun n => J m (fn n)) (H m) atTop)
    (hf : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) :
    ContDiff ℝ k f ∧ ∀ m ≤ k, J m f = H m := by
  have hTaylor : ContDiff ℝ k f ∧ ∀ m ≤ k, ∀ x, J m f x = H m x := by
    refine HRS.MS.S104e.C.s104c3_ftaylor_of_jets (N := k) (f := f)
      (p := fun x m => H m x) ?_ ?_ ?_
    · intro x
      have h1 : Tendsto (fun n => J 0 (fn n) x) atTop (𝓝 (H 0 x)) :=
        (hlim 0 (Nat.zero_le _)).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)
      have h2 := ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.tendsto _).comp h1
      have h3 : ∀ n, (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ) (J 0 (fn n) x) = fn n x :=
        fun n => by simp [iteratedFDeriv_zero_eq_comp]
      have h4 : Tendsto (fun n => fn n x) atTop
          (𝓝 ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ) (H 0 x))) := by
        simpa [Function.comp_def, h3] using h2
      rw [ContinuousMultilinearMap.curry0_apply]
      have heq := tendsto_nhds_unique h4 (hf x)
      simpa using heq
    · intro m hm x
      have hm' : m < k := hm
      have hu : TendstoLocallyUniformly
          (fun n y => (J (m + 1) (fn n) y).curryLeft)
          (fun y => (H (m + 1) y).curryLeft) atTop := by
        let L := (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (m + 1) => Euc d) ℝ).toContinuousLinearEquiv
        have hL := L.toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformly
          (hlim (m + 1) hm)
        have hEq : ∀ A, L A = A.curryLeft := by
          intro A
          rfl
        simpa [Function.comp_def, hEq] using hL
      have hderiv : HasFDerivAt (fun y => H m y) ((H (m + 1) x).curryLeft) x := by
        apply hasFDerivAt_of_tendstoLocallyUniformlyOn (s := Set.univ) isOpen_univ (hu.tendstoLocallyUniformlyOn (s := Set.univ))
        · intro n y hy
          have h := ((hC n).differentiable_iteratedFDeriv (m := m)
            (by exact_mod_cast hm') y).hasFDerivAt
          rw [fderiv_iteratedFDeriv] at h
          exact h
        · intro y hy
          exact (hlim m hm.le).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ y)
        · exact Set.mem_univ x
      exact hderiv
    · intro m hm
      exact (hlim m hm).continuous (Eventually.of_forall fun n =>
        (hC n).continuous_iteratedFDeriv (by exact_mod_cast hm)).frequently
  exact ⟨hTaylor.1, fun m hm => funext (hTaylor.2 m hm)⟩

#print axioms HRS.Fp81.S21.fp81s21_b3_jets_limit_local

end HRS.Fp81.S21
