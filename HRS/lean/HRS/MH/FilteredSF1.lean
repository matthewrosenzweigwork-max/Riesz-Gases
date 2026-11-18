import HRS.PDE.Classical
import HRS.PDE.EnergyTorusSqrt

/-!
# Packet SF1 `sf1_laplacian_iter_le` (iterated torus Laplacian bounded by the `C_b^{2L}` norm)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Route: lift `Δ^m φ` to `lapE^[m] (lift φ)` with `lapE G y = ∑ j, D_j D_j G y`; one-step bound
`‖D^i (lapE G)‖ ≤ d ‖D^{i+2} G‖`; iterate; finish with `norm_iteratedFDeriv_le_cbNorm`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS

variable {d : ℕ}

/-- Directional derivative along a vector `e`. -/
def sf1_dir (G : Euc d → ℝ) (e : Euc d) : Euc d → ℝ := fun z => fderiv ℝ G z e

/-- Euclidean Laplacian as the sum of second directional derivatives along the basis. -/
def sf1_lapE (G : Euc d → ℝ) : Euc d → ℝ :=
  fun y => ∑ j : Fin d, sf1_dir (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ)) y

lemma sf1_dir_bound (G : Euc d → ℝ) (e : Euc d) (he : ‖e‖ ≤ 1) (i : ℕ)
    (hG : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (i : WithTop ℕ∞) (sf1_dir G e) ∧
      ∀ y, ‖iteratedFDeriv ℝ i (sf1_dir G e) y‖ ≤ ‖iteratedFDeriv ℝ (i + 1) G y‖ := by
  have hf : ContDiff ℝ (i : WithTop ℕ∞) (fderiv ℝ G) :=
    hG.fderiv_right (by push_cast; exact le_rfl)
  have e1 : sf1_dir G e = (ContinuousLinearMap.apply ℝ ℝ e) ∘ (fderiv ℝ G) := rfl
  refine ⟨?_, fun y => ?_⟩
  · rw [e1]; exact (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp hf
  · rw [e1]
    refine ((ContinuousLinearMap.apply ℝ ℝ e).norm_iteratedFDeriv_comp_left hf.contDiffAt
      (by exact le_rfl)).trans ?_
    rw [norm_iteratedFDeriv_fderiv.symm]
    have : ‖ContinuousLinearMap.apply ℝ ℝ e‖ ≤ 1 :=
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
        simpa [mul_comm] using (f.le_opNorm e).trans (by nlinarith [norm_nonneg f, norm_nonneg e]))
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ i (fderiv ℝ G) y‖ := by gcongr
      _ = _ := one_mul _

lemma sf1_lapE_bound (G : Euc d → ℝ) (i : ℕ) (hG : ContDiff ℝ ((i + 2 : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (i : WithTop ℕ∞) (sf1_lapE G) ∧
      ∀ y, ‖iteratedFDeriv ℝ i (sf1_lapE G) y‖ ≤ d * ‖iteratedFDeriv ℝ (i + 2) G y‖ := by
  have he : ∀ j : Fin d, ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ ≤ 1 := fun j => by simp
  have h1 : ∀ j : Fin d, ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) ∧
      ∀ y, ‖iteratedFDeriv ℝ (i + 1) (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) y‖ ≤
        ‖iteratedFDeriv ℝ (i + 2) G y‖ := fun j =>
    sf1_dir_bound G _ (he j) (i + 1) hG
  have h2 : ∀ j : Fin d, ContDiff ℝ (i : WithTop ℕ∞)
      (sf1_dir (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ))) ∧
      ∀ y, ‖iteratedFDeriv ℝ i
        (sf1_dir (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ))) y‖ ≤
        ‖iteratedFDeriv ℝ (i + 2) G y‖ := fun j =>
    ⟨(sf1_dir_bound _ _ (he j) i (h1 j).1).1, fun y =>
      ((sf1_dir_bound _ _ (he j) i (h1 j).1).2 y).trans ((h1 j).2 y)⟩
  refine ⟨?_, fun y => ?_⟩
  · exact ContDiff.sum fun j _ => (h2 j).1
  · have e : sf1_lapE G = fun y => ∑ j : Fin d,
        sf1_dir (sf1_dir G (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ)) y := rfl
    rw [e, iteratedFDeriv_fun_sum_apply (fun j _ => (h2 j).1.contDiffAt)]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ j : Fin d, ‖iteratedFDeriv ℝ (i + 2) G y‖ := Finset.sum_le_sum fun j _ => (h2 j).2 y
      _ = _ := by simp

lemma sf1_lapE_iter (G : Euc d → ℝ) (m : ℕ) : ∀ i : ℕ,
    ContDiff ℝ ((i + 2 * m : ℕ) : WithTop ℕ∞) G →
    ContDiff ℝ (i : WithTop ℕ∞) ((sf1_lapE)^[m] G) ∧
      ∀ y, ‖iteratedFDeriv ℝ i ((sf1_lapE)^[m] G) y‖ ≤ (d : ℝ) ^ m * ‖iteratedFDeriv ℝ (i + 2 * m) G y‖ := by
  induction m with
  | zero => intro i hG; simpa using hG
  | succ m ih =>
    intro i hG
    have hG' : ContDiff ℝ ((i + 2 + 2 * m : ℕ) : WithTop ℕ∞) G := by
      have : i + 2 + 2 * m = i + 2 * (m + 1) := by omega
      rw [this]; exact hG
    obtain ⟨hc, hb⟩ := ih (i + 2) hG'
    rw [Function.iterate_succ_apply']
    obtain ⟨hc2, hb2⟩ := sf1_lapE_bound ((sf1_lapE)^[m] G) i hc
    refine ⟨hc2, fun y => (hb2 y).trans ?_⟩
    have : i + 2 + 2 * m = i + 2 * (m + 1) := by omega
    calc (d : ℝ) * ‖iteratedFDeriv ℝ (i + 2) ((sf1_lapE)^[m] G) y‖
        ≤ (d : ℝ) * ((d : ℝ) ^ m * ‖iteratedFDeriv ℝ (i + 2 + 2 * m) G y‖) := by
          gcongr; exact hb y
      _ = _ := by rw [this]; ring

lemma sf1_laplacian_lift (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    Torus.lift (Torus.laplacian ψ) = sf1_lapE (Torus.lift ψ) := by
  funext y
  have h := PDE.ClassicalAux.laplacian_mk ψ hψ y
  have hc : ContDiff ℝ 2 (Torus.lift ψ) := hψ
  have hd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift ψ)) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero _
  show Torus.laplacian ψ (Torus.mk y) = _
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  have e : sf1_dir (Torus.lift ψ) (EuclideanSpace.single j (1 : ℝ)) =
      fun z => fderiv ℝ (Torus.lift ψ) z (EuclideanSpace.single j (1 : ℝ)) := rfl
  show _ = fderiv ℝ (sf1_dir (Torus.lift ψ) (EuclideanSpace.single j (1 : ℝ))) y _
  rw [e, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem sf1_laplacian_iter_le (L : ℕ) {φ : Torus d → ℝ} (hφ : Torus.IsCk (2 * L : ℕ) φ) (x : Torus d) :
    |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x| ≤ (d : ℝ) ^ L * Torus.cbNorm (2 * L) φ := by
  have hlift : ∀ m, m ≤ L → Torus.lift ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[m] φ) =
      (sf1_lapE)^[m] (Torus.lift φ) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hm' : m ≤ L := by omega
      have h2 : Torus.IsCk 2 ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[m] φ) := by
        unfold Torus.IsCk
        rw [ih hm']
        refine (sf1_lapE_iter (Torus.lift φ) m 2 ?_).1
        have hc : ContDiff ℝ ((2 * L : ℕ) : WithTop ℕ∞) (Torus.lift φ) := hφ
        exact hc.of_le (by exact_mod_cast (by omega : 2 + 2 * m ≤ 2 * L))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sf1_laplacian_lift _ h2, ih hm']
  have hc : ContDiff ℝ ((0 + 2 * L : ℕ) : WithTop ℕ∞) (Torus.lift φ) := by
    have : ContDiff ℝ ((2 * L : ℕ) : WithTop ℕ∞) (Torus.lift φ) := hφ
    simpa using this
  obtain ⟨-, hb⟩ := sf1_lapE_iter (Torus.lift φ) L 0 hc
  have e : ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x =
      ((sf1_lapE)^[L] (Torus.lift φ)) (Torus.rep x) := by
    rw [← hlift L le_rfl]
    show _ = ((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) (Torus.mk (Torus.rep x))
    rw [Torus.mk_rep]
  rw [e, ← Real.norm_eq_abs, ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
  refine (hb (Torus.rep x)).trans ?_
  gcongr
  rw [zero_add]
  exact PDE.ET.norm_iteratedFDeriv_le_cbNorm le_rfl hφ _

end HRS.MH.FilteredP
