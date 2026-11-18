import HRS.MS.S82UD4

/-!
# S8.2 A01 (S82U): measurability of the triple model and identification with `tripleG`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

lemma u_uGm_meas {d : ℕ} {Fm : Euc d → Euc d} {g : Euc d → Euc d → Euc d} {Jt : Euc d → Euc d → ℝ}
    (hFm : Measurable Fm) (hgm : Measurable (Function.uncurry g)) (hJm : Measurable (Function.uncurry Jt)) :
    Measurable (fun p : Euc d × Euc d × Euc d => uGm Fm g Jt p.1 p.2.1 p.2.2) := by
  have hGm : Measurable (rieszKernelGrad d (criticalS d)) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have p1 : Measurable (fun p : Euc d × Euc d × Euc d => p.1) := measurable_fst
  have p2 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.1) := measurable_fst.comp measurable_snd
  have p3 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.2) := measurable_snd.comp measurable_snd
  have hg' : ∀ (u v : Euc d × Euc d × Euc d → Euc d), Measurable u → Measurable v →
      Measurable (fun p => g (u p) (v p)) := fun u v hu hv => hgm.comp (hu.prodMk hv)
  have hJ' : ∀ (u v : Euc d × Euc d × Euc d → Euc d), Measurable u → Measurable v →
      Measurable (fun p => Jt (u p) (v p)) := fun u v hu hv => hJm.comp (hu.prodMk hv)
  have huc : ∀ (u v : Euc d × Euc d × Euc d → Euc d), Measurable u → Measurable v →
      Measurable (fun p => uc Fm (u p) (v p)) := fun u v hu hv =>
    (hGm.comp (hu.sub hv)).sub (hFm.comp hu)
  have hT : ∀ (u v w : Euc d × Euc d × Euc d → Euc d), Measurable u → Measurable v → Measurable w →
      Measurable (fun p => uT Fm g (u p) (v p) (w p)) := by
    intro u v w hu hv hw
    unfold uT
    exact (Measurable.inner (huc u w hu hw) (hg' u v hu hv)).neg.sub
      (Measurable.inner (huc v w hv hw) (hg' v u hv hu))
  unfold uGm
  have h1 := hT _ _ _ p1 p2 p3
  have h2 := hT _ _ _ p1 p3 p2
  have h3 := hT _ _ _ p2 p3 p1
  have j1 := hJ' _ _ p1 p2
  have j2 := hJ' _ _ p1 p3
  have j3 := hJ' _ _ p2 p3
  exact (((((h1.add h2).add h3).sub j1).sub j2).sub j3).div_const 3

lemma u_uG_meas {d : ℕ} {Fm : Euc d → Euc d} {g : Euc d → Euc d → Euc d} {Jt : Euc d → Euc d → ℝ}
    (hFm : Measurable Fm) (hgm : Measurable (Function.uncurry g)) (hJm : Measurable (Function.uncurry Jt)) :
    Measurable (fun p : Euc d × Euc d × Euc d => uG Fm g Jt p.1 p.2.1 p.2.2) := by
  have p1 : Measurable (fun p : Euc d × Euc d × Euc d => p.1) := measurable_fst
  have p2 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.1) := measurable_fst.comp measurable_snd
  have p3 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.2) := measurable_snd.comp measurable_snd
  unfold uG
  refine Measurable.ite ?_ (u_uGm_meas hFm hgm hJm) measurable_const
  have s12 : MeasurableSet {p : Euc d × Euc d × Euc d | p.1 ≠ p.2.1} := (measurableSet_eq_fun p1 p2).compl
  have s13 : MeasurableSet {p : Euc d × Euc d × Euc d | p.1 ≠ p.2.2} := (measurableSet_eq_fun p1 p3).compl
  have s23 : MeasurableSet {p : Euc d × Euc d × Euc d | p.2.1 ≠ p.2.2} := (measurableSet_eq_fun p2 p3).compl
  exact s12.inter (s13.inter s23)

lemma u_uGm_sec_meas {d : ℕ} {Fm : Euc d → Euc d} {g : Euc d → Euc d → Euc d} {Jt : Euc d → Euc d → ℝ}
    (hFm : Measurable Fm) (hgm : Measurable (Function.uncurry g)) (hJm : Measurable (Function.uncurry Jt))
    (x y : Euc d) : Measurable (fun z => uGm Fm g Jt x y z) := by
  have h := u_uGm_meas hFm hgm hJm
  have hφ : Measurable (fun z : Euc d => ((x, (y, z)) : Euc d × Euc d × Euc d)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have := h.comp hφ
  simpa [Function.comp_def] using this

lemma u_hJsmall {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (p q : Euc d) (hpq : p ≠ q) :
    |s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q) p q| ≤
      A * Phase2S82.pairWeight M p q * pole p q := by
  rw [← s82t_pairJ_eq hd hQ p q hpq]
  exact hQ.nonlocal.2 p q hpq

lemma u_tripleG_eq {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {x y z : Euc d}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleG (critCoeff d a beta rho) rho Q x y z =
      uGm (forceMean rho) (s82p2_gt Q)
        (s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q)) x y z := by
  have hTeq : ∀ p q r : Euc d, p ≠ q →
      tripleT rho Q p q r = uT (forceMean rho) (s82p2_gt Q) p q r := by
    intro p q r hpq
    unfold tripleT uT
    rw [← s82p2_gt_eq hQ p q hpq, s82t_pairGradY_eq hQ p q hpq]
    rfl
  unfold tripleG uGm
  rw [hTeq x y z hxy, hTeq x z y hxz, hTeq y z x hyz, s82t_pairJ_eq hd hQ x y hxy,
    s82t_pairJ_eq hd hQ x z hxz, s82t_pairJ_eq hd hQ y z hyz]

end HRS.MS.S82U
