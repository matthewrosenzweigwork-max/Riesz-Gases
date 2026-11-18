import HRS.MS.Fp81S21WeightedMoments7
import HRS.MS.Fp81S21MovingMeas

/-! Configuration-level measurable Riesz representatives for the centered quadratic field. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

/-- Density integration measurability for parameter spaces in arbitrary universes. -/
theorem fp81s21_moving_density_integral_meas_bigU
    {d : ℕ} {U : Type*} [MeasurableSpace U]
    {ρ : U → Euc d → ℝ} (hρ : Measurable (fun q : U × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    {f : U → Euc d → ℝ} (hf : Measurable (fun q : U × Euc d => f q.1 q.2)) :
    Measurable fun u => ∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u)) := by
  have hweighted : Measurable (fun q : U × Euc d => f q.1 q.2 * ρ q.1 q.2) := hf.mul hρ
  have hbase : Measurable fun u => ∫ x, f u x * ρ u x :=
    (hweighted.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun u => ∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u))) =
      fun u => ∫ x, f u x * ρ u x := by
    funext u
    calc
      (∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u))) = ∫ x, ρ u x * f u x :=
        HRS.MP.RdRem.mrr_integral_withDensityReal (ρ u)
          (hρ.comp (measurable_const.prodMk measurable_id)) (hρ0 u) (f u)
      _ = ∫ x, f u x * ρ u x := by
        congr 1
        funext x
        ring
  rw [heq]
  exact hbase

/-- Total integral measurability for probability spaces in arbitrary universes. -/
theorem fp81s21_moving_total_integral_meas_bigU
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {F : ℝ × Ω → ℝ} (hF : Measurable F) :
    Measurable (fun u : ℝ => ∫ ω, F (u, ω) ∂P) := by
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- Joint measurability of a pair energy along a moving measurable configuration.
This version integrates its particle coordinates directly, so the probability
variable need not be identified with the configuration space. -/
theorem fp81s21_moving_pairEnergy_process_joint_meas
    {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ρ : ℝ → Euc d → ℝ} {k : ℝ → Euc d → Euc d → ℝ}
    {Y : ℝ × Ω → EucConfig d N}
    (hρ : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hk : Measurable fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2)
    (hY : Measurable Y) :
    Measurable (fun q : ℝ × Ω =>
      HRS.Whole.pairEnergy (k q.1) (Y q) (HRS.Whole.withDensityReal (ρ q.1))) := by
  let ρU : (ℝ × Ω) → Euc d → ℝ := fun q x => ρ q.1 x
  have hρU : Measurable (fun q : (ℝ × Ω) × Euc d => ρU q.1 q.2) := by
    exact hρ.comp (measurable_fst.fst.prodMk measurable_snd)
  have hρU0 : ∀ q x, 0 ≤ ρU q x := fun q x => hρ0 q.1 x
  have hrowParticle (i : Fin N) : Measurable (fun q : ℝ × Ω =>
      ∫ y, k q.1 (Y q i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) := by
    have hYi : Measurable (fun q : ℝ × Ω => Y q i) :=
      (measurable_pi_apply i).comp hY
    have hf : Measurable (fun q : (ℝ × Ω) × Euc d =>
        k q.1.1 (Y q.1 i) q.2) :=
      hk.comp (measurable_fst.fst.prodMk
        ((hYi.comp measurable_fst).prodMk measurable_snd))
    exact fp81s21_moving_density_integral_meas_bigU (ρ := ρU) hρU hρU0 hf
  have hρInner : Measurable (fun q : ((ℝ × Ω) × Euc d) × Euc d =>
      ρ q.1.1.1 q.2) :=
    hρ.comp (measurable_fst.fst.fst.prodMk measurable_snd)
  have hρInner0 : ∀ (q : (ℝ × Ω) × Euc d) x,
      0 ≤ ρ q.1.1 x := fun q x => hρ0 q.1.1 x
  have hInner : Measurable (fun q : (ℝ × Ω) × Euc d =>
      ∫ y, k q.1.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1.1))) := by
    have hf : Measurable (fun q : ((ℝ × Ω) × Euc d) × Euc d =>
        k q.1.1.1 q.1.2 q.2) :=
      hk.comp (measurable_fst.fst.fst.prodMk
        (measurable_fst.snd.prodMk measurable_snd))
    exact fp81s21_moving_density_integral_meas_bigU
      (ρ := fun q : (ℝ × Ω) × Euc d => ρ q.1.1) hρInner hρInner0 hf
  have hdouble : Measurable (fun q : ℝ × Ω =>
      ∫ x, ∫ y, k q.1 x y ∂(HRS.Whole.withDensityReal (ρ q.1))
        ∂(HRS.Whole.withDensityReal (ρ q.1))) :=
    fp81s21_moving_density_integral_meas_bigU (ρ := ρU) hρU hρU0 hInner
  have hpp : Measurable (fun q : ℝ × Ω =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (Y q i) (Y q j)) := by
    refine Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => ?_
    have hi : Measurable (fun q : ℝ × Ω => Y q i) :=
      (measurable_pi_apply i).comp hY
    have hj : Measurable (fun q : ℝ × Ω => Y q j) :=
      (measurable_pi_apply j).comp hY
    exact hk.comp (measurable_fst.prodMk (hi.prodMk hj))
  have hrows : Measurable (fun q : ℝ × Ω =>
      ∑ i, ∫ y, k q.1 (Y q i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) :=
    Finset.measurable_sum _ fun i _ => hrowParticle i
  have hformula : (fun q : ℝ × Ω =>
      HRS.Whole.pairEnergy (k q.1) (Y q) (HRS.Whole.withDensityReal (ρ q.1))) =
      (fun q => (1 / (2 * (N : ℝ) ^ 2)) *
          (∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (Y q i) (Y q j)) -
        (1 / (N : ℝ)) *
          (∑ i, ∫ y, k q.1 (Y q i) y
            ∂(HRS.Whole.withDensityReal (ρ q.1))) +
        (1 / 2) * ∫ x, ∫ y, k q.1 x y
          ∂(HRS.Whole.withDensityReal (ρ q.1))
          ∂(HRS.Whole.withDensityReal (ρ q.1))) := by
    funext q
    rfl
  rw [hformula]
  exact ((hpp.const_mul _).sub (hrows.const_mul _)).add (hdouble.const_mul _)

/-- A jointly measurable configuration representative of the centered quadratic field.
The final clause is the pathwise `s102_Z_quad` estimate needed by moment transfer. -/
theorem fp81s21_quad_config_rep
    {d N : ℕ} {s M L C₀ c₀ β pint K : ℝ}
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hc₀ : 0 < c₀) (hβ : 0 < β) (hp : 1 < pint)
    {ρ : ℝ → Euc d → ℝ}
    (hρm : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hround : ∀ u, IsRound2Density d s M L (ρ u))
    (hgauss : ∀ u x, ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ × Ω → EucConfig d N) (hY : Measurable Y)
    (hactual : ∀ u, HasR2ActualDensity s β pint K
      (HRS.Whole.withDensityReal (ρ u)) (P.map (fun ω => Y (u, ω))))
    (E : r26t6_WeightedChart d (2 * d + 8) ((d : ℝ) + 2)) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      ∃ z : ℝ → EucConfig d N → r26t6_Coeff,
        Measurable (Function.uncurry z) ∧
        (∀ (u : ℝ) (X : EucConfig d N), fp81s21_TestRep E
          (fun f => r2CommDistr d s (HRS.Whole.withDensityReal (ρ u)) X f -
            ∫ ω : Ω, r2CommDistr d s (HRS.Whole.withDensityReal (ρ u))
              (Y (u, ω)) f ∂P)
          (z u X)) ∧
        (∀ (u : ℝ) (X : EucConfig d N) (f : Euc d → ℝ),
          IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f →
          |r2CommDistr d s (HRS.Whole.withDensityReal (ρ u)) X f -
            ∫ ω : Ω, r2CommDistr d s (HRS.Whole.withDensityReal (ρ u))
              (Y (u, ω)) f ∂P| ≤
          c₁ * N *
            (s102_Env (s102_gk s ((d : ℝ) + 2)) X
                (HRS.Whole.withDensityReal (ρ u)) +
              ∫ ω : Ω, s102_Env (s102_gk s ((d : ℝ) + 2)) (Y (u, ω))
                (HRS.Whole.withDensityReal (ρ u)) ∂P) *
            (weightedSobolevE (2 * d + 8) ((d : ℝ) + 2) f).toReal) := by
  have hd1 : 1 ≤ d := by omega
  have hPw : 0 ≤ (d : ℝ) + 2 := by positivity
  have hchartP : (d : ℝ) < 2 * ((d : ℝ) + 2) := by nlinarith
  have hr : (d : ℝ) / 2 + 2 < ((2 * d + 8 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  obtain ⟨c₁, hc₁, hker⟩ :=
    s102_comm_poly hd1 hs0 hPw (2 * d + 8) hr
  obtain ⟨Agk, hgk₁⟩ := s102_gk_int hd1 hs0 hs M C₀ c₀ hc₀ hPw
  rcases hgk₁ with ⟨hgk0, hgk⟩
  obtain ⟨CE, hCE₁⟩ :=
    s102_Env_bound hd hs0 hs M L C₀ c₀ β pint K hc₀ hβ hp hPw
  rcases hCE₁ with ⟨hCE0, henvelope⟩
  have hρ0 : ∀ u x, 0 ≤ ρ u x := by
    intro u x
    exact (hround u).prob.nonneg x
  let Tactual : ℝ × EucConfig d N → (Euc d → ℝ) → ℝ := fun q f =>
    r2CommDistr d s (HRS.Whole.withDensityReal (ρ q.1)) q.2 f -
      ∫ ω : Ω, r2CommDistr d s (HRS.Whole.withDensityReal (ρ q.1))
        (Y (q.1, ω)) f ∂P
  let T : ℝ × EucConfig d N → (Euc d → ℝ) → ℝ := fun q f =>
    s102_fld (P.map (fun ω => Y (q.1, ω)))
      (HRS.Whole.withDensityReal (ρ q.1)) (fun X => X)
      (commutatorKernel d s (fun x => gradient f x)) q.2
  have hT_eq (u : ℝ) (X : EucConfig d N) (f : Euc d → ℝ)
      (hf : IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f) :
      T (u, X) f = Tactual (u, X) f := by
    let μ := HRS.Whole.withDensityReal (ρ u)
    let Ya : Ω → EucConfig d N := fun ω => Y (u, ω)
    have hYa : Measurable Ya := hY.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu (hround u).prob
    have hkernel : Measurable (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient f) xy.1 xy.2) :=
      (hker f hf.1 hf.2).1.measurable
    have hpair : Measurable (fun X' : EucConfig d N =>
        pairEnergy (commutatorKernel d s (gradient f)) X' μ) :=
      HRS.MS.Wr.wr9_measurable_pairEnergy hkernel
    have hmap : (∫ X', pairEnergy (commutatorKernel d s (gradient f)) X' μ
        ∂(P.map Ya)) =
        ∫ ω : Ω, pairEnergy (commutatorKernel d s (gradient f)) (Ya ω) μ ∂P :=
      integral_map hYa.aemeasurable hpair.aestronglyMeasurable
    dsimp [T, Tactual, HRS.Whole.r2CommDistr, s102_fld]
    rw [integral_const_mul, ← hmap]
    ring
  have hZraw : ∀ a : ℝ × EucConfig d N,
      S102Z (2 * d + 8) ((d : ℝ) + 2) (T a) ∧
        ∀ f, IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f →
          |Tactual a f| ≤ c₁ * N *
            (s102_Env (s102_gk s ((d : ℝ) + 2)) a.2
                (HRS.Whole.withDensityReal (ρ a.1)) +
              ∫ ω : Ω, s102_Env (s102_gk s ((d : ℝ) + 2)) (Y (a.1, ω))
                (HRS.Whole.withDensityReal (ρ a.1)) ∂P) *
            (weightedSobolevE (2 * d + 8) ((d : ℝ) + 2) f).toReal := by
    intro a
    let μ := HRS.Whole.withDensityReal (ρ a.1)
    let Ya : Ω → EucConfig d N := fun ω => Y (a.1, ω)
    have hYa : Measurable Ya := hY.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure μ :=
      HRS.Whole.Q34.isProbabilityMeasure_nu (hround a.1).prob
    obtain ⟨hgi, hgH, -⟩ := hgk (ρ a.1) (hround a.1).prob
      (hround a.1).bdd (hgauss a.1)
    have hactualMap : HasR2ActualDensity s β pint K μ
        (Measure.map (fun X : EucConfig d N => X) (P.map Ya)) := by
      change HasR2ActualDensity s β pint K μ ((P.map Ya).map id)
      rw [Measure.map_id]
      exact hactual a.1
    obtain ⟨hEi, -⟩ := henvelope (hround a.1) (hgauss a.1) hN
      (P.map Ya) (fun X => X) measurable_id hactualMap
    have hEnvMeas : Measurable (fun X : EucConfig d N =>
        s102_Env (s102_gk s ((d : ℝ) + 2)) X μ) :=
      s102_Env_meas (s102_gk_meas s ((d : ℝ) + 2))
    have hEiMap : Integrable
        (fun X : EucConfig d N => s102_Env (s102_gk s ((d : ℝ) + 2)) X μ)
        (P.map Ya) := hEi
    have hEnvMap :
        (∫ X : EucConfig d N, s102_Env (s102_gk s ((d : ℝ) + 2)) X μ
          ∂(P.map Ya)) =
        ∫ ω : Ω, s102_Env (s102_gk s ((d : ℝ) + 2)) (Ya ω) μ ∂P :=
      integral_map hYa.aemeasurable hEnvMeas.aestronglyMeasurable
    obtain ⟨hZ, hbound⟩ := s102_Z_quad (s := s)
      (Pw := (d : ℝ) + 2) (2 * d + 8) hr hc₁ hker hgi hgH
      (P.map Ya) (fun X => X) measurable_id hEiMap a.2
    refine ⟨hZ, ?_⟩
    intro f hf
    have hbound' := hbound f hf
    rw [hEnvMap] at hbound'
    rw [← hT_eq a.1 a.2 f hf]
    exact hbound'
  have hk : ∀ j, Measurable
      (fun q : ℝ × Euc d × Euc d =>
        commutatorKernel d s (gradient (E.test j)) q.2.1 q.2.2) := by
    intro j
    exact (HRS.MS.Comm.comm_meas _
      (HRS.MH.DualityRd.db1_gradient_continuous
        ((E.test_smooth j).1.of_le (by norm_num))).measurable).comp measurable_snd
  have hPair : ∀ j, Measurable
      (fun q : ℝ × EucConfig d N =>
        pairEnergy (commutatorKernel d s (gradient (E.test j))) q.2
          (HRS.Whole.withDensityReal (ρ q.1))) := by
    intro j
    exact fp81s21_moving_pairEnergy_joint_meas (d := d) (N := N)
      (ρ := ρ) (k := fun _ x y =>
        commutatorKernel d s (gradient (E.test j)) x y) hρm hρ0 (hk j)
  have hPairY : ∀ j, Measurable
      (fun q : ℝ × Ω =>
        pairEnergy (commutatorKernel d s (gradient (E.test j))) (Y q)
          (HRS.Whole.withDensityReal (ρ q.1))) := by
    intro j
    exact fp81s21_moving_pairEnergy_process_joint_meas (d := d) (N := N)
      (ρ := ρ) (k := fun _ x y =>
        commutatorKernel d s (gradient (E.test j)) x y) hρm hρ0 (hk j) hY
  have hIntegral : ∀ j, Measurable (fun u : ℝ =>
      ∫ ω : Ω, pairEnergy (commutatorKernel d s (gradient (E.test j))) (Y (u, ω))
        (HRS.Whole.withDensityReal (ρ u)) ∂P) := by
    intro j
    exact fp81s21_moving_total_integral_meas_bigU (hPairY j)
  have hTest : ∀ j, IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) (E.test j) := by
    intro j
    exact weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth hchartP (E.test_smooth j))
  have hc : ∀ j, Measurable (fun q : ℝ × EucConfig d N => T q (E.test j)) := by
    intro j
    have hformula : (fun q : ℝ × EucConfig d N => Tactual q (E.test j)) =
        (fun q => (N : ℝ) *
            pairEnergy (commutatorKernel d s (gradient (E.test j))) q.2
              (HRS.Whole.withDensityReal (ρ q.1)) -
          (N : ℝ) * ∫ ω : Ω,
            pairEnergy (commutatorKernel d s (gradient (E.test j))) (Y (q.1, ω))
              (HRS.Whole.withDensityReal (ρ q.1)) ∂P) := by
      funext q
      dsimp [Tactual, HRS.Whole.r2CommDistr]
      rw [integral_const_mul]
    have hteq : (fun q : ℝ × EucConfig d N => T q (E.test j)) =
        (fun q => Tactual q (E.test j)) := by
      funext q
      exact hT_eq q.1 q.2 (E.test j) (hTest j)
    rw [hteq, hformula]
    exact (measurable_const.mul (hPair j)).sub
      (measurable_const.mul ((hIntegral j).comp measurable_fst))
  obtain ⟨q, hq, hqrep⟩ := fp81s21_measurable_riesz hchartP E T
    (fun a => (hZraw a).1) hc
  refine ⟨c₁, hc₁, fun u X => q (u, X), ?_, ?_, ?_⟩
  · change Measurable (fun p : ℝ × EucConfig d N => q p)
    exact hq
  · intro u X
    rcases hqrep (u, X) with ⟨haction, hcoord, hnorm⟩
    have hdual : dualNormE (2 * d + 8) ((d : ℝ) + 2)
        (fun f => Tactual (u, X) f) =
        dualNormE (2 * d + 8) ((d : ℝ) + 2) (T (u, X)) := by
      unfold dualNormE
      apply le_antisymm
      · refine iSup_le fun f => iSup_le fun hf => ?_
        have hwt : IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f :=
          weightedTestSubmodule_iff.1
            (weighted_test_of_compact_smooth hchartP ⟨hf.1, hf.2.1⟩)
        change ENNReal.ofReal |Tactual (u, X) f| /
          weightedSobolevE (2 * d + 8) ((d : ℝ) + 2) f ≤ _
        rw [← hT_eq u X f hwt]
        exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
      · refine iSup_le fun f => iSup_le fun hf => ?_
        have hwt : IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f :=
          weightedTestSubmodule_iff.1
            (weighted_test_of_compact_smooth hchartP ⟨hf.1, hf.2.1⟩)
        change ENNReal.ofReal |T (u, X) f| /
          weightedSobolevE (2 * d + 8) ((d : ℝ) + 2) f ≤ _
        rw [hT_eq u X f hwt]
        exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
    refine ⟨?_, ?_, hdual.trans hnorm⟩
    · intro f hf
      have hwt : IsR2WeightedTest (2 * d + 8) ((d : ℝ) + 2) f :=
        weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hchartP hf)
      change fp81s21_chartAction E (q (u, X)) f = Tactual (u, X) f
      rw [← hT_eq u X f hwt]
      exact haction f hf
    · intro j
      change q (u, X) j = Tactual (u, X) (E.test j)
      rw [← hT_eq u X (E.test j) (hTest j)]
      exact hcoord j
  · intro u X f hf
    exact (hZraw (u, X)).2 f hf

#print axioms HRS.Fp81.S21.fp81s21_moving_pairEnergy_process_joint_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_density_integral_meas_bigU
#print axioms HRS.Fp81.S21.fp81s21_moving_total_integral_meas_bigU
#print axioms HRS.Fp81.S21.fp81s21_quad_config_rep

end HRS.Fp81.S21

end
