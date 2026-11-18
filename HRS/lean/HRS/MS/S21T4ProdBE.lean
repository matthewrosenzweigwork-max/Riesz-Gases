import HRS.MS.S21T4ProdBD

/-!
# R26-T3.S13: finite families of finite-rank quadratic statistics

The varying-configuration-space Cramér-Wold theorem turns the single-kernel
joint CLT into the joint CLT for any finite family sharing a finite collection
of smooth compactly supported test functions. The limit lives on the original
ProductGaussian probability space.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_family_joint_one_space
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ)) :
          EuclideanSpace ℝ (Fin (n + m)))) atTop
      (fun ω : I.Ω =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => I.η (f i) ω)
          (fun k : Fin m => (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
            c k a b * (I.η (u a) ω * I.η (u b) ω -
              HRS.Whole.pair μ (fun x => u a x * u b x)))) :
          EuclideanSpace ℝ (Fin (n + m))))
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  letI := I.mΩ
  letI := I.prob
  let X : (N : ℕ) → EucConfig d N → EuclideanSpace ℝ (Fin (n + m)) :=
    fun N v => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => r2EmpDistr μ v (f i))
      (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) v μ))
  let Z : I.Ω → EuclideanSpace ℝ (Fin (n + m)) :=
    fun ω => WithLp.toLp 2 (Fin.append
      (fun i : Fin n => I.η (f i) ω)
      (fun k : Fin m => (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
        c k a b * (I.η (u a) ω * I.η (u b) ω -
          HRS.Whole.pair μ (fun x => u a x * u b x))))
  change TendstoInDistribution X atTop Z
    (fun N => Measure.pi fun _ : Fin N => μ) I.P
  refine s21t4_varying_cramer_wold
    (fun N => s21t4_finite_family_source_ae I f hf c u hu hc N)
    (s21t4_finite_family_limit_ae I f hf c u hu hc) ?_
  intro t
  let α : Fin m → ℝ := fun k => t (Fin.natAdd n k)
  let cstar : Fin r → Fin r → ℝ := fun a b => ∑ k : Fin m, α k * c k a b
  have hdata : IsR2FiniteRankData cstar u :=
    s21t4_finite_rank_matrix_combination c u hu hc α
  have hb := s21t4_finite_rank_joint_one_space I f hf cstar u hdata
  let G : ((Fin n → ℝ) × ℝ) → ℝ :=
    fun v => (∑ i : Fin n, t (Fin.castAdd m i) * v.1 i) + v.2
  have hG : Continuous G := by
    refine (continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp continuous_fst)).add continuous_snd
  have hproj := hb.continuous_comp hG
  have hXproj : ∀ N (v : EucConfig d N),
      inner ℝ (X N v) t =
      G ((fun i : Fin n => r2EmpDistr μ v (f i)),
        (N : ℝ) * pairEnergy (r2FiniteRankKernel cstar u) v μ) := by
    intro N v
    exact s21t4_finite_family_particle_projection f c u hu hc v t
  have hZproj : ∀ ω : I.Ω,
      inner ℝ (Z ω) t =
      G ((fun i : Fin n => I.η (f i) ω),
        (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
          cstar a b * (I.η (u a) ω * I.η (u b) ω -
            HRS.Whole.pair μ (fun x => u a x * u b x))) := by
    intro ω
    exact s21t4_finite_family_limit_projection I f c u ω t
  convert hproj using 1
  · funext N v
    exact hXproj N v
  · funext ω
    exact hZproj ω

end HRS.MS.R26T3
