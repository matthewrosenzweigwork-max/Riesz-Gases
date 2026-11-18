import HRS.MS.GenPathAux20

/-!
# S5.6 packet P5c: the `𝒦`-valued particle martingale and its covariation

`s56_hsCov_eq`: `hsCovForm` of the clamped integrand is the feature form `featureForm m T q (Γ_·(r)) μ_N^r`.
`s56_particle_martingale`: existence of the `𝒦`-valued Itô integral `M` of `s56Phi` (copy of `gf_particle_martingale_proof`)
with covariation density `r ↦ featureForm m T q (Γ_·(clamp r)) (μ_N^r)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_hsCov_eq (m T q : ℝ) (hq : 0 ≤ q) (C : WholeCoeff d) {N : ℕ} (hN : 1 ≤ N) (r : ℝ)
    (x : EucConfig d N) (u v : KSpace d m T) :
    hsCovForm (fun k : Fin N × Fin d =>
        Real.sqrt (2 * q / N) • gradFeature C m T k.2 (mrrClamp T r) (x k.1)) u v =
      featureForm m T q (fun a => gradFeature C m T a (mrrClamp T r)) (HRS.Whole.empirical x) u v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable fun k : Fin N × Fin d =>
      ‖Real.sqrt (2 * q / N) • gradFeature C m T k.2 (mrrClamp T r) (x k.1)‖ ^ 2 := Summable.of_finite
  rw [hsCovForm_apply hsum]
  unfold featureForm
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hint : ∫ y, inner ℝ (gradFeature C m T a (mrrClamp T r) y) u *
      inner ℝ (gradFeature C m T a (mrrClamp T r) y) v ∂(HRS.Whole.empirical x) =
      (N : ℝ)⁻¹ * ∑ i, inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) u *
        inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) v :=
    HRS.Whole.pair_empirical hN (x) (fun y => inner ℝ (gradFeature C m T a (mrrClamp T r) y) u *
      inner ℝ (gradFeature C m T a (mrrClamp T r) y) v)
  rw [hint, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, conj_trivial]
  have h2 : Real.sqrt (2 * q / N) * Real.sqrt (2 * q / N) = 2 * q / N :=
    Real.mul_self_sqrt (by positivity)
  calc Real.sqrt (2 * q / N) * inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) u *
        (Real.sqrt (2 * q / N) * inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) v)
      = (Real.sqrt (2 * q / N) * Real.sqrt (2 * q / N)) *
        (inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) u *
          inner ℝ (gradFeature C m T a (mrrClamp T r) (x i)) v) := by ring
    _ = _ := by rw [h2]; field_simp

theorem s56_particle_martingale (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (q : ℝ) (hq : 0 ≤ q)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hB : IsBrownianFiltration P ℱ W') (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    ∃ M : ℝ → Ω → KSpace d b.m b.T,
      IsHilbertItoIntegral P ℱ W' (s56Phi (S.coeff N) b.m b.T q X) M ∧
      IsHilbertMartingaleWithCovariation P ℱ b.T M (fun r ζ => hsCovForm (s56Phi (S.coeff N) b.m b.T q X r ζ)) := by
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hB
  have hZ := fun τ => s56_phi_isHS b hbv S N hC q P ℱ X hprog τ
  obtain ⟨Mart, hc, had, hz, hJ⟩ := HRS.GF.gfb3_exists_hilbert_version hW hZ
  refine ⟨Mart, ⟨hc, had, hz, ?_⟩, ?_⟩
  · intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  · have hM := HRS.Uniform.Q07c.isHM_of_ito hW hZ hc had hz hJ b.T
    exact hM

end HRS.MS.GenPath
