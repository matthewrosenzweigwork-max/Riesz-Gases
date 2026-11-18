import HRS.MS.R26T8AO03b12

/-!
# S8.2 T8A O03b (part 13): linear combinations of the corrected drift defect `D`
If `Q f = c₁ Q g + c₂ Q h` and the commutator source is the same combination (also after integration against `μ`),
then `D f = c₁ D g + c₂ D h` off collisions.  Proof: the identity `D = scalarForcing + L Q` reduces the claim to a
constant (the `L Q` part is linear since `Q` is `C²`, the `scalarForcing` part is linear up to an additive constant);
the constant vanishes since all three `D` have mean zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_D_lincomb (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {Af Ag Ah : ℝ} {f g h : Euc d → ℝ} (hf : TestBound (testOrder d) Af f) (hg : TestBound (testOrder d) Ag g)
    (hh : TestBound (testOrder d) Ah h) (c1 c2 : ℝ)
    (HQ : r26t8a_correctedQ (N := N) a beta Psi f =
      c1 • r26t8a_correctedQ (N := N) a beta Psi g + c2 • r26t8a_correctedQ (N := N) a beta Psi h)
    (Hh : ∀ x y, hSource f x y = c1 * hSource g x y + c2 * hSource h x y)
    (Hi : ∀ x, ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho) =
      c1 * ∫ y, hSource g x y ∂(HRS.Whole.withDensityReal rho) +
        c2 * ∫ y, hSource h x y ∂(HRS.Whole.withDensityReal rho))
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    r26t8a_correctedD (N := N) a beta rho Psi f X =
      c1 * r26t8a_correctedD (N := N) a beta rho Psi g X + c2 * r26t8a_correctedD (N := N) a beta rho Psi h X := by
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  set P := canonicalP d N a beta with hPdef
  set μ := HRS.Whole.withDensityReal rho with hμ
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hAf := r26t8a_o03b_tb_nonneg hk hf
  have hAg := r26t8a_o03b_tb_nonneg hk hg
  have hAh := r26t8a_o03b_tb_nonneg hk hh
  -- the scalar forcing combination is a constant
  set T : (Euc d → ℝ) → EucConfig d N → ℝ := fun u Y => centeredPairFunctional (hSource u) Y μ with hT
  set K3 : ℝ := (∫ x, ∫ y, hSource f x y ∂μ ∂μ) - c1 * (∫ x, ∫ y, hSource g x y ∂μ ∂μ) -
    c2 * (∫ x, ∫ y, hSource h x y ∂μ ∂μ) with hK3
  have hA : ∀ Y, T f Y - c1 * T g Y - c2 * T h Y = K3 := by
    intro Y
    have s1 : ∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (Y i) (Y j) =
        c1 * ∑ i, ∑ j ∈ Finset.univ.erase i, hSource g (Y i) (Y j) +
          c2 * ∑ i, ∑ j ∈ Finset.univ.erase i, hSource h (Y i) (Y j) := by
      simp only [Hh, Finset.sum_add_distrib, Finset.mul_sum]
    have s2 : ∑ i, ∫ y, hSource f (Y i) y ∂μ =
        c1 * ∑ i, ∫ y, hSource g (Y i) y ∂μ + c2 * ∑ i, ∫ y, hSource h (Y i) y ∂μ := by
      simp only [Hi, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [hT, centeredPairFunctional, hK3]
    rw [s1, s2]
    ring
  set SF : (Euc d → ℝ) → EucConfig d N → ℝ := fun u Z => scalarForcing a beta rho u Z with hSF
  have hSFeq : ∀ u Z, SF u Z = (Real.sqrt N / 2) * (T u Z - ∫ Y, T u Y ∂P) := fun u Z => rfl
  set K : ℝ := (Real.sqrt N / 2) * (K3 - ((∫ Y, T f Y ∂P) - c1 * ∫ Y, T g Y ∂P - c2 * ∫ Y, T h Y ∂P)) with hK
  have hSFc : ∀ Z, SF f Z - c1 * SF g Z - c2 * SF h Z = K := by
    intro Z
    rw [hSFeq, hSFeq, hSFeq, hK, ← hA Z]
    ring
  -- the generator part
  have hpG : ∀ Z : EucConfig d N, Z ∉ eucCollisionSet d N →
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (r26t8a_correctedQ (N := N) a beta Psi f) Z =
      c1 * particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (r26t8a_correctedQ (N := N) a beta Psi g) Z +
        c2 * particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
          (r26t8a_correctedQ (N := N) a beta Psi h) Z := fun Z hZ =>
    r26t8a_o03b_pG_lin _ (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hg hZ)
      (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hh hZ) c1 c2 HQ
  -- pointwise relation off collisions
  have hrel : ∀ Z : EucConfig d N, Z ∉ eucCollisionSet d N →
      r26t8a_correctedD (N := N) a beta rho Psi f Z - c1 * r26t8a_correctedD (N := N) a beta rho Psi g Z -
        c2 * r26t8a_correctedD (N := N) a beta rho Psi h Z = K := by
    intro Z hZ
    have e1 := hPsi.identity N hN f Af hAf hf Z hZ
    have e2 := hPsi.identity N hN g Ag hAg hg Z hZ
    have e3 := hPsi.identity N hN h Ah hAh hh Z hZ
    have := hSFc Z
    have hp := hpG Z hZ
    simp only [hSF] at this
    have d1 : r26t8a_correctedD (N := N) a beta rho Psi f Z = scalarForcing a beta rho f Z +
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (r26t8a_correctedQ (N := N) a beta Psi f) Z := by
      linarith
    have d2 : r26t8a_correctedD (N := N) a beta rho Psi g Z = scalarForcing a beta rho g Z +
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (r26t8a_correctedQ (N := N) a beta Psi g) Z := by
      linarith
    have d3 : r26t8a_correctedD (N := N) a beta rho Psi h Z = scalarForcing a beta rho h Z +
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (r26t8a_correctedQ (N := N) a beta Psi h) Z := by
      linarith
    rw [d1, d2, d3, hp]
    linarith
  -- the constant vanishes
  have hDint : ∀ {A' : ℝ} {u : Euc d → ℝ}, TestBound (testOrder d) A' u →
      Integrable (r26t8a_correctedD (N := N) a beta rho Psi u) P := fun {A' u} hu =>
    (hPsi.bound N hN u A' (r26t8a_o03b_tb_nonneg hk hu) hu).1.integrable one_le_two
  have hae0 : ∀ᵐ Z ∂P, Z ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  have hint1 : ∫ Z, (r26t8a_correctedD (N := N) a beta rho Psi f Z - c1 * r26t8a_correctedD (N := N) a beta rho Psi g Z -
      c2 * r26t8a_correctedD (N := N) a beta rho Psi h Z) ∂P = K := by
    rw [integral_congr_ae (g := fun _ => K) (by filter_upwards [hae0] with Z hZ using hrel Z hZ)]
    simp
  have hint2 : ∫ Z, (r26t8a_correctedD (N := N) a beta rho Psi f Z - c1 * r26t8a_correctedD (N := N) a beta rho Psi g Z -
      c2 * r26t8a_correctedD (N := N) a beta rho Psi h Z) ∂P = 0 := by
    have i12 : Integrable (fun Z => r26t8a_correctedD (N := N) a beta rho Psi f Z -
        c1 * r26t8a_correctedD (N := N) a beta rho Psi g Z) P := (hDint hf).sub ((hDint hg).const_mul c1)
    have i3 : Integrable (fun Z => c2 * r26t8a_correctedD (N := N) a beta rho Psi h Z) P :=
      (hDint hh).const_mul c2
    have i2 : Integrable (fun Z => c1 * r26t8a_correctedD (N := N) a beta rho Psi g Z) P :=
      (hDint hg).const_mul c1
    rw [integral_sub i12 i3, integral_sub (hDint hf) i2, integral_const_mul, integral_const_mul,
      r26t8a_o03b_D_mean_zero N hd hN a beta M C ha hbeta rho hrho Psi hPsi hf,
      r26t8a_o03b_D_mean_zero N hd hN a beta M C ha hbeta rho hrho Psi hPsi hg,
      r26t8a_o03b_D_mean_zero N hd hN a beta M C ha hbeta rho hrho Psi hPsi hh]
    simp
  have hK0 : K = 0 := by rw [← hint1, hint2]
  have := hrel X hX
  rw [hK0] at this
  linarith

end HRS.MS.R26T8A
