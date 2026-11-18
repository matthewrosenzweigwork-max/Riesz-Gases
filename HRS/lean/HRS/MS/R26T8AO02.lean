import HRS.MS.R26T8AO02f
import HRS.MS.R26T8AA06

/-!
# S8.2 T8A O02: `r26t8a_normal_local_bound` (Pro contract, verbatim)
`B = C A`-linear pointwise bounds of the pair and error statistics (O02e) by the `A`-free pole envelope (O02b, c),
the envelope is bounded on `K` (O02a) and integrable against the Gibbs law (G00/`u4_env_L2`), which bounds the centring
constants; the linear row term is bounded by `aSource ≤ Ca A` (O02d).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

set_option maxHeartbeats 12800000 in
theorem r26t8a_normal_local_bound (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (K : Set (EucConfig d N)) (hK : IsCompact K) (hKD : K ⊆ (eucCollisionSet d N)ᶜ) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      (∀ ell ≤ 2, ∀ X ∈ K, ‖iteratedFDeriv ℝ ell (r26t8a_correctedQ a beta Psi f) X‖ ≤ CK * A) ∧
      (∀ X ∈ K, |r26t8a_correctedD a beta rho Psi f X| ≤ CK * A) := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := HRS.MS.S82W.w_mu_prob hd ha hbeta hrho
  set P := canonicalP d N a beta with hPdef
  obtain ⟨K1, Cb, M', hK10, hCb0, hMM', hSt⟩ := r26t8a_o02_stat_bounds hd a beta M ha hbeta hM hrho
  have hM'0 : 0 ≤ M' := le_trans hM hMM'
  obtain ⟨Cg, p, q, hCg, hp, hq, hG⟩ := r26t8a_o02_tame (N := N) hd hM hM'0
  obtain ⟨S, hS⟩ := r26t8a_o02_env_sup (N := N) p q K hK hKD
  obtain ⟨Ca, hCa0, hCa⟩ := r26t8a_o02_aSource_bound hd ha hbeta hrho
  -- integrability of the envelope
  have hEm := u4_Env_meas (d := d) (N := N) p q
  have hEint : Integrable (u4Env (d := d) (N := N) p q) P := by
    refine Integrable.mono' (u4_env_L2 hd hN0 ha hbeta hp hq) hEm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    have h1 := u4Env_ge_one (d := d) (N := N) hp (q := q) X
    rw [Real.norm_of_nonneg (by linarith)]
    nlinarith
  set I : ℝ := ∫ X, u4Env (d := d) (N := N) p q X ∂P with hI
  have hI0 : 0 ≤ I := integral_nonneg fun X => by
    show 0 ≤ u4Env (d := d) (N := N) p q X
    linarith [u4Env_ge_one (d := d) (N := N) hp (q := q) X]
  have hae0 : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  set S' : ℝ := max S 0 with hS'
  have hS'0 : 0 ≤ S' := le_max_right _ _
  have hSK : ∀ X ∈ K, u4Env (d := d) (N := N) p q X ≤ S' := fun X hX => (hS X hX).trans (le_max_left _ _)
  set k3 : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hk3
  set k5 : ℝ := (N : ℝ) ^ (-(5 / 2 : ℝ)) with hk5
  have hk30 : 0 ≤ k3 := Real.rpow_nonneg hNpos.le _
  have hk50 : 0 ≤ k5 := Real.rpow_nonneg hNpos.le _
  set E1 : ℝ := (2 / (N : ℝ)) * k3 + k5 * K1 + k5 * Cb with hE1
  have hE10 : 0 ≤ E1 := by positivity
  refine ⟨5 * k3 * C * Cg * (S' + I) + C * E1 * Cg * (S' + I) + 4 * Ca, by positivity, ?_⟩
  intro f A hA hTB
  have hB : 0 ≤ C * A := mul_nonneg hC hA
  have hQ := hPsi.corrector f A hA hTB
  have hUne : ∀ X : EucConfig d N, 0 ≤ u4Env (d := d) (N := N) p q X := fun X => by
    linarith [u4Env_ge_one (d := d) (N := N) hp (q := q) X]
  -- pointwise bounds by the envelope
  have hpsX : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |pairStatistic (Psi f) X| ≤ 5 * k3 * (C * A) * (Cg * u4Env (d := d) (N := N) p q X) := by
    intro X hX
    have h1 := (hSt f (C * A) hB (Psi f) hQ N X hX).1
    have h2 := (r26t8a_o02_each_le (hG X hX)).1
    refine h1.trans ?_
    have : 0 ≤ 5 * k3 * (C * A) := by positivity
    calc 5 * k3 * ((C * A) * r26t8a_o02_Wb M X) = 5 * k3 * (C * A) * r26t8a_o02_Wb M X := by ring
      _ ≤ 5 * k3 * (C * A) * (Cg * u4Env (d := d) (N := N) p q X) := mul_le_mul_of_nonneg_left h2 this
  have herrX : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |errorStatistic (critCoeff d a beta rho) rho (Psi f) X| ≤ (C * A) * (E1 * (Cg * u4Env (d := d) (N := N) p q X)) := by
    intro X hX
    have h1 := (hSt f (C * A) hB (Psi f) hQ N X hX).2
    obtain ⟨w1, w2, w3⟩ := r26t8a_o02_each_le (hG X hX)
    obtain ⟨n1, n2, n3⟩ := r26t8a_o02_nonneg (d := d) (N := N) M M' X
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB
    have hc1 : 0 ≤ (2 / (N : ℝ)) * k3 := by positivity
    calc (2 / (N : ℝ)) * k3 * r26t8a_o02_Wb M X + k5 * (K1 * r26t8a_o02_Tr M' X + Cb * r26t8a_o02_Pj M' X)
        ≤ (2 / (N : ℝ)) * k3 * (Cg * u4Env (d := d) (N := N) p q X) +
            k5 * (K1 * (Cg * u4Env (d := d) (N := N) p q X) + Cb * (Cg * u4Env (d := d) (N := N) p q X)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left w1 hc1) (mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left w3 hK10) (mul_le_mul_of_nonneg_left w2 hCb0)) hk50)
      _ = E1 * (Cg * u4Env (d := d) (N := N) p q X) := by rw [hE1]; ring
  -- the means
  have hmeanQ : |∫ Y, pairStatistic (Psi f) Y ∂P| ≤ 5 * k3 * (C * A) * (Cg * I) := by
    have hint : Integrable (fun Y : EucConfig d N => 5 * k3 * (C * A) * (Cg * u4Env (d := d) (N := N) p q Y)) P :=
      (hEint.const_mul Cg).const_mul _
    have := norm_integral_le_of_norm_le hint (by
      filter_upwards [hae0] with X hX
      rw [Real.norm_eq_abs]; exact hpsX X hX)
    rw [Real.norm_eq_abs, integral_const_mul, integral_const_mul] at this
    exact this
  have hmeanD : |∫ Y, errorStatistic (critCoeff d a beta rho) rho (Psi f) Y ∂P| ≤ (C * A) * (E1 * (Cg * I)) := by
    have hint : Integrable (fun Y : EucConfig d N => (C * A) * (E1 * (Cg * u4Env (d := d) (N := N) p q Y))) P :=
      ((hEint.const_mul Cg).const_mul _).const_mul _
    have := norm_integral_le_of_norm_le hint (by
      filter_upwards [hae0] with X hX
      rw [Real.norm_eq_abs]; exact herrX X hX)
    rw [Real.norm_eq_abs, integral_const_mul, integral_const_mul, integral_const_mul] at this
    exact this
  -- jets of the corrected pair statistic
  have hcQ : r26t8a_correctedQ (N := N) a beta Psi f =
      fun X => pairStatistic (Psi f) X - ∫ Y, pairStatistic (Psi f) Y ∂P := rfl
  obtain ⟨-, hjet⟩ := w_pairstat_jets (N := N) hd hQ hB (∫ Y, pairStatistic (Psi f) Y ∂P)
  have hbQ : ∀ X ∈ K, |pairStatistic (Psi f) X - ∫ Y, pairStatistic (Psi f) Y ∂P| +
      ‖fderiv ℝ (fun Y => pairStatistic (Psi f) Y - ∫ Z, pairStatistic (Psi f) Z ∂P) X‖ +
      ‖iteratedFDeriv ℝ 2 (fun Y => pairStatistic (Psi f) Y - ∫ Z, pairStatistic (Psi f) Z ∂P) X‖ ≤
      (5 * k3 * C * Cg * (S' + I)) * A := by
    intro X hX
    have hXc : X ∉ eucCollisionSet d N := hKD hX
    refine (hjet X hXc).trans ?_
    have hsw : ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M (C * A) i j X = (C * A) * r26t8a_o02_Wb M X := by
      unfold r26t8a_o02_Wb
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => r26t8a_o02_wBq_lin M (C * A) i j X
    rw [hsw]
    have hw := (r26t8a_o02_each_le (hG X hXc)).1
    have hUS := hSK X hX
    have hWS : r26t8a_o02_Wb M X ≤ Cg * S' := hw.trans (mul_le_mul_of_nonneg_left hUS hCg)
    have h1 : 5 * k3 * ((C * A) * r26t8a_o02_Wb M X) ≤ 5 * k3 * ((C * A) * (Cg * S')) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWS hB) (by positivity)
    have h2 := hmeanQ
    nlinarith [h1, h2]
  have hQjets : ∀ ell ≤ 2, ∀ X ∈ K, ‖iteratedFDeriv ℝ ell (r26t8a_correctedQ a beta Psi f) X‖ ≤
      (5 * k3 * C * Cg * (S' + I) + C * E1 * Cg * (S' + I) + 4 * Ca) * A := by
    intro ell hell X hX
    rw [hcQ]
    have hb := hbQ X hX
    have n1 := norm_nonneg (fderiv ℝ (fun Y => pairStatistic (Psi f) Y - ∫ Z, pairStatistic (Psi f) Z ∂P) X)
    have n2 := norm_nonneg (iteratedFDeriv ℝ 2 (fun Y => pairStatistic (Psi f) Y - ∫ Z, pairStatistic (Psi f) Z ∂P) X)
    have n0 := abs_nonneg (pairStatistic (Psi f) X - ∫ Y, pairStatistic (Psi f) Y ∂P)
    have extra : 0 ≤ (C * E1 * Cg * (S' + I) + 4 * Ca) * A := by positivity
    have hlow : ‖iteratedFDeriv ℝ ell (fun Y => pairStatistic (Psi f) Y - ∫ Z, pairStatistic (Psi f) Z ∂P) X‖ ≤
        (5 * k3 * C * Cg * (S' + I)) * A := by
      interval_cases ell
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; linarith
      · rw [norm_iteratedFDeriv_one]; linarith
      · linarith
    nlinarith
  -- the corrected error
  have hDb : ∀ X ∈ K, |r26t8a_correctedD a beta rho Psi f X| ≤
      (5 * k3 * C * Cg * (S' + I) + C * E1 * Cg * (S' + I) + 4 * Ca) * A := by
    intro X hX
    have hXc : X ∉ eucCollisionSet d N := hKD hX
    have hUS := hSK X hX
    have e1 : |errorStatistic (critCoeff d a beta rho) rho (Psi f) X -
        ∫ Y, errorStatistic (critCoeff d a beta rho) rho (Psi f) Y ∂P| ≤ (C * E1 * Cg * (S' + I)) * A := by
      refine (abs_sub _ _).trans ?_
      have h1 := herrX X hXc
      have h2 : (C * A) * (E1 * (Cg * u4Env (d := d) (N := N) p q X)) ≤ (C * A) * (E1 * (Cg * S')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUS hCg) hE10) hB
      have h3 := hmeanD
      nlinarith [h1, h2, h3]
    set g : Euc d → ℝ := aSource (HRS.Whole.withDensityReal rho) f with hg
    have hgb : ∀ x, |g x| ≤ Ca * A := fun x => hCa f A hA hTB x
    have hCaA : 0 ≤ Ca * A := mul_nonneg hCa0 hA
    set Gz : EucConfig d N → ℝ := fun Y => (1 / (N : ℝ)) * ∑ i, g (Y i) with hGz
    have hGzb : ∀ Y, |Gz Y| ≤ Ca * A := by
      intro Y
      simp only [hGz]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
      have : |∑ i, g (Y i)| ≤ (N : ℝ) * (Ca * A) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |g (Y i)| ≤ ∑ _i : Fin N, Ca * A := Finset.sum_le_sum fun i _ => hgb (Y i)
          _ = (N : ℝ) * (Ca * A) := by simp
      calc 1 / (N : ℝ) * |∑ i, g (Y i)| ≤ 1 / (N : ℝ) * ((N : ℝ) * (Ca * A)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Ca * A := by field_simp
    have hGzm : |∫ Y, Gz Y ∂P| ≤ Ca * A := by
      have := norm_integral_le_of_norm_le (integrable_const (Ca * A)) (μ := P)
        (f := Gz) (Filter.Eventually.of_forall fun Y => by rw [Real.norm_eq_abs]; exact hGzb Y)
      rw [integral_const, Real.norm_eq_abs] at this
      simpa using this
    have hsq0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    have hsq1 : 1 ≤ Real.sqrt N := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hN0)
    have hz : |zetaActual (N := N) a beta g X| ≤ Real.sqrt N * (2 * (Ca * A)) := by
      have e : zetaActual (N := N) a beta g X = Real.sqrt N * (Gz X - ∫ Y, Gz Y ∂P) := rfl
      rw [e, abs_mul, abs_of_nonneg hsq0]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hsq0
      linarith [hGzb X, hGzm]
    have hz2 : |(2 / (N : ℝ)) * zetaActual (N := N) a beta g X| ≤ 4 * Ca * A := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (N : ℝ))]
      have hsn : Real.sqrt N ≤ N := by nlinarith
      calc 2 / (N : ℝ) * |zetaActual (N := N) a beta g X| ≤ 2 / (N : ℝ) * (Real.sqrt N * (2 * (Ca * A))) :=
            mul_le_mul_of_nonneg_left hz (by positivity)
        _ ≤ 2 / (N : ℝ) * ((N : ℝ) * (2 * (Ca * A))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsn (by positivity)) (by positivity)
        _ = 4 * Ca * A := by field_simp; ring
    have hD : r26t8a_correctedD a beta rho Psi f X =
        (errorStatistic (critCoeff d a beta rho) rho (Psi f) X -
          ∫ Y, errorStatistic (critCoeff d a beta rho) rho (Psi f) Y ∂P) -
          (2 / (N : ℝ)) * zetaActual (N := N) a beta g X := rfl
    rw [hD]
    refine (abs_sub _ _).trans ?_
    have hpos : 0 ≤ (5 * k3 * C * Cg * (S' + I)) * A := by positivity
    nlinarith [e1, hz2, hpos]
  exact ⟨hQjets, hDb⟩

end HRS.MS.R26T8A
