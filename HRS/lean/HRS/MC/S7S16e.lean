import HRS.MC.Sec7Vocab
import HRS.MC.SEdgeB14
import HRS.MC.SEdgeS16aAux4
import HRS.MC.S7S16d

/-!
# Packet `s7_S16e_edge_two_observables`: `O(N^{-1/2})` for observables of the mode pair

`static_edge` (`HRS.MC.SEdge.B14.static_edge_assembly_proof`) with `rho = 1`, `p = 2`, the two real modes at
`k, -k`, gives that `sqrt N (E w(W_N) - E w(Z))` converges, hence is bounded; `W_N = pi eta_N` (Haar centring,
`s16a_centering`, `s16a_coord_eta`) and `pi_* G = N(0, C)` (`IsGaussian.ext`, as in `S16aAux4`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16e

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.S16a HRS.MC.Sec7

variable {d : ℕ}

/-- the two test functions `cos, sin` at `k` and `-k` -/
def s7e_phi (k : NonzeroLattice d) : Fin 2 → Torus d → ℝ :=
  fun a => if a = 0 then Torus.realMode k else Torus.realMode (s7_neg k)

theorem s7e_phi_smooth (k : NonzeroLattice d) (a : Fin 2) : Torus.IsSmooth (s7e_phi k a) := by
  unfold s7e_phi
  split_ifs
  · exact StaticLimitAux.isSmooth_realMode' _
  · exact StaticLimitAux.isSmooth_realMode' _

theorem s7e_modePair_eq_eval {m : ℝ} (k : NonzeroLattice d) (u : NegSobolev d m) (a : Fin 2) :
    s7_modePair m k u a = NegSobolev.eval u (s7e_phi k a) := by
  fin_cases a
  · simp only [s7_modePair, s7e_phi]
    simp [s16a_eval_realMode]
  · simp only [s7_modePair, s7e_phi]
    simp [s16a_eval_realMode]

section Law

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
include hd hs0 hs hβ

/-- Law of a coefficient vector under `G`, for an arbitrary finite family of smooth tests. -/
theorem s7e_law_G {m : ℝ} (G : Measure (NegSobolev d m)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (volume : Measure (Torus d)) β ψ x
        ∂(volume : Measure (Torus d)))
    {p : ℕ} (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (W : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hWa : ∀ (u : NegSobolev d m) (a : Fin p), W u a = NegSobolev.eval u (φ a)) :
    G.map W = multivariateGaussian 0 (sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) φ) := by
  classical
  haveI : IsGaussian G := hG.1.1
  set C := sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) φ with hC
  have hpsd : C.PosSemidef :=
    HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ (s16a_smoothPos (d := d)) hφ
  have hWm : Measurable W := W.continuous.measurable
  have hint : ∀ a b : Fin p, Integrable (fun u => W u a * W u b) G := by
    intro a b
    have hLa : ∀ c : Fin p, MemLp (fun u => W u c) 2 G := by
      intro c
      have : (fun u => W u c) = ⇑((EuclideanSpace.proj c : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp W) := by
        funext u; rfl
      rw [this]
      exact IsGaussian.memLp_dual G _ 2 (by simp)
    exact (hLa a).integrable_mul (hLa b)
  have hcov : ∀ a b : Fin p, ∫ u, W u a * W u b ∂G = C a b := by
    intro a b
    simp_rw [hWa]
    rw [hG.2 _ _ (hφ a) (hφ b)]
    exact (s16a_Cmat_eq hd hs0 hs hβ (hφ b)).symm
  haveI : IsGaussian (G.map W) := inferInstance
  haveI : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C) := inferInstance
  have hmean : ∫ z, id z ∂(G.map W) = 0 := by
    set m0 : EuclideanSpace ℝ (Fin p) := ∫ z, id z ∂(G.map W) with hm0
    have h1 : inner ℝ m0 m0 = ∫ z, inner ℝ m0 (id z) ∂(G.map W) := by
      rw [integral_inner IsGaussian.integrable_id]
    rw [integral_map hWm.aemeasurable (by fun_prop)] at h1
    have h2 : ∫ u, inner ℝ m0 (id (W u)) ∂G =
        ∫ u, ((innerSL ℝ m0).comp W) u ∂G := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp
    rw [h2, hG.1.2 ((innerSL ℝ m0).comp W)] at h1
    exact inner_self_eq_zero.1 h1
  refine IsGaussian.ext ?_ ?_
  · rw [hmean]
    simp
  · ext x y
    rw [covarianceBilin_multivariateGaussian hpsd]
    rw [covarianceBilin_apply IsGaussian.memLp_two_id, hmean]
    simp only [id, sub_zero]
    rw [integral_map hWm.aemeasurable (by fun_prop)]
    have hexp : ∀ u, inner ℝ x (W u) * inner ℝ y (W u) =
        ∑ a, ∑ b, (x a * y b) * (W u a * W u b) := by
      intro u
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hexp]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _]
    simp_rw [integral_finsetSum _ fun b _ => (hint _ b).const_mul _, integral_const_mul, hcov]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- `W_N = pi eta_N` -/
theorem s7e_centered_eq {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N)
    (k : NonzeroLattice d) (X : Config d N) :
    centeredStat (s16aQ d s N β) (s7e_phi k) X = s7_modePair m k (etaE m X (volume : Measure (Torus d))) := by
  have hc : ∀ a, ∫ Y, pair (empirical Y) (s7e_phi k a) ∂(s16aQ d s N β) = 0 := by
    intro a
    unfold s7e_phi
    split_ifs
    · exact s16a_centering hd hs0 hs hβ hN k
    · exact s16a_centering hd hs0 hs hβ hN (s7_neg k)
  have hco : ∀ j : NonzeroLattice d, NegSobolev.fourierCoeff (etaE m X (volume : Measure (Torus d))) j =
      Real.sqrt N * pair (empirical X) (Torus.realMode j) := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [s16a_coord_eta hm hN]
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
    simp
  ext a
  fin_cases a
  · have h0 := hc 0
    simp only [s7e_phi, ite_true] at h0
    simp only [centeredStat, s7_modePair, s7e_phi]
    simp [h0, hco]
  · have h1 : ∫ Y, pair (empirical Y) (Torus.realMode (s7_neg k)) ∂(s16aQ d s N β) = 0 :=
      s16a_centering hd hs0 hs hβ hN (s7_neg k)
    simp only [centeredStat, s7_modePair, s7e_phi]
    simp [h1, hco]

end Law


/-- a convergent `sqrt N`-scaled remainder gives an `O(N^{-1/2})` bound -/
theorem s7e_bdd (E : ℕ → ℝ) (Z A : ℝ)
    (h : Tendsto (fun N : ℕ => Real.sqrt N * (E N - Z - (1 / (6 * Real.sqrt N)) * A)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |E N - Z| ≤ C / Real.sqrt N := by
  obtain ⟨B, hB⟩ := (h.norm).bddAbove_range
  refine ⟨B + |A| / 6, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hB' : |Real.sqrt N * (E N - Z - (1 / (6 * Real.sqrt N)) * A)| ≤ B := by
    have := hB ⟨N, rfl⟩
    simpa [Real.norm_eq_abs] using this
  have hid : E N - Z = (Real.sqrt N * (E N - Z - (1 / (6 * Real.sqrt N)) * A) + A / 6) / Real.sqrt N := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hs]
  refine div_le_div_of_nonneg_right ?_ hs.le
  calc _ ≤ |Real.sqrt N * (E N - Z - (1 / (6 * Real.sqrt N)) * A)| + |A / 6| := abs_add_le _ _
    _ ≤ B + |A| / 6 := by
      have : |A / 6| = |A| / 6 := by rw [abs_div]; norm_num
      linarith

theorem s7_S16e_edge_two_observables_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (G : Measure (NegSobolev d m))
    [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) volume β ψ x ∂volume)
    (k : NonzeroLattice d) {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : MemCb 5 w) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ X, w (s7_modePair m k (etaE m X volume)) ∂(modulatedGibbs (periodicRiesz d s) N β volume) -
        ∫ y, w (s7_modePair m k y) ∂G| ≤ C / Real.sqrt N := by
  have hβ0 : 0 ≤ β := hβ.le
  have hm' : (d : ℝ) < 2 * m := by linarith
  obtain ⟨π, hπ, -⟩ := HRS.MC.Sec7.S16d.s7_S16d_modePair_clm_proof d m k
  have hWa : ∀ (u : NegSobolev d m) (a : Fin 2), π u a = NegSobolev.eval u (s7e_phi k a) :=
    fun u a => by rw [hπ]; exact s7e_modePair_eq_eval k u a
  have hlaw : G.map π = multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
      ∫ x : Torus d, s7e_phi k a x * responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (s7e_phi k b) x ∂(volume : Measure (Torus d))) := by
    have := s7e_law_G hd hs0 hs hβ0 G hG (s7e_phi k) (s7e_phi_smooth k) π hWa
    rw [this]
    unfold sed_Cmat
    rw [s16a_wdr_one]
  have hedge := HRS.MC.SEdge.B14.static_edge_assembly_proof hd hs0 hs β hβ0
    (fun _ : Torus d => (1 : ℝ)) s16a_smoothPos 2 (s7e_phi k) (s7e_phi_smooth k) w hw
  dsimp only at hedge
  rw [s16a_wdr_one] at hedge
  have hwc : Continuous w := hw.1.continuous
  have hZ : ∫ y, w (s7_modePair m k y) ∂G =
      ∫ z, w z ∂(multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
      ∫ x : Torus d, s7e_phi k a x * responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (s7e_phi k b) x ∂(volume : Measure (Torus d)))) := by
    rw [← hlaw, integral_map π.continuous.measurable.aemeasurable hwc.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [hπ])
  have hE : ∀ N : ℕ, 1 ≤ N →
      ∫ X, w (s7_modePair m k (etaE m X volume)) ∂(modulatedGibbs (periodicRiesz d s) N β volume) =
      ∫ X, w (centeredStat (modulatedGibbs (periodicRiesz d s) N β volume) (s7e_phi k) X)
        ∂(modulatedGibbs (periodicRiesz d s) N β volume) := by
    intro N hN
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show w _ = w _
    rw [s7e_centered_eq hd hs0 hs hβ0 hm' hN k X]
  obtain ⟨C, hC⟩ := s7e_bdd
    (fun N => ∫ X, w (centeredStat (modulatedGibbs (periodicRiesz d s) N β volume) (s7e_phi k) X)
      ∂(modulatedGibbs (periodicRiesz d s) N β volume))
    (∫ z, w z ∂(multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
      ∫ x : Torus d, s7e_phi k a x * responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (s7e_phi k b) x ∂(volume : Measure (Torus d)))))
    (A := ∑ a, ∑ b, ∑ c,
        (∫ x : Torus d, responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (s7e_phi k a) x *
            responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (s7e_phi k b) x *
            responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (s7e_phi k c) x ∂volume) *
          ∫ z : EuclideanSpace ℝ (Fin 2), (iteratedFDeriv ℝ 3 w z) ![stdVec a, stdVec b, stdVec c] ∂(multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
      ∫ x : Torus d, s7e_phi k a x * responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (s7e_phi k b) x ∂(volume : Measure (Torus d)))))
    hedge
  refine ⟨C, fun N hN => ?_⟩
  rw [hE N hN, hZ]
  exact hC N hN

end HRS.MC.Sec7.S16e

end
