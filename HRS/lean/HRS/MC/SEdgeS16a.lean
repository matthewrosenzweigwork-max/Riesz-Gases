import HRS.MC.SEdgeS16aAux4

/-!
# Packet S16A: `sed_S16a_field_clt_proof` (leading field CLT in `E_m`, every `m > d/2`, Haar background)

Plan (all steps proved in this file and `SEdgeS16aAux1..4.lean`):
1. (Aux1) Abstract criterion: probability measures `nu_n`, `G` on `E_m = ell^2` with (i) uniform coordinate tails
   `int coord_k^2 d nu_n <= w k`, `w` summable, and (ii) convergence of `int F(proj_S y)` for every finite `S` and
   bounded continuous `F`, give `int F d nu_n -> int F dG` for every bounded continuous `F`.  Proof: the tail bound
   passes to `G` (monotone truncation, using (ii) with `S = {k}`); test against bounded Lipschitz `F`
   (Mathlib `tendsto_iff_forall_lipschitz_integral_tendsto`) and compare `F` with `F o proj_S` using
   `|F y - F (proj_S y)| <= L ||y - proj_S y||`.  No compact embedding / Prokhorov is needed: the uniform
   second-moment tails `sum_{k notin S} jp(k)^{-2m}` (summable since `2m > d`) already give tightness.
2. (Aux2) Haar background: `volume = withDensityReal 1`; `Q_N` is translation invariant, hence every one-particle
   marginal is Haar and `E_Q mu_N(e_k) = 0`; the `k`-th coordinate of `eta_N` is `jp^{-m} sqrt N mu_N(e_k)`;
   `sed_B7_lln_proof` (`m = 1`, `|e_k| <= sqrt 2`) gives `E coord_k^2 <= C jp(k)^{-2m}`, uniform in `N`, `k`.
3. (Aux3) For finite `S` (enumerated `Fin p`), `proj_S (eta_N) = Phi (centeredStat Q_N (e_k)_{k in S})`.
4. (Aux4) Under `G`, the coefficient vector `(F^(k))_{k in S} = (eval F e_k)` is a centred Gaussian with covariance
   `C_ab = int e_a R e_b = sed_Cmat` (`IsGaussian.ext`), i.e. `multivariateGaussian 0 C`.
5. (here) `sed_B10b_clt_proof` for the smooth bounded modes `e_k` gives (ii); assemble with step 1.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.S16a

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

theorem sed_S16a_field_clt_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (G : Measure (NegSobolev d m))
    [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) volume β ψ x ∂volume) :
    ∀ F : NegSobolev d m → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N : ℕ => ∫ X, F (etaE m X volume)
          ∂(modulatedGibbs (periodicRiesz d s) N β volume)) atTop (𝓝 (∫ y, F y ∂G)) := by
  have hβ0 : 0 ≤ β := hβ.le
  have hm' : (d : ℝ) < 2 * m := by linarith
  intro F hFc hFb
  -- the shifted sequence of laws
  have hQp : ∀ n : ℕ, IsProbabilityMeasure (s16aQ d s (n + 1) β) := fun n =>
    s16a_prob hd hs0 hs hβ0 (by omega)
  have hmeas : ∀ n : ℕ, Measurable (fun X : Config d (n + 1) => etaE m X (volume : Measure (Torus d))) := by
    intro n
    have := measurable_ofMeasureDiff_empirical (N := n + 1) hm' (volume : Measure (Torus d))
      (by omega)
    unfold etaE flucE
    exact this.const_smul (Real.sqrt ((n + 1 : ℕ) : ℝ))
  let ν : ℕ → Measure (NegSobolev d m) := fun n =>
    (s16aQ d s (n + 1) β).map (fun X : Config d (n + 1) => etaE m X (volume : Measure (Torus d)))
  have hνp : ∀ n, IsProbabilityMeasure (ν n) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hmeas n).aemeasurable).2 (hQp n)
  haveI := hνp
  obtain ⟨C, hC0, hC⟩ := s16a_coord_tail hd hs0 hs hβ0 hm'
  have hws : Summable (fun k : NonzeroLattice d => C * Lattice.jp k.1 ^ (-(2 * m))) :=
    (summable_jp_rpow (d := d) m hm').mul_left C
  have hw0 : ∀ k : NonzeroLattice d, 0 ≤ C * Lattice.jp k.1 ^ (-(2 * m)) := fun k =>
    mul_nonneg hC0 (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hcont_coord : ∀ k : NonzeroLattice d,
      Measurable (fun y : NegSobolev d m => ENNReal.ofReal (NegSobolev.coord y k ^ 2)) := fun k =>
    Measurable.ennreal_ofReal ((s16a_continuous_coord k).pow 2).measurable
  have hν_tail : ∀ n k, ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2) ∂(ν n) ≤
      ENNReal.ofReal (C * Lattice.jp k.1 ^ (-(2 * m))) := by
    intro n k
    show ∫⁻ y, ENNReal.ofReal (NegSobolev.coord y k ^ 2)
      ∂((s16aQ d s (n + 1) β).map _) ≤ _
    rw [lintegral_map (hcont_coord k) (hmeas n)]
    exact hC (n + 1) (by omega) k
  have hfdd : S16aFdd ν G := by
    intro S F' hF'c hF'b
    have hQcen : ∀ (n : ℕ) (a : Fin S.card), ∫ Y, pair (empirical Y) (s16a_phi S a)
        ∂(s16aQ d s (n + 1) β) = 0 := fun n a =>
      s16a_centering hd hs0 hs hβ0 (by omega) (s16a_e S a)
    set Ψ : EuclideanSpace ℝ (Fin S.card) → ℝ := fun z => F' (s16a_Phi m S z) with hΨ
    have hΨc : Continuous Ψ := hF'c.comp (s16a_continuous_Phi m S)
    have hΨb : ∃ M, ∀ z, |Ψ z| ≤ M := by
      obtain ⟨M, hM⟩ := hF'b
      exact ⟨M, fun z => hM _⟩
    have hB := HRS.MC.SEdge.B10b.sed_B10b_clt_proof hd hs0 hs hβ0
      (s16a_smoothPos (d := d)) (φ := s16a_phi S) (fun a => s16a_phi_smooth S a) hΨc hΨb
    have hB' : Tendsto (fun n : ℕ => ∫ X, Ψ (centeredStat (s16aQ d s (n + 1) β) (s16a_phi S) X)
        ∂(s16aQ d s (n + 1) β)) atTop
        (𝓝 (∫ z, Ψ z ∂multivariateGaussian 0
          (sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) (s16a_phi S)))) := by
      have := hB.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, s16a_sedQ] using this
    have hlimeq : ∫ y, F' (s16a_proj S y) ∂G =
        ∫ z, Ψ z ∂multivariateGaussian 0
          (sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) (s16a_phi S)) := by
      rw [← s16a_law_G hd hs0 hs hβ0 hm G hG S,
        integral_map (s16a_Wmap m S).continuous.measurable.aemeasurable hΨc.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hΨ, s16a_proj_eq_Phi]
    rw [hlimeq]
    refine hB'.congr fun n => ?_
    show _ = ∫ y, F' (s16a_proj S y) ∂((s16aQ d s (n + 1) β).map _)
    rw [integral_map (f := fun y => F' (s16a_proj S y)) (hmeas n).aemeasurable
      (hF'c.comp (s16a_continuous_proj S)).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hΨ]
    rw [s16a_proj_eta_eq_Phi hm' (by omega) S (s16aQ d s (n + 1) β) (hQcen n) X]
  have hmain := s16a_weak_conv ν G hws hw0 hν_tail hfdd F hFc hFb
  have hmain' : Tendsto (fun n : ℕ => ∫ X, F (etaE m X (volume : Measure (Torus d)))
      ∂(s16aQ d s (n + 1) β)) atTop (𝓝 (∫ y, F y ∂G)) := by
    refine hmain.congr fun n => ?_
    show ∫ y, F y ∂((s16aQ d s (n + 1) β).map _) = _
    exact integral_map (hmeas n).aemeasurable hFc.aestronglyMeasurable
  exact (tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∫ X, F (etaE m X (volume : Measure (Torus d)))
    ∂(s16aQ d s N β)) 1).1 hmain'

end HRS.MC.SEdge.S16a

end
