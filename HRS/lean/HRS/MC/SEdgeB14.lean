import HRS.MC.SEdgeB14Aux2

/-!
# Packet B14: `static_edge` (assembly) -- relocation of `HRS.MC.SEdge.static_edge_proof`

For `F in C_b^5`, `f` is the Stein solution of B11b.  B12 gives the exact decomposition
`sqrt N (E F(W_N) - E F(Z)) = e1 - e2 + e3` with
* `e1 = sum_ab sqrt N (C_ab - E A_ab) E g_ab(W_N) -> 0` (B13a),
* `e2 = sum_ab E[Y_{w_ab} g_ab(W_N)] -> sum mu(w_ab r_c) E d_cba f(Z)` (B13b),
* `e3 = beta sum_a E[B_a d_a f(W_N)] -> (beta/2) sum Q_{a;bc} E d_abc f(Z)` (B13c; absent for `beta = 0`),
and the cubic cancellation B9cancel together with the symmetry of `D^3 f` and B11b give the limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B14

open HRS.Sec7
open HRS.MC.SEdge

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem b14_main {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {F : EuclideanSpace ℝ (Fin p) → ℝ} (hF : MemCb 5 F) :
    Tendsto (fun N : ℕ => Real.sqrt N *
        (∫ X, F (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) -
          ∫ z, F z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)) -
          (1 / (6 * Real.sqrt N)) * ∑ a, ∑ b, ∑ c, sed_kappa d s β ρ φ a b c *
            ∫ z, iteratedFDeriv ℝ 3 F z ![stdVec a, stdVec b, stdVec c]
              ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) atTop (𝓝 0) := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := B3.b3_prob hρ
  set γ := multivariateGaussian 0 (sed_Cmat d s β ρ φ) with hγ
  have hCpsd : (sed_Cmat d s β ρ φ).PosSemidef := B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ hρ hφ
  obtain ⟨f, -, hf5, hfb, hstein, hthird⟩ := B11b.sed_B11b_ou_proof _ hCpsd hF
  have hf3 : ContDiff ℝ 3 f := hf5.of_le (by norm_num)
  have hf : sed_StBdd f 3 := ⟨hf3, fun j h1 h3 =>
    ⟨(j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j F y‖, fun x => hfb j h1 (by omega) x⟩⟩
  have hFc : Continuous F := hF.1.continuous
  have hFb : ∃ M, ∀ z, |F z| ≤ M := by
    obtain ⟨M, hM⟩ := hF.2 0 (Nat.zero_le _)
    exact ⟨M, fun z => by simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hM ⟨z, rfl⟩⟩
  -- smooth data
  choose ra va hras hvas hae hresp hmean hdiv using
    fun a => B1.sed_B1_regular_proof hd hs0 hs hβ hρ (hφ a)
  have hint : ∀ a, ∀ N : ℕ, 1 ≤ N → Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s (va a)) X (withDensityReal ρ))
      (sed_Q d s N β ρ) := fun a => (B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ (hvas a)).1
  -- tensors
  obtain ⟨T, hTdef⟩ : ∃ T : Fin p → Fin p → Fin p → ℝ, ∀ a b c,
      T a b c = ∫ z, iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c] ∂γ :=
    ⟨fun a b c => _, fun _ _ _ => rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm : Fin p → Fin p → Fin p → ℝ, ∀ a b c,
      mm a b c = ∫ x, sed_drift (va a) (φ b) x *
        responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c) x ∂(withDensityReal ρ) :=
    ⟨fun a b c => _, fun _ _ _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin p → Fin p → Fin p → ℝ, ∀ a b c,
      q a b c = sed_Qt d s ρ (va a)
        (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b))
        (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c)) :=
    ⟨fun a b c => _, fun _ _ _ => rfl⟩
  -- the three sequences
  obtain ⟨e1, he1⟩ : ∃ e1 : ℕ → ℝ, e1 = fun N : ℕ => ∑ a, ∑ b, Real.sqrt N *
      (sed_Cmat d s β ρ φ a b - ∫ X, sed_A (va a) (φ b) X ∂(sed_Q d s N β ρ)) *
      ∫ X, iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
        ∂(sed_Q d s N β ρ) := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : ℕ → ℝ, e2 = fun N : ℕ => ∑ a, ∑ b,
      ∫ X, sed_Y (sed_Q d s N β ρ) (sed_drift (va a) (φ b)) X *
        iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
        ∂(sed_Q d s N β ρ) := ⟨_, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ e3 : ℕ → ℝ, e3 = fun N : ℕ => β * ∑ a,
      ∫ X, sed_B d s ρ β (va a) X * fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a)
        ∂(sed_Q d s N β ρ) := ⟨_, rfl⟩
  -- the exact identity
  have hid : ∀ N : ℕ, 1 ≤ N → Real.sqrt N *
      (∫ X, F (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) - ∫ z, F z ∂γ) =
      e1 N - e2 N + e3 N := by
    intro N hN
    haveI := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
    have hmaster := B12.sed_B12_master_proof hd hs0 hs hβ hρ hN hφ hras hvas hdiv hresp
      (fun a => hint a N hN) hFc hFb hf hstein
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hWm := b14_Wmeas hN hφ (sed_Q d s N β ρ)
    have hg : ∀ a b, b14Bdd (fun X : Config d N => iteratedFDeriv ℝ 2 f
        (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]) := by
      intro a b
      obtain ⟨hc, M, hM⟩ := B12.b12_second_facts hf a b
      exact ⟨hc.measurable.comp hWm, M, fun X => hM _⟩
    have hA : ∀ a b, b14Bdd (fun X : Config d N => sed_A (va a) (φ b) X) := fun a b =>
      B12.b12_A_facts hN (hvas a) (hφ b)
    have hterm : ∀ a b, Real.sqrt N * ∫ X, (sed_Cmat d s β ρ φ a b - sed_A (va a) (φ b) X) *
        iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
          ∂(sed_Q d s N β ρ) =
        Real.sqrt N * (sed_Cmat d s β ρ φ a b - ∫ X, sed_A (va a) (φ b) X ∂(sed_Q d s N β ρ)) *
          ∫ X, iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
            ∂(sed_Q d s N β ρ) -
        ∫ X, sed_Y (sed_Q d s N β ρ) (sed_drift (va a) (φ b)) X *
          iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
            ∂(sed_Q d s N β ρ) := fun a b =>
      b14_split (sed_Q d s N β ρ) (sed_Cmat d s β ρ φ a b) (Real.sqrt N) _ _
        ((hg a b).integrable _) (((hA a b).mul (hg a b)).integrable _)
    rw [hmaster, he1, he2, he3]
    have h1 : Real.sqrt N * (β / Real.sqrt N * ∑ a, ∫ X, sed_B d s ρ β (va a) X *
        fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ)) =
        β * ∑ a, ∫ X, sed_B d s ρ β (va a) X *
          fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ) := by
      field_simp
    rw [mul_add, h1, Finset.mul_sum]
    simp only [Finset.mul_sum, hterm, Finset.sum_sub_distrib]
  -- e1 -> 0
  have hT1 : Tendsto e1 atTop (𝓝 0) := by
    have hab : ∀ a b, Tendsto (fun N : ℕ => Real.sqrt N *
        (sed_Cmat d s β ρ φ a b - ∫ X, sed_A (va a) (φ b) X ∂(sed_Q d s N β ρ)) *
        ∫ X, iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
          ∂(sed_Q d s N β ρ)) atTop (𝓝 0) := by
      intro a b
      obtain ⟨K, hK⟩ := B13a.sed_B13a_bias_proof hd hs0 hs hβ hρ hφ (a := a) (b := b)
        (hras a) (hvas a) (hdiv a) (hresp a)
      obtain ⟨hc, Mg, hMg⟩ := B12.b12_second_facts hf a b
      have hlim : Tendsto (fun N : ℕ => |K| * |Mg| / Real.sqrt N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop b14_tendsto_sqrt
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      haveI := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
      have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hg : |∫ X, iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X)
          ![stdVec b, stdVec a] ∂(sed_Q d s N β ρ)| ≤ |Mg| :=
        (b14_abs_integral_le (fun X => hMg _)).trans (le_abs_self _)
      have hb : |Real.sqrt N * (sed_Cmat d s β ρ φ a b -
          ∫ X, sed_A (va a) (φ b) X ∂(sed_Q d s N β ρ))| ≤ |K| / Real.sqrt N := by
        rw [abs_mul, abs_of_pos hsq]
        calc Real.sqrt N * |sed_Cmat d s β ρ φ a b - ∫ X, sed_A (va a) (φ b) X ∂(sed_Q d s N β ρ)|
            ≤ Real.sqrt N * (K / N) := mul_le_mul_of_nonneg_left (hK N hN) hsq.le
          _ = K / Real.sqrt N := b14_sqrt_div hN K
          _ ≤ |K| / Real.sqrt N := div_le_div_of_nonneg_right (le_abs_self K) hsq.le
      rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ |K| / Real.sqrt N * |Mg| := mul_le_mul hb hg (abs_nonneg _) (by positivity)
        _ = |K| * |Mg| / Real.sqrt N := by ring
    rw [he1]
    have := tendsto_finset_sum Finset.univ fun a _ =>
      tendsto_finset_sum Finset.univ fun b _ => hab a b
    simpa only [Finset.sum_const_zero] using this
  -- e2
  have hlim2 : ∀ a b, Tendsto (fun N : ℕ => ∫ X, sed_Y (sed_Q d s N β ρ) (sed_drift (va a) (φ b)) X *
        iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
        ∂(sed_Q d s N β ρ)) atTop (𝓝 (∑ c, mm a b c * T a c b)) := by
    intro a b
    have h := B13b.sed_B13b_linear_limit_proof hd hs0 hs hβ hρ hφ
      (b14_drift_smooth (hvas a) (hφ b)) (b14_g_memCb hf a b)
    have heq : ∀ c, ∫ z, fderiv ℝ (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) z
        (stdVec c) ∂γ = T a c b := fun c => by
      rw [hTdef]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => b14_fderiv_g hf3 a b c z)
    have hsum : ∑ c, (∫ x, sed_drift (va a) (φ b) x *
        responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c) x ∂(withDensityReal ρ)) *
        ∫ z, fderiv ℝ (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) z (stdVec c) ∂γ =
        ∑ c, mm a b c * T a c b := Finset.sum_congr rfl fun c _ => by rw [heq c, hmm]
    rw [← hsum]
    exact h
  have hT2 : Tendsto e2 atTop (𝓝 (∑ a, ∑ b, ∑ c, mm a b c * T a c b)) := by
    rw [he2]
    exact tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ => hlim2 a b
  -- e3
  have hT3 : Tendsto e3 atTop (𝓝 (β * ∑ a, (1 / 2) * ∑ b, ∑ c, q a b c * T a b c)) := by
    rw [he3]
    by_cases hβ0 : β = 0
    · simp [hβ0]
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      refine Tendsto.const_mul β (tendsto_finset_sum _ fun a _ => ?_)
      have := B13c.sed_B13c_chaos_limit_proof hd hs0 hs hβ hρ hβpos hφ (hvas a) hf a
      simp only [hq, hTdef]
      exact this
  -- the cubic cancellation, transferred to `responseInverse`
  have hcan : ∀ a b c, mm a b c + mm a c b - β * q a b c = sed_kappa d s β ρ φ a b c := by
    intro a b c
    have h := B9cancel.sed_B9cancel_proof hd hs0 hs hβ hρ (hras a) (hras b) (hras c) (hφ b) (hφ c)
      (hvas a) (hdiv a) (hresp b) (hresp c)
    have e1' : ∫ x, sed_drift (va a) (φ b) x * ra c x ∂(withDensityReal ρ) = mm a b c := by
      rw [hmm]
      refine integral_congr_ae ?_
      filter_upwards [hae c] with x hx
      rw [hx]
    have e2' : ∫ x, sed_drift (va a) (φ c) x * ra b x ∂(withDensityReal ρ) = mm a c b := by
      rw [hmm]
      refine integral_congr_ae ?_
      filter_upwards [hae b] with x hx
      rw [hx]
    have e3' := (B15c.sed_B15c_congr_proof s (va a) (hae b) (hae c) (hae a)).1
    have e4' := (B15c.sed_B15c_congr_proof s (va a) (hae a) (hae b) (hae c)).2
    rw [hq, ← e3']
    unfold sed_kappa
    rw [← e4']
    linarith [h, e1', e2']
  have hTsymm : ∀ a b c, T a b c = T a c b := fun a b c => by
    rw [hTdef, hTdef]; exact b14_T_symm hf3 γ a b c
  have halg := b14_alg β T mm q (sed_kappa d s β ρ φ) hTsymm hcan
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ a, ∑ b, ∑ c, sed_kappa d s β ρ φ a b c *
      ∫ z, iteratedFDeriv ℝ 3 F z ![stdVec a, stdVec b, stdVec c] ∂γ := ⟨_, rfl⟩
  have hκT : ∑ a, ∑ b, ∑ c, sed_kappa d s β ρ φ a b c * T a b c = -(1 / 3) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hTdef, hthird]; ring
  have key : Tendsto (fun N => e1 N - e2 N + e3 N - S / 6) atTop (𝓝 0) := by
    have := ((hT1.sub hT2).add hT3).sub_const (S / 6)
    convert this using 2
    linarith
  rw [← hS]
  refine Tendsto.congr' ?_ key
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [← hid N hN]
  field_simp

end Main

section Final

variable {d : ℕ}

theorem static_edge_assembly_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 ≤ β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    let μ := withDensityReal ρ
    let r : Fin p → Torus d → ℝ := fun a => responseInverse (periodicRiesz d s) μ β (φ a)
    let C : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => ∫ x, φ a x * r b x ∂μ
    let κ : Fin p → Fin p → Fin p → ℝ := fun a b c => ∫ x, r a x * r b x * r c x ∂μ
    ∀ F : EuclideanSpace ℝ (Fin p) → ℝ, MemCb 5 F →
      Tendsto (fun N : ℕ => Real.sqrt N *
        (∫ X, F (centeredStat (modulatedGibbs (periodicRiesz d s) N β μ) φ X)
            ∂(modulatedGibbs (periodicRiesz d s) N β μ) -
          ∫ z, F z ∂(multivariateGaussian 0 C) -
          (1 / (6 * Real.sqrt N)) * ∑ a, ∑ b, ∑ c, κ a b c *
            ∫ z, iteratedFDeriv ℝ 3 F z ![stdVec a, stdVec b, stdVec c] ∂(multivariateGaussian 0 C)))
        atTop (𝓝 0) := by
  intro μ r C κ F hF
  exact b14_main hd hs0 hs hβ hρ hφ hF

end Final

end HRS.MC.SEdge.B14

end


