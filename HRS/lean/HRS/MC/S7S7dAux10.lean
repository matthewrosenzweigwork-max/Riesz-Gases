import HRS.MC.S7S7dAux9
import HRS.MC.S7S7c
import HRS.MC.S7S7eAux2
import HRS.MC.SEdgeB11a

/-!
# Packet `s7_S7d_uniform_limits`, helper 10: the Gaussian side

* `s7d_eval_phi`: `F(phi_k) = coord F k`;
* the law of the finite coordinates `(coord F (kappa a))_a` under the Gaussian `G` is
  `N(0, sed_Cmat)` (adapting `s16a_law_G`; `responseInverse (phi_k) = a_k` a.e.);
* `iota (Wmap kappa_K F) = truncE K F`;
* `∫ min(2, ‖F - truncE K F‖) dG → 0` along `K → ∞` (dominated convergence).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_eval_phi (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.eval F (s7_phi r k) = NegSobolev.coord F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff NegSobolev.fourierCoeff s7_phi
    have : ∀ x : Torus d, Torus.realMode k x * (Lattice.jp k.1 ^ (-r) * Torus.realMode k x) =
        Lattice.jp k.1 ^ (-r) * (Torus.realMode k x * Torus.realMode k x) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, Torus.realMode_orthonormal k k]
    simp only [if_true, mul_one]
    rw [mul_right_comm, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  · intro l hl
    unfold Torus.funRealCoeff s7_phi
    have : ∀ x : Torus d, Torus.realMode l x * (Lattice.jp k.1 ^ (-r) * Torus.realMode k x) =
        Lattice.jp k.1 ^ (-r) * (Torus.realMode l x * Torus.realMode k x) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, Torus.realMode_orthonormal l k, if_neg hl]
    simp

/-- Coordinates on the modes `κ`. -/
def s7d_Wmap (r : ℝ) {p : ℕ} (κ : Fin p → NonzeroLattice d) :
    NegSobolev d r →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ∑ a : Fin p, (negCoordCLM (m := r) (κ a)).smulRight (EuclideanSpace.single a (1 : ℝ))

theorem s7d_Wmap_apply {p : ℕ} (κ : Fin p → NonzeroLattice d) (F : NegSobolev d r) (a : Fin p) :
    s7d_Wmap r κ F a = NegSobolev.coord F (κ a) := by
  classical
  unfold s7d_Wmap
  simp [Pi.single_apply, negCoordCLM_apply]

theorem s7d_iota_Wmap (K : Finset (NonzeroLattice d)) (F : NegSobolev d r) :
    HRS.MC.Sec7.S7c.s7c_iota r (HRS.MC.Sec7.S7c.s7c_kap K) (s7d_Wmap r (HRS.MC.Sec7.S7c.s7c_kap K) F) =
      truncE K F := by
  rw [HRS.MC.Sec7.S7c.s7c_iota_apply]
  simp_rw [s7d_Wmap_apply]
  rw [HRS.MC.Sec7.S7c.s7c_sum_kap K (fun k => NegSobolev.coord F k • s7_eps r k)]
  rfl

theorem s7d_truncE_continuous (K : Finset (NonzeroLattice d)) :
    Continuous (fun F : NegSobolev d r => truncE K F) := by
  have : (fun F : NegSobolev d r => truncE K F) =
      fun F => ∑ k ∈ K, negCoordCLM (m := r) k F • s7_eps r k := by
    funext F; rfl
  rw [this]
  exact continuous_finset_sum _ fun k _ => (negCoordCLM (m := r) k).continuous.smul continuous_const

theorem s7d_gauss_trunc_tendsto (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G] :
    Tendsto (fun K : Finset (NonzeroLattice d) =>
      ∫ F, min 2 ‖F - truncE K F‖ ∂G) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := G) (l := atTop)
    (F := fun (K : Finset (NonzeroLattice d)) (F : NegSobolev d r) => min 2 ‖F - truncE K F‖)
    (f := fun _ => 0) (bound := fun _ => 2)
    (Eventually.of_forall fun K => ((continuous_const.min
      (continuous_norm.comp (continuous_id.sub (s7d_truncE_continuous K)))).measurable.aestronglyMeasurable))
    (Eventually.of_forall fun K => Eventually.of_forall fun F => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (norm_nonneg _))]
      exact min_le_left _ _)
    (integrable_const _)
    (Eventually.of_forall fun F => by
      have h1 := HRS.MC.Sec7.S7c.s7c_tendsto_trunc F
      have h2 : Tendsto (fun K : Finset (NonzeroLattice d) => F - truncE K F) atTop (𝓝 (F - F)) :=
        tendsto_const_nhds.sub h1
      rw [sub_self] at h2
      have h3 : Continuous fun x : NegSobolev d r => min (2 : ℝ) ‖x‖ :=
        continuous_const.min continuous_norm
      have h4 := (h3.tendsto (0 : NegSobolev d r)).comp h2
      have h5 : min (2 : ℝ) ‖(0 : NegSobolev d r)‖ = 0 := by simp
      rw [h5] at h4
      exact h4)
  simpa using h

section Law

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hγ hρ

/-- `responseInverse` of a mode test is a.e. the mode datum `a_k`. -/
theorem s7d_respInv_ae {ψ h : Torus d → ℝ} (hψ : MemLp ψ 2 (withDensityReal ρ)) (hh : Continuous h)
    (hmean : pair (withDensityReal ρ) h = 0)
    (heq : ∀ x, h x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) h x =
      projMean (withDensityReal ρ) ψ x) :
    responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ =ᵐ[withDensityReal ρ] h := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨Λ, hΛ'⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
  have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ h :=
    ⟨hh.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), hmean,
      Eventually.of_forall fun x => heq x⟩
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ h := ⟨h, hresp⟩
  obtain ⟨h₀, -, huniq⟩ := exists_unique_response hd hs0 hsd ρ hρ.density Λ
    (fun x => (le_abs_self _).trans (hΛ' x)) γ hγ ψ hψ
  have hchoose := hex.choose_spec
  have hri : responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ = hex.choose := by
    unfold responseInverse
    rw [dif_pos hex]
  rw [hri]
  exact (huniq _ hchoose).trans (huniq h hresp).symm

end Law

end HRS.MC.Sec7.S7d

end
