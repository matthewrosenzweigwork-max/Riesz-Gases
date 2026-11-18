import HRS.Equilibrium.QuadraticLimit.GibbsAuxN
import HRS.Equilibrium.QuadraticLimit.GibbsAuxH

/-!
# Lemma 7.5, `q08_gibbs_approx`: final assembly (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace HRS.Q08

section Conv

variable {T : Type*} [MeasurableSpace T] (μ : Measure T) [IsProbabilityMeasure μ]

/-- The doubly centred form of a symmetric kernel. -/
theorem q08gl_kt_conv (k : T → T → ℝ) (hs : ∀ x y, k x y = k y x) (x y : T) :
    k x y - ∫ y', k x y' ∂μ - ∫ x', k x' y ∂μ + ∫ x', ∫ y', k x' y' ∂μ ∂μ = q08e_kt μ k x y := by
  have h : ∫ x', k x' y ∂μ = ∫ y', k y y' ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x' => hs x' y)
  rw [h]
  simp only [q08e_kt, q08e_m, q08e_a]

/-- Iterated integrals of squares of `L²(μ ⊗ μ)` functions. -/
theorem q08gl_iter_prod (f : T → T → ℝ) (hf : MemLp (fun z : T × T => f z.1 z.2) 2 (μ.prod μ)) :
    ∫ x, ∫ y, f x y ^ 2 ∂μ ∂μ = ∫ z : T × T, f z.1 z.2 ^ 2 ∂(μ.prod μ) :=
  (integral_prod (fun z : T × T => f z.1 z.2 ^ 2) hf.integrable_sq).symm

theorem q08gl_kap_sub {m : ℕ} (u : Fin m → T → ℝ) (A B : Matrix (Fin m) (Fin m) ℝ) (x y : T) :
    q08gl_kap u A x y - q08gl_kap u B x y = q08gl_kap u (A - B) x y := by
  unfold q08gl_kap
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.sub_apply]
  ring

end Conv

section FTend

variable {m : ℕ}

theorem q08gl_F2_tendsto (X : ℕ → Matrix (Fin m) (Fin m) ℝ) (X0 : Matrix (Fin m) (Fin m) ℝ)
    (h : ∀ i j, Tendsto (fun L => X L i j) atTop (𝓝 (X0 i j))) :
    Tendsto (fun L => q08gl_F2 (X L)) atTop (𝓝 (q08gl_F2 X0)) := by
  unfold q08gl_F2
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact (h i j).pow 2

end FTend

section Final

variable {d : ℕ} (D : Q08Data d)

/-- `H^U_{ij} = ∬ h u_i u_j`. -/
def q08gl_HU {m : ℕ} (u : Fin m → Torus d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ x, ∫ y, D.h x y * u i x * u j y ∂D.μ ∂D.μ

theorem q08gl_HU_symm {m : ℕ} {u : Fin m → Torus d → ℝ} (hu : q08gl_UData D.μ u) (i j : Fin m) :
    q08gl_HU D u i j = q08gl_HU D u j i := by
  haveI := q08_isProb_μ D
  unfold q08gl_HU
  simp only [Matrix.of_apply]
  have hint : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 * u i z.1 * u j z.2) (D.μ.prod D.μ) := by
    have := (q08s_h_memLp D).integrable_mul (q08s_memLp_tensor (q08gl_memLp_u' hu i) (q08gl_memLp_u' hu j))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [integral_integral_swap (f := fun x y => D.h x y * u i x * u j y) hint]
  refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae (Eventually.of_forall fun b => ?_))
  simp only
  rw [D.hsymm b a]
  ring

theorem q08gl_bf_ker {m : ℕ} {u : Fin m → Torus d → ℝ} (k : Torus d → Torus d → ℝ)
    (hs : ∀ x y, k x y = k y x) (τ : ℝ)
    (h : ∫ x, ∫ y, (k x y - ∫ y', k x y' ∂D.μ - ∫ x', k x' y ∂D.μ + ∫ x', ∫ y', k x' y' ∂D.μ ∂D.μ
            - ∑ i, ∑ j, (∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) * u i x * u j y) ^ 2 ∂D.μ ∂D.μ ≤ τ ^ 2)
    (hw : MemLp (fun z : Torus d × Torus d => q08e_kt D.μ k z.1 z.2 -
      q08gl_kap u (Matrix.of fun i j => ∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) z.1 z.2) 2
      (D.μ.prod D.μ)) :
    ∫ z : Torus d × Torus d, (q08e_kt D.μ k z.1 z.2 -
      q08gl_kap u (Matrix.of fun i j => ∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) z.1 z.2) ^ 2
      ∂(D.μ.prod D.μ) ≤ τ ^ 2 := by
  haveI := q08_isProb_μ D
  have hpt : ∀ x y, (k x y - ∫ y', k x y' ∂D.μ - ∫ x', k x' y ∂D.μ + ∫ x', ∫ y', k x' y' ∂D.μ ∂D.μ
            - ∑ i, ∑ j, (∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) * u i x * u j y) =
      q08e_kt D.μ k x y - q08gl_kap u (Matrix.of fun i j => ∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) x y := by
    intro x y
    rw [← q08gl_kt_conv D.μ k hs x y]
    simp only [q08gl_kap, Matrix.of_apply]
  simp only [hpt] at h
  rw [← q08gl_iter_prod D.μ (fun x y => q08e_kt D.μ k x y -
    q08gl_kap u (Matrix.of fun i j => ∫ x', ∫ y', k x' y' * u i x' * u j y' ∂D.μ ∂D.μ) x y) hw]
  exact h

set_option maxHeartbeats 1600000 in
/-- **`q08_gibbs_approx`** in unfolded form. -/
theorem q08gl_final (F : ℝ × (Fin D.p → ℝ) → ℝ) (hb : ∃ M, ∀ z, |F z| ≤ M)
    (hl : ∃ K : ℝ≥0, LipschitzWith K F) (ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ᶠ N : ℕ in atTop,
      |∫ X : Config d N, F ((N : ℝ) * (modulatedEnergy D.h X D.μ -
              ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
            fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) -
              pair (firstMarginal (D.Gibbs N)) (D.φ a))) ∂(D.Gibbs N) -
        ∫ g : EuclideanSpace ℝ (Fin L), F ((1 / 2) * ∑ i : Fin L, ∑ j : Fin L,
            D.Hmat i j * (g i * g j - D.Cmat i j), fun b => ∑ i : Fin L, D.coef b i * g i)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (Matrix.of fun i j : Fin L => D.Cmat i j))| ≤ ε := by
  haveI := q08_isProb_μ D
  obtain ⟨M0, hM0⟩ := hb
  obtain ⟨K, hK⟩ := hl
  have hβ : 0 < D.β := D.hβ
  obtain ⟨δ, hδ, hmain⟩ := q08gl_main D F ⟨M0, hM0⟩ ⟨K, hK⟩ (ε / 2) (by linarith)
  -- constants
  set β : ℝ := D.β with hβdef
  set Cg : ℝ := ∫ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2 ∂(D.μ.prod D.μ) with hCg
  have hCg0 : 0 ≤ Cg := integral_nonneg fun z => sq_nonneg _
  set c2 : ℝ := 2 + 64 * (1 + β ^ 2 * Cg) with hc2def
  have hc2 : 1 ≤ c2 := by
    have : 0 ≤ β ^ 2 * Cg := mul_nonneg (sq_nonneg _) hCg0
    rw [hc2def]; linarith
  have hc2pos : 0 < c2 := by linarith
  have hKn : (0 : ℝ) ≤ K := K.2
  set τ : ℝ := min (min 1 (1 / (4 * β))) (min (δ ^ 2 / c2) (ε / (2 * ((K : ℝ) + 1) * ((D.p : ℝ) + 1)))) with hτ
  have hτ0 : 0 < τ := by
    refine lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) ?_)
    positivity
  have hτ1 : τ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ 1 / (4 * β) := (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ δ ^ 2 / c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ4 : τ ≤ ε / (2 * ((K : ℝ) + 1) * ((D.p : ℝ) + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτc : τ * c2 ≤ δ ^ 2 := (le_div_iff₀ hc2pos).1 hτ3
  have hτsq : τ ^ 2 ≤ τ := by nlinarith
  have hτδ : τ ^ 2 ≤ δ ^ 2 := by nlinarith
  have hτe : (K : ℝ) * (τ + D.p * τ) ≤ ε / 2 := by
    have h1 : τ * (2 * ((K : ℝ) + 1) * ((D.p : ℝ) + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 hτ4
    have h2 : (K : ℝ) * (τ + D.p * τ) = (K : ℝ) * (τ * ((D.p : ℝ) + 1)) := by ring
    have h3 : (K : ℝ) * (τ * ((D.p : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (τ * ((D.p : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  -- the bounded family
  obtain ⟨m, u, hum, hu0, huo, hker, hphi⟩ := q08_bounded_family D τ hτ0
  have hu : q08gl_UData D.μ u := ⟨fun i => (hum i).1, fun i => (hum i).2, hu0, huo⟩
  have hktg : MemLp (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08e_kt_memLp D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)
  have hkth : MemLp (fun z : Torus d × Torus d => q08e_kt D.μ D.h z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08e_kt_memLp D.μ D.h D.hmeas (q08s_h_memLp D).integrable_sq
  have hKUτ : ∫ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
      q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ τ ^ 2 :=
    q08gl_bf_ker D (fun x y => periodicRiesz d D.s (x - y)) (q08gl_kg_symm' D) τ
      (hker _ (Or.inl rfl)) (hktg.sub (q08gl_kap_memLp (q08gl_KU D u) hu))
  have hHUτ : ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 -
      q08gl_kap u (q08gl_HU D u) z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ τ ^ 2 :=
    q08gl_bf_ker D D.h D.hsymm τ (hker _ (Or.inr rfl)) (hkth.sub (q08gl_kap_memLp (q08gl_HU D u) hu))
  have hφτ : ∀ b, ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, l2Inner D.μ (D.φ b) (u k) * u k x) ^ 2 ∂D.μ ≤ τ ^ 2 :=
    hphi
  -- convergence of the finite sections
  have hSE := q08gl_Sig_est D hu
  have hlim : q08gl_F2 ((1 + β • q08gl_KU D u) * q08gl_Sig D hu - 1) ≤ β ^ 2 * τ ^ 2 :=
    hSE.trans (mul_le_mul_of_nonneg_left hKUτ (sq_nonneg β))
  have hXt : ∀ i j, Tendsto (fun L => ((1 + β • q08gl_KU D u) * q08gl_SL D u L - 1) i j) atTop
      (𝓝 (((1 + β • q08gl_KU D u) * q08gl_Sig D hu - 1) i j)) := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    exact (tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul (q08gl_SL_tendsto D hu k j)).sub
      tendsto_const_nhds
  have hF2t := q08gl_F2_tendsto _ _ hXt
  have hβτ : 0 < β ^ 2 * τ ^ 2 := by positivity
  have hev : ∀ᶠ L in atTop, q08gl_F2 ((1 + β • q08gl_KU D u) * q08gl_SL D u L - 1) < (2 * β * τ) ^ 2 :=
    hF2t.eventually (gt_mem_nhds (by nlinarith))
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hev
  refine ⟨L0, fun L hL => ?_⟩
  -- the inverse matrix
  have hS : (q08gl_SL D u L)ᵀ = q08gl_SL D u L := by
    ext i j
    simp only [Matrix.transpose_apply]
    exact q08gl_SL_symm D j i L
  have hrho := q08gl_rho_eq D hu
  have hrho0 : 0 ≤ ∫ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
      q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) := integral_nonneg fun z => sq_nonneg _
  have hFk : q08gl_F2 (q08gl_KU D u) ≤ (Real.sqrt Cg) ^ 2 := by
    rw [Real.sq_sqrt hCg0]
    unfold q08gl_F2 q08gl_KU
    simp only [Matrix.of_apply]
    linarith
  have he0 : 0 ≤ 2 * β * τ := by positivity
  have he : 2 * β * τ ≤ 1 / 2 := by
    have : β * τ ≤ β * (1 / (4 * β)) := mul_le_mul_of_nonneg_left hτ2 hβ.le
    have h2 : β * (1 / (4 * β)) = 1 / 4 := by field_simp
    linarith
  obtain ⟨K', hK't, hK'psd, hSK, hF2K⟩ := q08gl_matrix_inv β hβ (q08gl_KU D u) (q08gl_SL D u L) hS
    (fun x => q08gl_SL_psd D x L) (fun x => q08gl_SL_le D hu x L) (Real.sqrt Cg) (2 * β * τ) hFk he0 he
    (hL0 L hL).le
  have hF2K' : q08gl_F2 (K' - q08gl_KU D u) ≤ 32 * (1 + β ^ 2 * Cg) * τ ^ 2 := by
    refine hF2K.trans (le_of_eq ?_)
    rw [Real.sq_sqrt hCg0]
    field_simp
    ring
  -- closeness of the kernel of `K'`
  have hkapK : MemLp (fun z : Torus d × Torus d => q08gl_kap u K' z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08gl_kap_memLp K' hu
  have hkapKU : MemLp (fun z : Torus d × Torus d => q08gl_kap u (q08gl_KU D u) z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08gl_kap_memLp (q08gl_KU D u) hu
  have hdK : MemLp (fun z : Torus d × Torus d => q08gl_kap u (q08gl_KU D u - K') z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08gl_kap_memLp _ hu
  have ha : Integrable (fun z : Torus d × Torus d => (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
      q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2) (D.μ.prod D.μ) := (hktg.sub hkapKU).integrable_sq
  have hbb : Integrable (fun z : Torus d × Torus d => q08gl_kap u (q08gl_KU D u - K') z.1 z.2 ^ 2)
    (D.μ.prod D.μ) := hdK.integrable_sq
  have hLHS : Integrable (fun z : Torus d × Torus d => (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
      q08gl_kap u K' z.1 z.2) ^ 2) (D.μ.prod D.μ) := (hktg.sub hkapK).integrable_sq
  have hker' : ∫ z : Torus d × Torus d, (q08e_kt D.μ (fun x y => periodicRiesz d D.s (x - y)) z.1 z.2 -
      q08gl_kap u K' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ δ ^ 2 := by
    have hpt : ∀ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u K' z.1 z.2) ^ 2 ≤
        2 * (q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 +
          2 * q08gl_kap u (q08gl_KU D u - K') z.1 z.2 ^ 2 := by
      intro z
      have := q08gl_kap_sub u (q08gl_KU D u) K' z.1 z.2
      rw [← this]
      nlinarith [sq_nonneg ((q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u (q08gl_KU D u) z.1 z.2) -
        (q08gl_kap u (q08gl_KU D u) z.1 z.2 - q08gl_kap u K' z.1 z.2))]
    have hRHS : Integrable (fun z : Torus d × Torus d => 2 * (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
        q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 + 2 * q08gl_kap u (q08gl_KU D u - K') z.1 z.2 ^ 2)
        (D.μ.prod D.μ) := (ha.const_mul 2).add (hbb.const_mul 2)
    have h1 := integral_mono hLHS hRHS hpt
    rw [integral_add (ha.const_mul 2) (hbb.const_mul 2), integral_const_mul, integral_const_mul,
      q08gl_kap_sq _ hu] at h1
    have h2 : ∑ k, ∑ l, (q08gl_KU D u - K') k l ^ 2 = q08gl_F2 (K' - q08gl_KU D u) := by
      rw [← q08gl_F2_neg, neg_sub]; rfl
    rw [h2] at h1
    show ∫ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u K' z.1 z.2) ^ 2
      ∂(D.μ.prod D.μ) ≤ δ ^ 2
    have h3 : 2 * τ ^ 2 + 2 * (32 * (1 + β ^ 2 * Cg) * τ ^ 2) = c2 * τ ^ 2 := by rw [hc2def]; ring
    have h4 : c2 * τ ^ 2 ≤ δ ^ 2 := by nlinarith
    linarith
  have hm := hmain m u K' (q08gl_HU D u) (q08gl_SL D u L) (fun b k => l2Inner D.μ (D.φ b) (u k)) hu hK'psd
    (q08gl_HU_symm D hu) hSK hker' (hHUτ.trans hτδ) (fun b => (hφτ b).trans hτδ)
  have hc := q08gl_couple D hu (q08gl_HU D u) (q08gl_HU_symm D hu) (fun b k => l2Inner D.μ (D.φ b) (u k)) τ
    hτ0.le hHUτ hφτ F M0 hM0 K hK L
  filter_upwards [hm] with N hN
  rw [abs_le] at hN hc ⊢
  constructor <;> linarith [hN.1, hN.2, hc.1, hc.2]

end Final

end HRS.Q08

end
