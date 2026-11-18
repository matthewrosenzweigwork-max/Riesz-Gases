import HRS.MC.S7FCH4C
import HRS.MC.S7FCD5

/-!
# S7FCH4D: the particle-side identification (H4, part D)

`S7FCH4_tilde_eq`: for every configuration, `fcPartTilde = φ_{N^{-1/2}}(η_N) - cst`, from H1a (exact algebra).
`S7FCH4_particle_id`: for `N ≥ 2`, a.s. `toL2 (fcPartAt ..) = ι(Y(ζ_N) - ∫ Y(ζ_N) dP)` where `Y = Y_{N^{-1/2}, m_N}`
and `m_N` is the deterministic mean path of D5 (`ζ_N = η_N - m_N`); only a.s. continuity of the windows (E1, D5B) is used.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open Classical
variable {d : ℕ}

theorem S7FCH4_eval_etaE {N : ℕ} (hN : 1 ≤ N) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (X : Config d N) {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    NegSobolev.eval (etaE r X μ) g = Real.sqrt N * (pair (empirical X) g - pair μ g) := by
  have hsm := HRS.MC.Sec7.S7FCH1.S7FCH1_smooth_props hg
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure (by omega) X
  unfold etaE flucE
  rw [HRS.MC.Sec7.S7FCH1.S7FCH1_eval_smul, NegSobolev.eval_ofMeasureDiff_of_summable hm (empirical X) μ g hsm.1 hsm.2]

/-- The deterministic centring of the particle field: `∑_{k∈S} (½ ∑ c_ij μ(f_i f_j)) e_k`. -/
def S7FCH4_cst (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (μ : Measure (Torus d)) : NegSobolev d r :=
  ∑ k ∈ S, ((1 / 2) * ∑ i, ∑ j, (K k).c i j * pair μ (fun x => (K k).f i x * (K k).f j x)) • S7FCH4_e r k

theorem S7FCH4_tilde_eq {N : ℕ} (hN : 1 ≤ N) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (X : Config d N) :
    fcPartTilde r S K μ X = S7FCH4_phi r S K (Real.sqrt N)⁻¹ (etaE r X μ) - S7FCH4_cst r S K μ := by
  unfold fcPartTilde S7FCH4_phi S7FCH4_cst
  rw [S7FCH4_ofSeq_sum]
  unfold S7FCH4_gq S7FCH4_hq
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hH := HRS.MC.Sec7.S7FCH1.s7_FC_H1a_particle_proof hN r hr μ (K k) X
  have hemp : ∀ i j, pair (empirical X) (fun x => (K k).f i x * (K k).f j x) =
      pair μ (fun x => (K k).f i x * (K k).f j x) +
      (Real.sqrt N)⁻¹ * NegSobolev.eval (etaE r X μ) (fun x => (K k).f i x * (K k).f j x) := by
    intro i j
    rw [S7FCH4_eval_etaE hN r hr μ X (S7FCH4_smooth_mul ((K k).smooth i) ((K k).smooth j))]
    field_simp
    ring
  simp_rw [hemp] at hH
  rw [smul_smul, ← sub_smul, ← sub_smul]
  congr 1
  rw [hH]
  unfold S7FCH4_lin
  have e1 : ∑ i, ∑ j, (K k).c i j * ((pair μ fun x => (K k).f i x * (K k).f j x) +
      (Real.sqrt N)⁻¹ * (etaE r X μ).eval fun x => (K k).f i x * (K k).f j x) =
      (∑ i, ∑ j, (K k).c i j * pair μ (fun x => (K k).f i x * (K k).f j x)) +
      (Real.sqrt N)⁻¹ * ∑ i, ∑ j, (K k).c i j * (etaE r X μ).eval (fun x => (K k).f i x * (K k).f j x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1]
  ring

/-! ### Evaluation as a continuous linear map and Bochner integrals in `PathSpace` -/

def S7FCH4_evalCLM {r T : ℝ} (t : Set.Icc (0 : ℝ) T) : PathSpace d r T →L[ℝ] NegSobolev d r :=
  LinearMap.mkContinuous
    { toFun := fun w => PathSpace.at' w t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun w => by rw [one_mul]; exact S7FCH4_norm_at_le w t)

theorem S7FCH4_at_integral {r T : ℝ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → PathSpace d r T} (hf : Integrable f μ) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (∫ x, f x ∂μ) t = ∫ x, PathSpace.at' (f x) t ∂μ :=
  ((S7FCH4_evalCLM (d := d) (r := r) t).integral_comp_comm hf).symm

theorem S7FCH4_integrable_at {r T : ℝ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → PathSpace d r T} (hf : Integrable f μ) (t : Set.Icc (0 : ℝ) T) :
    Integrable (fun x => PathSpace.at' (f x) t) μ :=
  (S7FCH4_evalCLM (d := d) (r := r) t).integrable_comp hf

/-! ### The particle-side identification -/

open HRS.MC.Sec7.S7FCD5B in
theorem S7FCH4_particle_id (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (m : PathSpace d r T)
    (hm : ∀ᵐ ω ∂P, zetaWin r T 0 P X ω = HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ ω - m)
    (hint : Integrable (fun ω => S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T 0 P X ω)) P) :
    ∀ᵐ ω ∂P, toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (0 + t) ω) =
      S7FCH4_iota hT.le (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T 0 P X ω) -
        ∫ ω', S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T 0 P X ω') ∂P) := by
  have hhon := (S7FCD5B_honest R r hr T (by omega) P X₀ W X hreal).1
  have key : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) T,
      fcPartTilde r S K (withDensityReal (R.ρ t)) (X (t : ℝ).toNNReal ω) =
        PathSpace.at' (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T 0 P X ω)) t -
          S7FCH4_cst r S K (withDensityReal (R.ρ t)) := by
    filter_upwards [hm, hhon] with ω h1 h2
    intro t
    have := isProb_withDensityReal (S7FCD5B_hdens R t t.2.1)
    have hη : PathSpace.at' (zetaWin r T 0 P X ω) t + PathSpace.at' m t =
        etaE r (X (t : ℝ).toNNReal ω) (withDensityReal (R.ρ t)) := by
      rw [h1, S7FCD5B_windowFluc_eq, S7FCH4_at_sub, S7FCD5B_toPath_apply r T _ ω h2 t]
      abel
    rw [S7FCH4_at_Y, hη]
    exact S7FCH4_tilde_eq (by omega) r hr S K _ _
  filter_upwards [key] with ω hω
  refine S7FCH4_toL2_eq_iota hT.le _ _ fun t ht => ?_
  set tt : Set.Icc (0 : ℝ) T := ⟨t, ht⟩ with htt
  have hI : ∫ ω', fcPartTilde r S K (withDensityReal (R.ρ t)) (X t.toNNReal ω') ∂P =
      (∫ ω', PathSpace.at' (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T 0 P X ω')) tt ∂P) -
        S7FCH4_cst r S K (withDensityReal (R.ρ t)) := by
    rw [integral_congr_ae (key.mono fun ω' h => h tt),
      integral_sub (S7FCH4_integrable_at hint tt) (integrable_const _), integral_const]
    simp
    rfl
  show fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (0 + t) ω = _
  unfold fcPartAt
  simp only [zero_add]
  rw [hω tt, hI, S7FCH4_at_sub, S7FCH4_at_integral hint tt]
  abel

end HRS.MC.Sec7.S7FCH4
