import HRS.Main.MixEnt3
import HRS.Equilibrium.PreparationAux

/-!
# MIXENT 4: the expectation of the energy `N F_N(·; μ°)` under the mixture (lemma M3)

TeX L6952-6962: "expected `N F_N` bounded by a fixed quadratic integral".

Part A (`mx_integral_W_iid`): for ANY probability measure `ν` on the torus (sampling law) and centre `μ`,
`E_{ν^{⊗N}}[N F_N(·; μ)] = (N-1)/2 ∬ g dν dν - N ∬ g dμ dν + (N/2) ∬ g dμ dμ`
(the proof of `PreparationAux.integral_energy_iid` with two different measures).
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- **M3, Part A**: expectation of `N F_N(·; μ)` under `ν^{⊗N}` for an arbitrary sampling law `ν`. -/
theorem mx_integral_W_iid {g : Torus d → ℝ} {μ ν : Measure (Torus d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {N : ℕ} (hN : 1 ≤ N)
    (hνν : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (ν.prod ν))
    (hconv : Integrable (fun x => ∫ y, g (x - y) ∂μ) ν) :
    Integrable (fun X : Config d N => (N : ℝ) * modulatedEnergyKernel g X μ)
        (Measure.pi fun _ : Fin N => ν) ∧
      ∫ X : Config d N, (N : ℝ) * modulatedEnergyKernel g X μ ∂(Measure.pi fun _ : Fin N => ν) =
        ((N : ℝ) - 1) / 2 * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(ν.prod ν) -
          N * ∫ x, ∫ y, g (x - y) ∂μ ∂ν + N / 2 * ∫ x, ∫ y, g (x - y) ∂μ ∂μ := by
  set A := ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(ν.prod ν) with hA
  set B := ∫ x, ∫ y, g (x - y) ∂μ ∂ν with hB
  set C := ∫ x, ∫ y, g (x - y) ∂μ ∂μ with hC
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => ν) :=
    fun i j hij => integrable_pair_comp ν hij (H := fun p => g (p.1 - p.2)) hνν
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Config d N, g (X i - X j) ∂(Measure.pi fun _ : Fin N => ν) = A :=
    fun i j hij => integral_pair_comp ν hij (H := fun p => g (p.1 - p.2)) hνν
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => ν) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => ν) (i := i) hconv
  have h1' : ∀ i : Fin N, ∫ X : Config d N, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => ν) = B :=
    fun i => integral_comp_eval (μ := fun _ : Fin N => ν) (i := i) hconv.aestronglyMeasurable
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => ν) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => ν) := integrable_finsetSum _ fun i _ => h1 i
  have hE : Integrable (fun X : Config d N => modulatedEnergyKernel g X μ)
      (Measure.pi fun _ : Fin N => ν) := by
    unfold modulatedEnergyKernel modulatedEnergy
    exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)
  refine ⟨hE.const_mul _, ?_⟩
  have E1 : ∫ X : Config d N, ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      ∂(Measure.pi fun _ : Fin N => ν) = (N : ℝ) * ((N : ℝ) - 1) * A := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Config d N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        ∂(Measure.pi fun _ : Fin N => ν) = ((N : ℝ) - 1) * A := by
      intro i
      rw [integral_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_congr rfl fun j hj => hpair' i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have E2 : ∫ X : Config d N, ∑ i, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => ν) = N * B := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  rw [integral_const_mul]
  unfold modulatedEnergyKernel modulatedEnergy
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => ν).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    have : ∫ x, ∫ y, (fun x y => g (x - y)) x y ∂μ ∂μ = C := rfl
    rw [this]
    field_simp
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

section PartB

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- The bilinear form `J(φ, ψ) = ∬ φ(x) ψ(y) g(x - y) dμ(x) dμ(y)` (a Bochner integral over `μ ⊗ μ`). -/
def mxJ (g : Torus d → ℝ) (μ : Measure (Torus d)) (φ ψ : Torus d → ℝ) : ℝ :=
  ∫ p : Torus d × Torus d, φ p.1 * ψ p.2 * g (p.1 - p.2) ∂(μ.prod μ)

/-- Integrability of the weighted kernel for bounded measurable weights. -/
theorem mx_J_integrable (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    {φ ψ : Torus d → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {Cφ Cψ : ℝ}
    (hCφ : ∀ x, |φ x| ≤ Cφ) (hCψ : ∀ x, |ψ x| ≤ Cψ) :
    Integrable (fun p : Torus d × Torus d => φ p.1 * ψ p.2 * g (p.1 - p.2)) (μ.prod μ) := by
  refine hI.bdd_mul (f := fun p : Torus d × Torus d => φ p.1 * ψ p.2) (c := Cφ * Cψ)
    ((hφ.comp measurable_fst).mul (hψ.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCφ _) (hCψ _) (abs_nonneg _) ((abs_nonneg _).trans (hCφ p.1))

/-- `J(1 + t b, ψ) = J(1, ψ) + t J(b, ψ)`. -/
theorem mx_J_affine_left (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    {b ψ : Torus d → ℝ} (hb : Measurable b) (hψ : Measurable ψ) {M Cψ : ℝ}
    (hM : ∀ x, |b x| ≤ M) (hCψ : ∀ x, |ψ x| ≤ Cψ) (t : ℝ) :
    mxJ g μ (fun x => 1 + t * b x) ψ = mxJ g μ (fun _ => 1) ψ + t * mxJ g μ b ψ := by
  unfold mxJ
  have h1 := mx_J_integrable (μ := μ) hI (φ := fun _ => (1 : ℝ)) (measurable_const) hψ
    (fun _ => by simp : ∀ x, |(fun _ : Torus d => (1 : ℝ)) x| ≤ 1) hCψ
  have h2 := (mx_J_integrable (μ := μ) hI hb hψ hM hCψ).const_mul t
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1; funext p; ring

/-- `J(φ, 1 + t b) = J(φ, 1) + t J(φ, b)`. -/
theorem mx_J_affine_right (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    {b φ : Torus d → ℝ} (hb : Measurable b) (hφ : Measurable φ) {M Cφ : ℝ}
    (hM : ∀ x, |b x| ≤ M) (hCφ : ∀ x, |φ x| ≤ Cφ) (t : ℝ) :
    mxJ g μ φ (fun x => 1 + t * b x) = mxJ g μ φ (fun _ => 1) + t * mxJ g μ φ b := by
  unfold mxJ
  have h1 := mx_J_integrable (μ := μ) hI (ψ := fun _ => (1 : ℝ)) hφ (measurable_const)
    hCφ (fun _ => by simp : ∀ x, |(fun _ : Torus d => (1 : ℝ)) x| ≤ 1)
  have h2 := (mx_J_integrable (μ := μ) hI hφ hb hCφ hM).const_mul t
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1; funext p; ring

/-- Symmetry `J(b, 1) = J(1, b)` for an even kernel. -/
theorem mx_J_symm (geven : ∀ x, g (-x) = g x) (b : Torus d → ℝ) :
    mxJ g μ b (fun _ => 1) = mxJ g μ (fun _ => 1) b := by
  unfold mxJ
  rw [← integral_prod_swap (μ := μ) (ν := μ)]
  congr 1; funext p
  simp only [Prod.fst_swap, Prod.snd_swap, one_mul, mul_one]
  rw [show p.2 - p.1 = -(p.1 - p.2) by abel, geven]

/-- **M3, Part B**: expectation of `N F_N(·; μ)` under the product law with one-particle density
`1 + t b` (relative to `μ`, `μ(b) = 0`, `|t b| ≤ 1/2`):
`E[N F_N] = -J(1,1)/2 - t J(1,b) + ((N-1)/2) t² J(b,b)` (and the energy is integrable). -/
theorem mx_energy_withDensity (hgm : Measurable g) (geven : ∀ x, g (-x) = g x)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    {b : Torus d → ℝ} (hb : Measurable b) {M : ℝ} (hM : ∀ x, |b x| ≤ M)
    (hb0 : ∫ x, b x ∂μ = 0) (t : ℝ) (htb : ∀ x, |t * b x| ≤ 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => (N : ℝ) * modulatedEnergyKernel g X μ)
        (Measure.pi fun _ : Fin N => μ.withDensity fun x => ENNReal.ofReal (1 + t * b x)) ∧
      ∫ X : Config d N, (N : ℝ) * modulatedEnergyKernel g X μ
          ∂(Measure.pi fun _ : Fin N => μ.withDensity fun x => ENNReal.ofReal (1 + t * b x)) =
        -(1 / 2) * mxJ g μ (fun _ => 1) (fun _ => 1) - t * mxJ g μ (fun _ => 1) b +
          (((N : ℝ) - 1) / 2) * t ^ 2 * mxJ g μ b b := by
  set f : Torus d → ℝ := fun x => 1 + t * b x with hf
  have hfm : Measurable f := by fun_prop
  have hf1 : ∀ x, 1 / 2 ≤ f x ∧ f x ≤ 3 / 2 := fun x => by
    have := abs_le.1 (htb x); simp only [hf]; constructor <;> linarith [this.1, this.2]
  have hfb : ∀ x, |f x| ≤ 3 / 2 := fun x => by
    rw [abs_of_pos (by linarith [(hf1 x).1])]; exact (hf1 x).2
  have hbi : Integrable b μ :=
    Integrable.of_bound hb.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).add (hbi.const_mul t)
  have hfint : ∫ x, f x ∂μ = 1 := by
    simp only [hf]
    rw [integral_add (integrable_const (1 : ℝ)) (hbi.const_mul t), integral_const_mul, hb0]
    simp
  set ν : Measure (Torus d) := μ.withDensity fun x => ENNReal.ofReal (f x) with hν
  haveI : IsProbabilityMeasure ν :=
    mx_isProb_withDensity μ f (fun x => by linarith [(hf1 x).1]) hfi hfint
  have hD : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hfm
  have hDlt : ∀ x, ENNReal.ofReal (f x) < ⊤ := fun x => ENNReal.ofReal_lt_top
  have hfnn : ∀ x, 0 ≤ f x := fun x => by linarith [(hf1 x).1]
  -- the product density
  have hprod : ν.prod ν = (μ.prod μ).withDensity
      (fun z => ENNReal.ofReal (f z.1) * ENNReal.ofReal (f z.2)) :=
    prod_withDensity₀ hD.aemeasurable hD.aemeasurable
  have hDp : Measurable fun z : Torus d × Torus d =>
      ENNReal.ofReal (f z.1) * ENNReal.ofReal (f z.2) :=
    (hD.comp measurable_fst).mul (hD.comp measurable_snd)
  have hDplt : ∀ᵐ z ∂(μ.prod μ), ENNReal.ofReal (f z.1) * ENNReal.ofReal (f z.2) < ⊤ :=
    ae_of_all _ fun z => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have htoReal : ∀ z : Torus d × Torus d,
      (ENNReal.ofReal (f z.1) * ENNReal.ofReal (f z.2)).toReal = f z.1 * f z.2 := fun z => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hfnn _), ENNReal.toReal_ofReal (hfnn _)]
  have hJff := mx_J_integrable (μ := μ) hI hfm hfm hfb hfb
  have hνν : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (ν.prod ν) := by
    rw [hprod, integrable_withDensity_iff_integrable_smul' hDp hDplt]
    simpa [htoReal, smul_eq_mul] using hJff
  have hconv0 : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hI.integral_prod_left
  have hconv : Integrable (fun x => ∫ y, g (x - y) ∂μ) ν := by
    rw [hν, integrable_withDensity_iff_integrable_smul' hD (ae_of_all _ hDlt)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hfnn _)]
    exact hconv0.bdd_mul (c := 3 / 2) hfm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hfb x)
  obtain ⟨hint, hval⟩ := mx_integral_W_iid (g := g) (μ := μ) (ν := ν) hN hνν hconv
  refine ⟨hint, ?_⟩
  rw [hval]
  -- evaluate the three integrals
  have hb1 : ∀ x : Torus d, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  have hJf1 := mx_J_integrable (μ := μ) hI (φ := f) (ψ := fun _ => (1 : ℝ)) hfm measurable_const
    hfb hb1
  have hJf1' : Integrable (fun p : Torus d × Torus d => f p.1 * g (p.1 - p.2)) (μ.prod μ) := by
    simpa using hJf1
  have e1 : ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(ν.prod ν) = mxJ g μ f f := by
    rw [hprod, integral_withDensity_eq_integral_toReal_smul hDp hDplt]
    simp only [htoReal, smul_eq_mul, mxJ]
  have e2 : ∫ x, ∫ y, g (x - y) ∂μ ∂ν = mxJ g μ f (fun _ => 1) := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul hD (ae_of_all _ hDlt)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hfnn _)]
    unfold mxJ
    simp only [mul_one]
    rw [integral_prod _ hJf1']
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show f x * ∫ y, g (x - y) ∂μ = ∫ y, f x * g (x - y) ∂μ
    rw [integral_const_mul]
  have e3 : ∫ x, ∫ y, g (x - y) ∂μ ∂μ = mxJ g μ (fun _ => 1) (fun _ => 1) := by
    unfold mxJ
    simp only [one_mul]
    rw [integral_prod _ hI]
  rw [e1, e2, e3]
  -- expand
  have A1 : mxJ g μ f f = mxJ g μ (fun _ => 1) (fun _ => 1) + t * mxJ g μ b (fun _ => 1) +
      t * (mxJ g μ (fun _ => 1) b + t * mxJ g μ b b) := by
    rw [show mxJ g μ f f = mxJ g μ (fun x => 1 + t * b x) (fun x => 1 + t * b x) from rfl,
      mx_J_affine_right hI hb hfm hM hfb, mx_J_affine_left hI hb measurable_const hM hb1,
      mx_J_affine_left hI hb hb hM hM]
  have A2 : mxJ g μ f (fun _ => 1) = mxJ g μ (fun _ => 1) (fun _ => 1) +
      t * mxJ g μ b (fun _ => 1) :=
    mx_J_affine_left hI hb measurable_const hM hb1 t
  rw [A1, A2, mx_J_symm geven b]
  ring

end PartB

/-- **M3** (expectation of `N F_N(·; μ°)` under the mixture; TeX L6952-6962, "expected `N F_N`
bounded by a fixed quadratic integral").  With `g = periodicRiesz d s`, `J(φ,ψ) = ∬ φ(x)ψ(y)g(x-y) dμ°dμ°`:
`N F_N ∈ L¹(mix)` and `E_mix[N F_N] = -J(1,1)/2 + ((N-1)/(2N)) a₀² J(b,b)`; in particular
`E_mix[N F_N] ≤ -J(1,1)/2 + (a₀²/2) |J(b,b)|`, uniformly in `N`.  (The exact cancellation
`A_ν - 2B_ν + A_0 = c² J(b,b)` is done at the integrand level in `mx_energy_withDensity`.) -/
theorem mx_energy_mix (S : PreparedData d) {b : Torus d → ℝ} (hb : Measurable b) {M : ℝ}
    (hM : ∀ x, |b x| ≤ M) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) :
    Integrable (mxW S N) (mixturePrep S.μ0 b a₀ N) ∧
      ∫ X, mxW S N X ∂(mixturePrep S.μ0 b a₀ N) =
        -(1 / 2) * mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) (fun _ => 1) +
          (((N : ℝ) - 1) / (2 * N)) * a₀ ^ 2 *
            mxJ (periodicRiesz d S.s) S.μ0 b b := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hg : Measurable (periodicRiesz d S.s) := PoleCavityAux.measurable_periodicRiesz S.hd S.hs0 S.hsd
  have hgi : Integrable (periodicRiesz d S.s) :=
    KernelAux.integrable_periodicRiesz S.hd S.hs0 S.hsd
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hI := PreparationAux.integrable_pair_withDensity hg hgi S.ρ0 Mρ
    (fun x => (le_abs_self _).trans (hMρ x)) (ν := S.μ0) rfl
  have geven : ∀ x, periodicRiesz d S.s (-x) = periodicRiesz d S.s x := fun x =>
    periodicRiesz_neg x
  have hb0' : ∫ x, b x ∂S.μ0 = 0 := hb0
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have htb : ∀ x, |(a₀ / Real.sqrt N) * b x| ≤ 1 / 2 := fun x => by
    rw [← mul_div_right_comm, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    linarith [hB x]
  have htb' : ∀ x, |(-(a₀ / Real.sqrt N)) * b x| ≤ 1 / 2 := fun x => by
    rw [neg_mul, abs_neg]; exact htb x
  obtain ⟨Ip, Vp⟩ := mx_energy_withDensity (g := periodicRiesz d S.s) (μ := S.μ0) hg geven hI hb hM
    hb0' (a₀ / Real.sqrt N) htb hN
  obtain ⟨Im, Vm⟩ := mx_energy_withDensity (g := periodicRiesz d S.s) (μ := S.μ0) hg geven hI hb hM
    hb0' (-(a₀ / Real.sqrt N)) htb' hN
  have ep : ∀ x, 1 + a₀ * b x / Real.sqrt N = 1 + (a₀ / Real.sqrt N) * b x := fun x => by ring
  have em : ∀ x, 1 - a₀ * b x / Real.sqrt N = 1 + (-(a₀ / Real.sqrt N)) * b x := fun x => by ring
  have hmix : mixturePrep S.μ0 b a₀ N =
      (1 / 2 : ℝ≥0∞) • Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (a₀ / Real.sqrt N) * b x)) +
      (1 / 2 : ℝ≥0∞) • Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (-(a₀ / Real.sqrt N)) * b x)) := by
    unfold mixturePrep
    simp only [ep, em]
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hhalf' : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    simp [ENNReal.toReal_inv]
  have Ip' : Integrable (mxW S N) (Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (a₀ / Real.sqrt N) * b x))) := Ip
  have Im' : Integrable (mxW S N) (Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (-(a₀ / Real.sqrt N)) * b x))) := Im
  refine ⟨?_, ?_⟩
  · rw [hmix]
    exact (Ip'.smul_measure hhalf).add_measure (Im'.smul_measure hhalf)
  · rw [hmix, integral_add_measure (Ip'.smul_measure hhalf) (Im'.smul_measure hhalf),
      integral_smul_measure, integral_smul_measure, hhalf']
    have Vp' : ∫ X, mxW S N X ∂(Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (a₀ / Real.sqrt N) * b x))) =
        -(1 / 2) * mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) (fun _ => 1) -
          (a₀ / Real.sqrt N) * mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) b +
          (((N : ℝ) - 1) / 2) * (a₀ / Real.sqrt N) ^ 2 * mxJ (periodicRiesz d S.s) S.μ0 b b := Vp
    have Vm' : ∫ X, mxW S N X ∂(Measure.pi (fun _ : Fin N =>
        S.μ0.withDensity fun x => ENNReal.ofReal (1 + (-(a₀ / Real.sqrt N)) * b x))) =
        -(1 / 2) * mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) (fun _ => 1) -
          (-(a₀ / Real.sqrt N)) * mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) b +
          (((N : ℝ) - 1) / 2) * (-(a₀ / Real.sqrt N)) ^ 2 * mxJ (periodicRiesz d S.s) S.μ0 b b := Vm
    rw [Vp', Vm']
    have hsq : (a₀ / Real.sqrt N) ^ 2 = a₀ ^ 2 / N := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hNne : (N : ℝ) ≠ 0 := by positivity
    simp only [smul_eq_mul, neg_sq, hsq]
    field_simp
    ring

end Main

end HRS
