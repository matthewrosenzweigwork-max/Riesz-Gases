import HRS.MC.S7E0a
import HRS.MC.S7W1

/-!
# Packet `s7_E0b_chaos_exists`: the second-chaos limit exists

Route.  (1) `H_ij = <h, e_i (x) e_j>_{L^2(mu x mu)}` and the Bessel inequality for the orthonormal family
`e_i (x) e_j` give `sum H_ij^2 < infinity`.  (2) By the Isserlis identity `s7_W1_isserlis_proof`, a finite
combination `sum a_ij (G_i G_j - C_ij)` has second moment `Q(a) + Q'(a) <= 2 Q(a) <= 2 lam^2 sum a_ij^2`
with `lam = ||R||`, where `Q(a) = sum a_ij a_kl C_ik C_jl` is the quadratic form of the Kronecker square of
the positive semidefinite matrix `C_n` (`lam I - C_n` is positive semidefinite).  (3) Hence the finite
sections are Cauchy in `L^2(P)`; take the limit in `Lp` and a measurable representative.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix Kronecker

noncomputable section

namespace HRS.MC.Sec7.E0b

open HRS HRS.Sec7

variable {d : ℕ} {ρ : Torus d → ℝ}

/-- the coefficients `H_ij = iint h e_i e_j dmu dmu` -/
def e0bH (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) (h : Torus d → Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)

theorem e0b_tensor_memLp {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f g : Torus d → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun z : Torus d × Torus d => f z.1 * g z.2) 2 (μ.prod μ) := by
  have hm : AEStronglyMeasurable (fun z : Torus d × Torus d => f z.1 * g z.2) (μ.prod μ) :=
    by
      have h1 : AEStronglyMeasurable (fun z : Torus d × Torus d => f z.1) (μ.prod μ) :=
        hf.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun z : Torus d × Torus d => g z.2) (μ.prod μ) :=
        hg.aestronglyMeasurable.comp_snd
      exact h1.mul h2
  rw [memLp_two_iff_integrable_sq hm]
  have := (hf.integrable_sq).mul_prod (hg.integrable_sq) (ν := μ)
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [mul_pow]

theorem e0b_bessel (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) {h : Torus d → Torus d → ℝ}
    (hL2 : MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) :
    Summable fun p : ℕ × ℕ => (e0bH ρ e h p.1 p.2) ^ 2 := by
  have := isProb_withDensityReal hρ.density
  set μ := withDensityReal ρ with hμ
  have wmem : ∀ i j, MemLp (fun z : Torus d × Torus d => e i z.1 * e j z.2) 2 (μ.prod μ) :=
    fun i j => e0b_tensor_memLp (he.memLp i) (he.memLp j)
  set W : ℕ × ℕ → Lp ℝ 2 (μ.prod μ) := fun p => (wmem p.1 p.2).toLp _ with hW
  set f : Lp ℝ 2 (μ.prod μ) := hL2.toLp _ with hf
  have hon : Orthonormal ℝ W := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, j⟩ ⟨k, l⟩
    rw [MeasureTheory.L2.inner_def]
    have h1 : ∀ᵐ z ∂(μ.prod μ), inner ℝ ((W (i, j)) z) ((W (k, l)) z) =
        (e i z.1 * e k z.1) * (e j z.2 * e l z.2) := by
      filter_upwards [MemLp.coeFn_toLp (wmem i j), MemLp.coeFn_toLp (wmem k l)] with z h1 h2
      simp only [hW, h1, h2, RCLike.inner_apply, conj_trivial]
      ring
    rw [integral_congr_ae h1, integral_prod_mul (fun x => e i x * e k x) (fun y => e j y * e l y)]
    have o1 := he.orthonormal i k
    have o2 := he.orthonormal j l
    unfold l2Inner at o1 o2
    rw [o1, o2]
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl, Prod.ext_iff]
  have key : ∀ p : ℕ × ℕ, inner ℝ (W p) f = e0bH ρ e h p.1 p.2 := by
    rintro ⟨i, j⟩
    rw [MeasureTheory.L2.inner_def]
    have hint : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2)) (μ.prod μ) :=
      (hL2.integrable_mul (wmem i j))
    have h1 : ∀ᵐ z ∂(μ.prod μ), inner ℝ ((W (i, j)) z) (f z) =
        h z.1 z.2 * (e i z.1 * e j z.2) := by
      filter_upwards [MemLp.coeFn_toLp (wmem i j), MemLp.coeFn_toLp hL2] with z h1 h2
      simp only [hW, hf, h1, h2, RCLike.inner_apply, conj_trivial]
      simp [Function.uncurry]
    rw [integral_congr_ae h1, integral_prod _ hint]
    unfold e0bH
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc]
  have := hon.inner_products_summable f
  refine this.congr fun p => ?_
  rw [key, Real.norm_eq_abs, sq_abs]


/-! ### Linear algebra: the Kronecker square of a bounded positive semidefinite matrix -/

section Kron

variable {N : ℕ}

theorem e0b_kron_quad (M : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → Fin N → ℝ) :
    star (fun p : Fin N × Fin N => a p.1 p.2) ⬝ᵥ (M ⊗ₖ M) *ᵥ (fun p : Fin N × Fin N => a p.1 p.2) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (M i k * M j l) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, star_trivial, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem e0b_kron_nonneg {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.PosSemidef) (a : Fin N → Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (M i k * M j l) := by
  rw [← e0b_kron_quad]
  exact (hM.kronecker hM).dotProduct_mulVec_nonneg _

theorem e0b_kron_le {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (hD : (lam • (1 : Matrix (Fin N) (Fin N) ℝ) - C).PosSemidef) (a : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i k * C j l) ≤ lam ^ 2 * ∑ i, ∑ j, a i j ^ 2 := by
  set D : Matrix (Fin N) (Fin N) ℝ := lam • (1 : Matrix (Fin N) (Fin N) ℝ) - C with hDdef
  have e : (lam ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ) - C ⊗ₖ C =
      lam • (D ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℝ)) + C ⊗ₖ D := by
    rw [← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [hDdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul]
    ring
  have hM : ((lam ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ) - C ⊗ₖ C).PosSemidef := by
    rw [e]
    exact ((hD.kronecker Matrix.PosSemidef.one).smul hlam).add (hC.kronecker hD)
  have h0 := hM.dotProduct_mulVec_nonneg (fun p : Fin N × Fin N => a p.1 p.2)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    e0b_kron_quad] at h0
  have h1 : star (fun p : Fin N × Fin N => a p.1 p.2) ⬝ᵥ (fun p : Fin N × Fin N => a p.1 p.2) =
      ∑ i, ∑ j, a i j ^ 2 := by
    simp only [dotProduct, star_trivial, Fintype.sum_prod_type, sq]
  rw [h1] at h0
  simp only [smul_eq_mul] at h0
  linarith

theorem e0b_sum_swap_ij (F : Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ j, ∑ k, ∑ l, F j i k l := by
  rw [Finset.sum_comm]

theorem e0b_sum_swap_kl (F : Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ j, ∑ k, ∑ l, F i j l k := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem e0b_cross_le {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (a : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i l * C j k) ≤
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i k * C j l) := by
  have h := e0b_kron_nonneg hC (fun i j => a i j - a j i)
  have hsym : ∀ i k : Fin N, C i k = C k i := fun i k => by
    have := hC.isHermitian.apply k i
    simpa using this
  have e2 : ∑ i, ∑ j, ∑ k, ∑ l, a i j * a l k * (C i k * C j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i l * C j k) := by
    rw [e0b_sum_swap_kl]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, a j i * a k l * (C i k * C j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i l * C j k) := by
    rw [e0b_sum_swap_ij]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hsym j k, hsym i l]; ring
  have e4 : ∑ i, ∑ j, ∑ k, ∑ l, a j i * a l k * (C i k * C j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i k * C j l) := by
    rw [e0b_sum_swap_ij, e0b_sum_swap_kl]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hsym j l, hsym i k]; ring
  have e : ∑ i, ∑ j, ∑ k, ∑ l, (a i j - a j i) * (a k l - a l k) * (C i k * C j l) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i k * C j l) -
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a l k * (C i k * C j l) -
      ∑ i, ∑ j, ∑ k, ∑ l, a j i * a k l * (C i k * C j l) +
      ∑ i, ∑ j, ∑ k, ∑ l, a j i * a l k * (C i k * C j l) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e, e2, e3, e4] at h
  linarith

end Kron


/-! ### Second moments of the finite sections -/

section Var

variable {s β : ℝ} {e : ℕ → Torus d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {G : ℕ → Ω → ℝ}

theorem e0b_memLp4 (hG : s7_GaussData d s β ρ e P G) (a : ℕ) : MemLp (G a) 4 P := by
  obtain ⟨hmeas, hlaw⟩ := hG
  set M := multivariateGaussian (0 : EuclideanSpace ℝ (Fin (a + 1)))
    (Matrix.of fun i j : Fin (a + 1) =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) with hM
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun b : Fin (a + 1) => G b ω :
      EuclideanSpace ℝ (Fin (a + 1)))) :=
    (MeasurableEquiv.toLp 2 (Fin (a + 1) → ℝ)).measurable.comp (Measurable.of_eval fun b => hmeas b)
  have h1 : MemLp (fun z : EuclideanSpace ℝ (Fin (a + 1)) => z (Fin.last a)) 4 M := by
    have := W1.w1_memLp4 (C := Matrix.of fun i j : Fin (a + 1) =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) (Pi.single (Fin.last a) 1)
    have e1 : Q08.q08c_ch_lin (Pi.single (Fin.last a) (1 : ℝ) : Fin (a + 1) → ℝ) =
        fun z : EuclideanSpace ℝ (Fin (a + 1)) => z (Fin.last a) :=
      funext (W1.w1_coord _)
    rw [e1] at this
    exact this
  have h2 := hlaw (a + 1)
  rw [← hM] at h2
  unfold law at h2
  have h3 : MemLp (fun z : EuclideanSpace ℝ (Fin (a + 1)) => z (Fin.last a)) 4
      (Measure.map (fun ω => (WithLp.toLp 2 fun b : Fin (a + 1) => G b ω :
        EuclideanSpace ℝ (Fin (a + 1)))) P) := by
    rw [h2]; exact h1
  have h4 := (memLp_map_measure_iff h3.aestronglyMeasurable hV.aemeasurable).1 h3
  convert h4 using 1
  funext ω; rfl

theorem e0b_X_memLp2 (hG4 : ∀ a, MemLp (G a) 4 P) (c : ℝ) (i j : ℕ) :
    MemLp (fun ω => G i ω * G j ω - c) 2 P := by
  have h : MemLp (fun ω => G i ω * G j ω) 2 P := (hG4 i).mul (hG4 j) (r := 2)
  exact h.sub (memLp_const c)



theorem e0b_var_block (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbd : ∀ n : ℕ, ((lam • (1 : Matrix (Fin n) (Fin n) ℝ)) -
      Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef)
    (N : ℕ) (a : Fin N → Fin N → ℝ) :
    ∫ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e p.1) (e p.2))) ^ 2 ∂P ≤
      2 * lam ^ 2 * ∑ i, ∑ j, a i j ^ 2 := by
  have hG4 := e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  set C : ℕ → ℕ → ℝ := fun x y => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e x) (e y)
    with hCdef
  show ∫ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω - C p.1 p.2)) ^ 2 ∂P ≤ _
  have hY : ∀ p : Fin N × Fin N, MemLp (fun ω => G p.1 ω * G p.2 ω - C p.1 p.2) 2 P :=
    fun p => e0b_X_memLp2 hG4 _ _ _
  have hint : ∀ p q : Fin N × Fin N, Integrable (fun ω => (G p.1 ω * G p.2 ω - C p.1 p.2) *
      (G q.1 ω * G q.2 ω - C q.1 q.2)) P := fun p q => (hY p).integrable_mul (hY q)
  have hw : ∀ p q : Fin N × Fin N, ∫ ω, (G p.1 ω * G p.2 ω - C p.1 p.2) *
      (G q.1 ω * G q.2 ω - C q.1 q.2) ∂P = C p.1 q.1 * C p.2 q.2 + C p.1 q.2 * C p.2 q.1 :=
    fun p q => W1.s7_W1_isserlis_proof d s β ρ e P G hd hs0 hsd hβ hρ he hG p.1 p.2 q.1 q.2
  have hexp : ∀ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω - C p.1 p.2)) ^ 2 =
      ∑ p : Fin N × Fin N, ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) *
        ((G p.1 ω * G p.2 ω - C p.1 p.2) * (G q.1 ω * G q.2 ω - C q.1 q.2)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ fun q _ => (hint p q).const_mul _)]
  have : ∀ p ∈ (Finset.univ : Finset (Fin N × Fin N)),
      ∫ ω, ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) *
        ((G p.1 ω * G p.2 ω - C p.1 p.2) * (G q.1 ω * G q.2 ω - C q.1 q.2)) ∂P =
      ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) * (C p.1 q.1 * C p.2 q.2 + C p.1 q.2 * C p.2 q.1) := by
    intro p _
    rw [integral_finset_sum _ (fun q _ => (hint p q).const_mul _)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, hw]
  rw [Finset.sum_congr rfl this]
  set CN : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j : Fin N => C i j with hCN
  have hPSD : CN.PosSemidef := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he N
  have e1 := e0b_kron_le hPSD hlam (hbd N) a
  have e2 := e0b_cross_le hPSD a
  simp only [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
  simp only [hCN, Matrix.of_apply] at e1 e2
  have e3 : ∀ i j k l : Fin N, a i j * a k l * (C i l * C j k) = a i j * a k l * (C i l * C j k) := fun _ _ _ _ => rfl
  linarith


/-! ### Range-indexed variance bound and increments -/

theorem e0b_var_range (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbd : ∀ n : ℕ, ((lam • (1 : Matrix (Fin n) (Fin n) ℝ)) -
      Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef)
    (N : ℕ) (a : ℕ → ℕ → ℝ) :
    ∫ ω, (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ^ 2 ∂P ≤
      2 * lam ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j ^ 2 := by
  have := e0b_var_block hd hs0 hsd hβ hρ he hG hlam hbd N (fun i j => a i j)
  simp only [Fintype.sum_prod_type] at this
  simp only [Finset.sum_range]
  exact this

theorem e0b_split (F : ℕ → ℕ → ℝ) (L L' : ℕ) (h : L ≤ L') :
    ∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L', F i j =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, F i j +
      ∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L',
        (if ¬ (i < L ∧ j < L) then F i j else 0) := by
  simp only [← Finset.sum_product']
  have h1 : ∑ p ∈ Finset.range L ×ˢ Finset.range L, F p.1 p.2 =
      ∑ p ∈ (Finset.range L' ×ˢ Finset.range L').filter (fun p => p.1 < L ∧ p.2 < L),
        F p.1 p.2 := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨i, j⟩
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    omega
  rw [h1, ← Finset.sum_filter (fun p : ℕ × ℕ => ¬ (p.1 < L ∧ p.2 < L)) (fun p => F p.1 p.2)]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm


theorem e0b_var_diff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbd : ∀ n : ℕ, ((lam • (1 : Matrix (Fin n) (Fin n) ℝ)) -
      Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef)
    (H : ℕ → ℕ → ℝ) {L L' : ℕ} (hLL : L ≤ L') :
    ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L', H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) -
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ^ 2 ∂P ≤
      lam ^ 2 / 2 * (∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L', H i j ^ 2 -
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2) := by
  set a : ℕ → ℕ → ℝ := fun i j => if ¬ (i < L ∧ j < L) then (1 / 2 : ℝ) * H i j else 0 with ha
  have hpt : ∀ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L', H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) -
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) =
      ∑ i ∈ Finset.range L', ∑ j ∈ Finset.range L', a i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) := by
    intro ω
    have := e0b_split (fun i j => (1 / 2 : ℝ) * (H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)))) L L' hLL
    simp only [← Finset.mul_sum] at this
    have h2 : ∀ i j : ℕ, a i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) =
        (if ¬ (i < L ∧ j < L) then (1 / 2 : ℝ) * (H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) else 0) := by
      intro i j
      simp only [ha]
      split_ifs <;> ring
    simp only [h2]
    linarith [this]
  simp only [hpt]
  refine (e0b_var_range hd hs0 hsd hβ hρ he hG hlam hbd L' a).trans ?_
  have h3 := e0b_split (fun i j => (1 / 4 : ℝ) * H i j ^ 2) L L' hLL
  simp only [← Finset.mul_sum] at h3
  have h4 : ∀ i j : ℕ, a i j ^ 2 =
      (if ¬ (i < L ∧ j < L) then (1 / 4 : ℝ) * H i j ^ 2 else 0) := by
    intro i j
    simp only [ha]
    split_ifs <;> ring
  simp only [h4]
  have hl2 : 0 ≤ lam ^ 2 := sq_nonneg lam
  nlinarith [h3]

end Var

section Lim

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

theorem e0b_sq_eq {g : Ω → ℝ} (hg : MemLp g 2 P) :
    (eLpNorm g 2 P).toReal ^ 2 = ∫ ω, g ω ^ 2 ∂P := by
  have h := hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have h0 : 0 ≤ ∫ ω, |g ω| ^ (2 : ℝ) ∂P := integral_nonneg fun ω => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem e0b_lint_eq (g : Ω → ℝ) (hg : AEStronglyMeasurable g P) :
    ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P = eLpNorm g 2 P ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := 2) (by norm_num) hg
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at this
  rw [← this]
  simp

theorem e0b_limit (S : ℕ → Ω → ℝ) (hS : ∀ L, MemLp (S L) 2 P)
    (t : ℕ → ℝ) {T : ℝ} (ht : Tendsto t atTop (𝓝 T)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ L L' : ℕ, L ≤ L' → ∫ ω, (S L' ω - S L ω) ^ 2 ∂P ≤ K * (t L' - t L)) :
    ∃ Q : Ω → ℝ, Measurable Q ∧
      Tendsto (fun L : ℕ => ∫⁻ ω, ‖Q ω - S L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  set f : ℕ → Lp ℝ 2 P := fun L => (hS L).toLp (S L) with hf
  have hd : ∀ L L' : ℕ, L ≤ L' → dist (f L') (f L) ^ 2 ≤ K * (t L' - t L) := by
    intro L L' hLL
    have h1 : dist (f L') (f L) = (eLpNorm (S L' - S L) 2 P).toReal := by
      rw [dist_eq_norm, hf]
      simp only
      rw [← MemLp.toLp_sub (hS L') (hS L), Lp.norm_toLp]
    rw [h1, e0b_sq_eq ((hS L').sub (hS L))]
    simpa using hb L L' hLL
  have hcau : CauchySeq f := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 ht.cauchySeq (ε ^ 2 / (K + 1)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hd N n hn
    rw [Real.dist_eq] at h1
    have h3 : K * (t n - t N) ≤ K * (ε ^ 2 / (K + 1)) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h1.le) hK
    have h4 : K * (ε ^ 2 / (K + 1)) < ε ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [pow_pos hε 2]
    by_contra hcon
    push_neg at hcon
    nlinarith [dist_nonneg (x := f n) (y := f N)]
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨F, (Lp.stronglyMeasurable F).measurable, ?_⟩
  have h5 : ∀ L, ∫⁻ ω, ‖F ω - S L ω‖ₑ ^ 2 ∂P = ENNReal.ofReal ‖F - f L‖ ^ 2 := by
    intro L
    have hae : (⇑(F - f L) : Ω → ℝ) =ᵐ[P] fun ω => F ω - S L ω := by
      filter_upwards [Lp.coeFn_sub F (f L), (hS L).coeFn_toLp] with ω h1 h2
      rw [h1]; simp only [Pi.sub_apply, hf] at *; rw [h2]
    refine (e0b_lint_eq (fun ω => (F : Ω → ℝ) ω - S L ω)
      ((Lp.aestronglyMeasurable F).sub (hS L).aestronglyMeasurable)).trans ?_
    rw [← eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp_rw [h5]
  have h6 : Tendsto (fun L => ‖F - f L‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hF)
    simpa [norm_sub_rev] using this
  have h7 : Tendsto (fun L => ENNReal.ofReal ‖F - f L‖) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal h6
    rwa [ENNReal.ofReal_zero] at this
  have h8 := ((ENNReal.continuous_pow 2).tendsto 0).comp h7
  rwa [zero_pow two_ne_zero] at h8

end Lim


/-! ### The packet -/

theorem s7_E0b_chaos_exists_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ) (hG : s7_GaussData d s β ρ e P G)
    (h : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hL2 : MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) :
    ∃ Q : Ω → ℝ, Measurable Q ∧ s7_IsChaosLimit d s β ρ e P G h Q := by
  obtain ⟨lam, hlam, hbd⟩ := E0a.s7e_cov_bdd hd hs0 hsd hβ hρ he
  have hG4 := e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  have hsum := e0b_bessel hρ he hL2
  set H : ℕ → ℕ → ℝ := e0bH ρ e h with hH
  set S : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω -
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) with hSdef
  have hS : ∀ L, MemLp (S L) 2 P := by
    intro L
    refine MemLp.const_mul ?_ _
    refine memLp_finset_sum _ fun i _ => memLp_finset_sum _ fun j _ => ?_
    exact (e0b_X_memLp2 hG4 _ i j).const_mul _
  set t : ℕ → ℝ := fun L => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 with htdef
  have ht : Tendsto t atTop (𝓝 (∑' p : ℕ × ℕ, (H p.1 p.2) ^ 2)) := by
    have h1 : Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) atTop atTop := by
      refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun p => ?_)
      · exact Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
      · exact ⟨max p.1 p.2 + 1, by
          simp only [Finset.mem_product, Finset.mem_range]; omega⟩
    have h2 := hsum.hasSum.comp h1
    refine Tendsto.congr (fun N => ?_) h2
    simp only [Function.comp_apply, htdef]
    rw [Finset.sum_product' (f := fun i j => H i j ^ 2)]
  obtain ⟨Q, hQm, hQ⟩ := e0b_limit S hS t ht (K := lam ^ 2 / 2) (by positivity) (fun L L' hLL => by
    have := e0b_var_diff hd hs0 hsd hβ hρ he hG hlam hbd H hLL
    exact this)
  exact ⟨Q, hQm, hQ⟩

end HRS.MC.Sec7.E0b
