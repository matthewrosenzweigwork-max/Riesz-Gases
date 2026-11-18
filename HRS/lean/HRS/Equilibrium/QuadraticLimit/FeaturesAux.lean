import HRS.Equilibrium.QuadraticLimit.Spectral
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.CalibratedReference

/-!
# Lemma 7.5: auxiliary lemmas for the `Features` sub-packet (prefix `q08f_`)

Bookkeeping for `Q08Data`: the kernel `h` satisfies the row bounds of `RowOK`, the pressure bounds of
Proposition 5.5 hold on an arbitrary compact interval of inverse temperatures for `N ≥ 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

variable {d : ℕ}

theorem q08f_hd1 (D : Q08Data d) : 1 ≤ d := by have := D.hd; omega

theorem q08f_hsd (D : Q08Data d) : D.s < d := by
  have := D.hs; have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith

theorem q08f_atomless (D : Q08Data d) (x : Torus d) : D.μ {x} = 0 :=
  HRS.External.Calib.atomless_withDensityReal (q08f_hd1 D) D.ρ x

/-- The kernel `h` with its diagonal set to `0`. -/
def Q08Data.q08f_h' (D : Q08Data d) (x y : Torus d) : ℝ := if x = y then 0 else D.h x y

theorem q08f_h'_meas (D : Q08Data d) : Measurable (Function.uncurry D.q08f_h') := by
  have hD : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} := isClosed_diagonal.measurableSet
  unfold Q08Data.q08f_h'
  exact Measurable.ite hD measurable_const D.hmeas

theorem q08f_h'_symm (D : Q08Data d) (x y : Torus d) : D.q08f_h' x y = D.q08f_h' y x := by
  unfold Q08Data.q08f_h'
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h, D.hsymm x y]

theorem q08f_density_bound (D : Q08Data d) : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x, D.ρ x ≤ Λ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := HRS.PoleCavityAux.exists_density_bound D.hρ
  exact ⟨Λ, hΛ0.le, hΛ⟩

/-- Constants making the diagonal-zeroed kernel dominated everywhere. -/
theorem q08f_h'_dom (D : Q08Data d) :
    ∃ cs : ℝ, (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + cs) ∧
      ∀ x y, |D.q08f_h' x y| ≤ max D.B 0 * (periodicRiesz d D.s (x - y) + cs) := by
  refine ⟨max D.c |periodicRiesz d D.s 0|, fun z hz => ?_, fun x y => ?_⟩
  · linarith [D.hc z hz, le_max_left D.c |periodicRiesz d D.s 0|]
  · unfold Q08Data.q08f_h'
    by_cases h : x = y
    · subst h
      simp only [↓reduceIte, abs_zero, sub_self]
      have : 0 ≤ periodicRiesz d D.s 0 + max D.c |periodicRiesz d D.s 0| := by
        have := le_max_right D.c |periodicRiesz d D.s 0|
        have := neg_abs_le (periodicRiesz d D.s 0)
        linarith
      exact mul_nonneg (le_max_right _ _) this
    · simp only [h, ↓reduceIte]
      have hz : x - y ≠ 0 := sub_ne_zero.2 h
      have h1 := D.hB x y h
      have h2 := D.hc (x - y) hz
      have hcs : D.c ≤ max D.c |periodicRiesz d D.s 0| := le_max_left _ _
      have hpos : 0 ≤ periodicRiesz d D.s (x - y) + D.c := by linarith
      calc |D.h x y| ≤ D.B * (periodicRiesz d D.s (x - y) + D.c) := h1
        _ ≤ max D.B 0 * (periodicRiesz d D.s (x - y) + D.c) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        _ ≤ max D.B 0 * (periodicRiesz d D.s (x - y) + max D.c |periodicRiesz d D.s 0|) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

theorem q08f_rowOK_h' (D : Q08Data d) : RowOK D.μ D.q08f_h' := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := q08f_density_bound D
  obtain ⟨cs, hw, hdom⟩ := q08f_h'_dom D
  have := (rowOK_g_h (q08f_hd1 D) D.s D.hs0 (q08f_hsd D) cs hw (max D.B 0) hΛ0 hΛ
    (q08f_h'_meas D) hdom).2
  exact this


theorem q08f_row_ae (D : Q08Data d) (x : Torus d) : D.h x =ᵐ[D.μ] D.q08f_h' x := by
  have : ∀ᵐ y ∂D.μ, y ≠ x := by
    rw [ae_iff]
    simpa using q08f_atomless D x
  filter_upwards [this] with y hy
  simp [Q08Data.q08f_h', Ne.symm hy]

theorem q08f_rowOK_h (D : Q08Data d) : RowOK D.μ D.h where
  meas := D.hmeas
  int x := ((q08f_rowOK_h' D).int x).congr (q08f_row_ae D x).symm
  bound := by
    obtain ⟨M, hM⟩ := (q08f_rowOK_h' D).bound
    refine ⟨M, fun x => ?_⟩
    have : ∫ y, |D.h x y| ∂D.μ = ∫ y, |D.q08f_h' x y| ∂D.μ :=
      integral_congr_ae (by filter_upwards [q08f_row_ae D x] with y hy; simp only [hy])
    rw [this]
    exact hM x

theorem q08f_rowOK_g (D : Q08Data d) :
    RowOK D.μ (fun x y => periodicRiesz d D.s (x - y)) :=
  haveI := q08_isProb_μ D
  ProdTransfer.rowOK_kernel (by have := D.hd; omega) D.hs0 (q08f_hsd D) D.hρ

/-! ### Pressure bounds on an arbitrary interval of inverse temperatures, all `N ≥ 1` -/

open ProdTransfer in
theorem q08f_pressure_N2 (D : Q08Data d) (βm βp : ℝ) (hβm : 0 < βm) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc βm βp,
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d D.s N))) ≤ Jint d D.s N b D.μ ∧
        Jint d D.s N b D.μ ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := by
  have hd := D.hd
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd D.hs0 (q08f_hsd D)
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (B + 1) :=
    fun z _ => by linarith [hB z]
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (PoleCavityAux.continuous_of_smoothPos D.hρ).continuousOn
  have hc₀ : 0 < D.ρ x0 := D.hρ.pos x0
  have hlow : ∀ x, D.ρ x0 ≤ D.ρ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  obtain ⟨θ₀, θ₁, C, hθ₀, hθ₁, H⟩ := perturbed_pressure (by omega) D.s D.hs0 (q08f_hsd D) (B + 1) hw βm
    βp hβm (D.ρ x0) hc₀ (fun k => Torus.cbNorm k D.ρ) 0
  refine ⟨C, fun N hN b hb => ?_⟩
  have := (H D.ρ D.hρ.density D.hρ.smooth hlow (fun k => le_rfl) (fun _ _ => 0) measurable_const
    (fun _ _ => rfl) (fun x y => by simp) N hN b hb).1 0 (by simp [hθ₀.le])
  simpa [Jint, modulatedEnergyKernel, Q08Data.μ] using this


open ProdTransfer in
theorem q08f_pressure_N1 (D : Q08Data d) (βm βp : ℝ) (hβm : 0 < βm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Set.Icc βm βp,
      ENNReal.ofReal (Real.exp (-C)) ≤ Jint d D.s 1 b D.μ ∧
        Jint d D.s 1 b D.μ ≤ ENNReal.ofReal (Real.exp C) := by
  have : IsProbabilityMeasure (withDensityReal D.ρ) := q08_isProb_μ D
  obtain ⟨B, Cc, hB, hK⟩ := PoleCavityAux.kerData_periodicRiesz (by have := D.hd; omega) D.hs0 (q08f_hsd D) D.hρ
  have hCc := hK.Cc_nonneg
  have hE : ∀ X : Config d 1, |modulatedEnergyKernel (periodicRiesz d D.s) X D.μ| ≤ 3 * Cc := by
    intro X
    unfold modulatedEnergyKernel modulatedEnergy
    have h0 : Finset.univ.erase (0 : Fin 1) = ∅ := by
      ext j; simp [Subsingleton.elim j 0]
    have hsum : ∀ i : Fin 1, Finset.univ.erase i = ∅ := fun i => by
      rw [Subsingleton.elim i 0]; exact h0
    simp only [hsum, Finset.sum_empty, mul_zero, zero_sub, Nat.cast_one, div_one, one_div, inv_one,
      one_mul, Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton]
    have h1 : |∫ y, periodicRiesz d D.s (X default - y) ∂D.μ| ≤ Cc := hK.conv _
    have h2 : |∫ x, ∫ y, periodicRiesz d D.s (x - y) ∂D.μ ∂D.μ| ≤ Cc := by
      have := norm_integral_le_of_norm_le_const (μ := D.μ)
        (f := fun x => ∫ y, periodicRiesz d D.s (x - y) ∂D.μ) (C := Cc)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK.conv x)
      simpa using this
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨6 * max βp 0 * Cc, by positivity, fun b hb => ?_⟩
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hbp : b ≤ max βp 0 := hb.2.trans (le_max_left _ _)
  have hbd : ∀ X : Config d 1, |-b * ((1 : ℕ) : ℝ) *
      modulatedEnergyKernel (periodicRiesz d D.s) X D.μ| ≤ 6 * max βp 0 * Cc := by
    intro X
    have := hE X
    calc |-b * ((1 : ℕ) : ℝ) * modulatedEnergyKernel (periodicRiesz d D.s) X D.μ|
        = b * |modulatedEnergyKernel (periodicRiesz d D.s) X D.μ| := by
          simp [abs_mul, abs_of_nonneg hb0]
      _ ≤ (2 * max βp 0) * (3 * Cc) := mul_le_mul (by linarith [le_max_right βp 0]) this
          (abs_nonneg _) (by positivity)
      _ = 6 * max βp 0 * Cc := by ring
  constructor
  · calc ENNReal.ofReal (Real.exp (-(6 * max βp 0 * Cc)))
        = ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (-(6 * max βp 0 * Cc)))
            ∂(Measure.pi fun _ => D.μ) := by simp
      _ ≤ _ := lintegral_mono fun X => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
  · calc _ ≤ ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (6 * max βp 0 * Cc))
            ∂(Measure.pi fun _ => D.μ) :=
          lintegral_mono fun X => ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
      _ = _ := by simp


open ProdTransfer in
theorem q08f_pressure_all (D : Q08Data d) (βm βp : ℝ) (hβm : 0 < βm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc βm βp,
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d D.s N))) ≤ Jint d D.s N b D.μ ∧
        Jint d D.s N b D.μ ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := by
  obtain ⟨C2, h2⟩ := q08f_pressure_N2 D βm βp hβm
  obtain ⟨C1, hC1, h1⟩ := q08f_pressure_N1 D βm βp hβm
  refine ⟨max (max C2 0) C1, (le_max_left _ _).trans' (le_max_right _ _), fun N hN b hb => ?_⟩
  have hNd := one_le_mul_deltaN (d := d) D.hs0 N hN
  have hCnn : 0 ≤ max (max C2 0) C1 := (le_max_right C2 0).trans ((le_max_left _ _))
  have hCNd : max (max C2 0) C1 * N * deltaN d D.s N = max (max C2 0) C1 * ((N : ℝ) * deltaN d D.s N) := by ring
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN1 : N = 1 := by omega
    subst hN1
    obtain ⟨hl, hu⟩ := h1 b hb
    have hCle : C1 ≤ max (max C2 0) C1 * (((1 : ℕ) : ℝ) * deltaN d D.s 1) :=
      (le_max_right _ _).trans (by nlinarith [le_max_right (max C2 0) C1])
    refine ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
    · rw [hCNd]; linarith
    · rw [hCNd]; linarith
  · obtain ⟨hl, hu⟩ := h2 N h b hb
    have hC2le : C2 ≤ max (max C2 0) C1 := (le_max_left _ _).trans (le_max_left _ _)
    have hmono : C2 * N * deltaN d D.s N ≤ max (max C2 0) C1 * N * deltaN d D.s N := by
      have : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
      nlinarith
    exact ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hmono))⟩

/-- For `s < d/2`, `N δ_N = 1`. -/
theorem q08f_mul_deltaN (D : Q08Data d) (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) * deltaN d D.s N = 1 := by
  unfold deltaN
  rw [if_pos D.hs]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- Pressure bounds with `N δ_N = 1`. -/
theorem q08f_pressure (D : Q08Data d) (βm βp : ℝ) (hβm : 0 < βm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc βm βp,
      ENNReal.ofReal (Real.exp (-C)) ≤ ProdTransfer.Jint d D.s N b D.μ ∧
        ProdTransfer.Jint d D.s N b D.μ ≤ ENNReal.ofReal (Real.exp C) := by
  obtain ⟨C, hC, H⟩ := q08f_pressure_all D βm βp hβm
  refine ⟨C, hC, fun N hN b hb => ?_⟩
  have := H N hN b hb
  have e : C * N * deltaN d D.s N = C := by
    rw [mul_assoc, q08f_mul_deltaN D N hN, mul_one]
  rwa [e] at this


/-! ### Gibbs law: probability, density -/

/-- Measurability of the energy with the periodic Riesz kernel. -/
theorem q08f_measurable_energyKernel (D : Q08Data d) (N : ℕ) :
    Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d D.s) X D.μ) := by
  haveI := q08_isProb_μ D
  exact measurable_modulatedEnergy (q08f_rowOK_g D)

theorem q08f_jint_ne (D : Q08Data d) (N : ℕ) (hN : 1 ≤ N) :
    ProdTransfer.Jint d D.s N D.β D.μ ≠ 0 ∧ ProdTransfer.Jint d D.s N D.β D.μ ≠ ∞ := by
  obtain ⟨C, hC0, H⟩ := q08f_pressure D D.β D.β D.hβ
  obtain ⟨h1, h2⟩ := H N hN D.β ⟨le_rfl, le_rfl⟩
  refine ⟨?_, ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2⟩
  intro h0
  rw [h0] at h1
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos (-C))).ne' (le_antisymm h1 bot_le)

theorem q08f_gibbs_facts (D : Q08Data d) (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (gibbsNormalizer (periodicRiesz d D.s) N D.β D.μ) =
        ProdTransfer.Jint d D.s N D.β D.μ ∧ IsProbabilityMeasure (D.Gibbs N) := by
  haveI := q08_isProb_μ D
  obtain ⟨h0, h1⟩ := q08f_jint_ne D N hN
  exact gibbs_facts (q08f_rowOK_g D) h0 h1

theorem q08f_gibbs_isProb (D : Q08Data d) (N : ℕ) (hN : 1 ≤ N) : IsProbabilityMeasure (D.Gibbs N) :=
  (q08f_gibbs_facts D N hN).2

open ProdTransfer in
theorem q08f_weight_Lq (D : Q08Data d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ((D.Gibbs N).rnDeriv (D.prodLaw N) X) ^ q ∂(D.prodLaw N) ≤ ENNReal.ofReal C := by
  have hβ := D.hβ
  have hq0 : 0 < q := by linarith
  have hβq : D.β ≤ q * D.β := by nlinarith
  obtain ⟨C, hC0, H⟩ := q08f_pressure D D.β (q * D.β) hβ
  refine ⟨Real.exp (C * q + C), fun N hN => ?_⟩
  haveI := q08_isProb_μ D
  set μN : Measure (Config d N) := D.prodLaw N with hμN
  set E : Config d N → ℝ := fun X => modulatedEnergyKernel (periodicRiesz d D.s) X D.μ with hE
  have hEm : Measurable E := q08f_measurable_energyKernel D N
  have hwm : ∀ b : ℝ, Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-b * N * E X))) :=
    fun b => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hEm))
  obtain ⟨hnorm, -⟩ := q08f_gibbs_facts D N hN
  haveI : IsProbabilityMeasure μN := by rw [hμN]; unfold Q08Data.prodLaw; infer_instance
  have hG : D.Gibbs N = (Jint d D.s N D.β D.μ)⁻¹ •
      μN.withDensity (fun X => ENNReal.ofReal (Real.exp (-D.β * N * E X))) := by
    unfold Q08Data.Gibbs modulatedGibbs
    rw [hnorm]
    rfl
  have hJne := q08f_jint_ne D N hN
  have hrn : (D.Gibbs N).rnDeriv μN =ᵐ[μN]
      fun X => (Jint d D.s N D.β D.μ)⁻¹ * ENNReal.ofReal (Real.exp (-D.β * N * E X)) := by
    rw [hG]
    haveI : IsFiniteMeasure (μN.withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-D.β * N * E X)))) := isFiniteMeasure_withDensity hJne.2
    have h1 := Measure.rnDeriv_smul_left_of_ne_top (μN.withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-D.β * N * E X)))) μN (r := (Jint d D.s N D.β D.μ)⁻¹)
      (ENNReal.inv_ne_top.2 hJne.1)
    have h2 := Measure.rnDeriv_withDensity μN (hwm D.β)
    filter_upwards [h1, h2] with X hX1 hX2
    rw [hX1, Pi.smul_apply, smul_eq_mul, hX2]
  obtain ⟨hl, -⟩ := H N hN D.β ⟨le_rfl, hβq⟩
  obtain ⟨-, hu⟩ := H N hN (q * D.β) ⟨hβq, le_rfl⟩
  have hpow : ∀ X : Config d N, (ENNReal.ofReal (Real.exp (-D.β * N * E X))) ^ q =
      ENNReal.ofReal (Real.exp (-(q * D.β) * N * E X)) := by
    intro X
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul]
    congr 2
    ring
  calc ∫⁻ X, ((D.Gibbs N).rnDeriv μN X) ^ q ∂μN
      = ∫⁻ X, ((Jint d D.s N D.β D.μ)⁻¹ * ENNReal.ofReal (Real.exp (-D.β * N * E X))) ^ q ∂μN :=
        lintegral_congr_ae (hrn.mono fun X hX => by dsimp only; rw [hX])
    _ = ((Jint d D.s N D.β D.μ)⁻¹) ^ q * Jint d D.s N (q * D.β) D.μ := by
        have : ∀ X : Config d N, ((Jint d D.s N D.β D.μ)⁻¹ *
            ENNReal.ofReal (Real.exp (-D.β * N * E X))) ^ q =
            ((Jint d D.s N D.β D.μ)⁻¹) ^ q * ENNReal.ofReal (Real.exp (-(q * D.β) * N * E X)) := by
          intro X
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, hpow]
        simp_rw [this]
        rw [lintegral_const_mul _ (hwm _)]
        rfl
    _ ≤ (ENNReal.ofReal (Real.exp C)) ^ q * ENNReal.ofReal (Real.exp C) := by
        gcongr
        · calc (Jint d D.s N D.β D.μ)⁻¹ ≤ (ENNReal.ofReal (Real.exp (-C)))⁻¹ := ENNReal.inv_le_inv.2 hl
            _ = ENNReal.ofReal (Real.exp C) := by
              rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
    _ = ENNReal.ofReal (Real.exp (C * q + C)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]


/-! ### Integrability of the energy under the Gibbs law -/

theorem q08f_energy_one_bdd {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {k : Torus d → Torus d → ℝ} (hk : RowOK μ k) :
    ∃ M : ℝ, ∀ X : Config d 1, |modulatedEnergy k X μ| ≤ M := by
  obtain ⟨M, hM⟩ := hk.bound
  refine ⟨M + M, fun X => ?_⟩
  unfold modulatedEnergy
  have h0 : Finset.univ.erase (0 : Fin 1) = ∅ := by
    ext j; simp [Subsingleton.elim j 0]
  have hsum : ∀ i : Fin 1, Finset.univ.erase i = ∅ := fun i => by
    rw [Subsingleton.elim i 0]; exact h0
  simp only [hsum, Finset.sum_empty, mul_zero, zero_sub, Nat.cast_one, div_one, one_div, inv_one,
    one_mul, Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton]
  have h1 : |∫ y, k (X default) y ∂μ| ≤ M := hk.abs_rowInt_le hM _
  have h2 : |∫ x, ∫ y, k x y ∂μ ∂μ| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => ∫ y, k x y ∂μ) (C := M)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hk.abs_rowInt_le hM x)
    simpa using this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem q08f_energy_ae (D : Q08Data d) (N : ℕ) :
    (fun X : Config d N => modulatedEnergy D.h X D.μ) =ᵐ[D.prodLaw N]
      fun X : Config d N => modulatedEnergy D.q08f_h' X D.μ := by
  haveI := q08_isProb_μ D
  filter_upwards [HRS.External.Calib.ae_distinct_pi (q08f_atomless D) N] with X hX
  have hrow : ∀ x, ∫ y, D.h x y ∂D.μ = ∫ y, D.q08f_h' x y ∂D.μ := fun x =>
    integral_congr_ae (q08f_row_ae D x)
  unfold modulatedEnergy
  have e1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, D.h (X i) (X j) =
      ∑ j ∈ Finset.univ.erase i, D.q08f_h' (X i) (X j) := by
    intro i
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have : X i ≠ X j := hX i j (Ne.symm hji)
    simp [Q08Data.q08f_h', this]
  simp_rw [e1, hrow]

open ProdTransfer in
theorem q08f_gibbs_ac (D : Q08Data d) (N : ℕ) : D.Gibbs N ≪ D.prodLaw N := by
  unfold Q08Data.Gibbs modulatedGibbs
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

theorem q08f_exp_moment (D : Q08Data d) :
    ∃ θ₁ C : ℝ, 0 < θ₁ ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N * |modulatedEnergy D.q08f_h' X D.μ|))
        ∂(D.Gibbs N) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := by
  have hd := D.hd
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd D.hs0 (q08f_hsd D)
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (B + 1) :=
    fun z _ => by linarith [hB z]
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (PoleCavityAux.continuous_of_smoothPos D.hρ).continuousOn
  have hc₀ : 0 < D.ρ x0 := D.hρ.pos x0
  have hlow : ∀ x, D.ρ x0 ≤ D.ρ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  obtain ⟨cs, hcs, hdom⟩ := q08f_h'_dom D
  have hw' : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + cs := hcs
  obtain ⟨θ₀, θ₁, C, hθ₀, hθ₁, H⟩ := perturbed_pressure (by omega) D.s D.hs0 (q08f_hsd D) cs hw' D.β
    D.β D.hβ (D.ρ x0) hc₀ (fun k => Torus.cbNorm k D.ρ) (max D.B 0)
  refine ⟨θ₁, C, hθ₁, fun N hN => ?_⟩
  have := (H D.ρ D.hρ.density D.hρ.smooth hlow (fun k => le_rfl) D.q08f_h' (q08f_h'_meas D)
    (q08f_h'_symm D) hdom N hN D.β ⟨le_rfl, le_rfl⟩).2.1
  exact this

theorem q08f_integrable_energy (D : Q08Data d) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => modulatedEnergy D.h X D.μ) (D.Gibbs N) := by
  haveI := q08_isProb_μ D
  haveI := q08f_gibbs_isProb D N hN
  have hmeas : Measurable (fun X : Config d N => modulatedEnergy D.h X D.μ) :=
    measurable_modulatedEnergy (q08f_rowOK_h D)
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN1 : N = 1 := by omega
    subst hN1
    obtain ⟨M, hM⟩ := q08f_energy_one_bdd (q08f_rowOK_h D)
    exact Integrable.of_bound hmeas.aestronglyMeasurable M (Filter.Eventually.of_forall fun X => by
      simpa using hM X)
  · obtain ⟨θ₁, C, hθ₁, H⟩ := q08f_exp_moment D
    have hmeas' : Measurable (fun X : Config d N => modulatedEnergy D.q08f_h' X D.μ) :=
      measurable_modulatedEnergy (q08f_rowOK_h' D)
    have hfin := (H N h).trans_lt ENNReal.ofReal_lt_top
    have hexp : Integrable (fun X : Config d N =>
        Real.exp (θ₁ * N * |modulatedEnergy D.q08f_h' X D.μ|)) (D.Gibbs N) := by
      refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).1 hfin.ne
      · exact (Real.measurable_exp.comp (measurable_const.mul hmeas'.abs)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun X => (Real.exp_pos _).le
    have hθN : 0 < θ₁ * N := by positivity
    have hint' : Integrable (fun X : Config d N => modulatedEnergy D.q08f_h' X D.μ) (D.Gibbs N) := by
      refine Integrable.mono' (hexp.const_mul (θ₁ * N)⁻¹) hmeas'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]
      have h1 := Real.add_one_le_exp (θ₁ * N * |modulatedEnergy D.q08f_h' X D.μ|)
      have h2 : |modulatedEnergy D.q08f_h' X D.μ| ≤
          (θ₁ * N)⁻¹ * Real.exp (θ₁ * N * |modulatedEnergy D.q08f_h' X D.μ|) := by
        rw [← div_eq_inv_mul, le_div_iff₀ hθN]
        nlinarith [abs_nonneg (modulatedEnergy D.q08f_h' X D.μ)]
      exact h2
    exact hint'.congr ((q08f_gibbs_ac D N).ae_eq (q08f_energy_ae D N).symm)

end HRS.Q08

end
