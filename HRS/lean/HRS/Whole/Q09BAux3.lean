import HRS.Whole.Q09BAux2
import HRS.Whole.Q09AAux2

/-!
# Packet Q09-B, part 3: energy control of the pair majorant and the mean-field second moment

* `q09b_u_energy_bound`: for `s > 0`, `(MB d s/N²) ∑_{i≠j} g(x_i - x_j) ≤ C (F_N + 𝔬_N + 1)` pointwise
  (the particle-background and background-background potentials are bounded by `Λ ∫_{B₁} g + 1`);
* `q09b_mf_second_moment`: `∫ |x|² ρ ≤ Λ K_d` from `weightedSupE r (d+3) ρ ≤ Λ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Whole.Q09B

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `∫_{B(0,1)} g`. -/
def q09b_I (d : ℕ) (s : ℝ) : ℝ := ∫ z in Metric.ball (0 : Euc d) 1, rieszKernel d s z

theorem q09b_kernel_nonneg {s : ℝ} (hs : 0 < s) (w : Euc d) : 0 ≤ rieszKernel d s w := by
  simp only [rieszKernel, hs.ne', ite_false]
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem q09b_prob_integrable {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

/-- `g * ρ ≤ Λ ∫_{B₁} g + 1` pointwise. -/
theorem q09b_conv_le {s : ℝ} (hs : 0 < s) (hsd : s < d) {Λ : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ) (x : Euc d) :
    convMeasure (rieszKernel d s) (withDensityReal ρ) x ≤ Λ * q09b_I d s + 1 := by
  have hloc := rieszKernel_locallyIntegrable (d := d) hs.le hsd
  have hgI : IntegrableOn (rieszKernel d s) (Metric.ball (0 : Euc d) 1) :=
    (hloc.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) 1)).mono_set
      Metric.ball_subset_closedBall
  set h : Euc d → ℝ := Set.indicator (Metric.ball (0 : Euc d) 1) (rieszKernel d s) with hh
  have hhI : Integrable h := hgI.integrable_indicator Metric.isOpen_ball.measurableSet
  have hρint := q09b_prob_integrable hρ
  have hconv : convMeasure (rieszKernel d s) (withDensityReal ρ) x =
      ∫ y, ρ y * rieszKernel d s (x - y) := by
    unfold convMeasure
    exact Q09A.pair_withDensityReal hρ (fun y => rieszKernel d s (x - y))
  rw [hconv]
  have hrhs : Integrable (fun y => Λ * h (x - y) + ρ y) :=
    ((hhI.comp_sub_left x).const_mul Λ).add hρint
  have hpt : ∀ y, ρ y * rieszKernel d s (x - y) ≤ Λ * h (x - y) + ρ y := by
    intro y
    have hg0 := q09b_kernel_nonneg (d := d) hs (x - y)
    by_cases hb : x - y ∈ Metric.ball (0 : Euc d) 1
    · have : h (x - y) = rieszKernel d s (x - y) := by simp [hh, Set.indicator, hb]
      rw [this]
      nlinarith [hρ.nonneg y, hρΛ y]
    · have : h (x - y) = 0 := by simp [hh, Set.indicator, hb]
      rw [this]
      have hn : 1 ≤ ‖x - y‖ := by simpa [Metric.mem_ball, dist_zero_right] using hb
      have hk : rieszKernel d s (x - y) ≤ 1 := by
        simp only [rieszKernel, hs.ne', ite_false]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
      nlinarith [hρ.nonneg y]
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => mul_nonneg (hρ.nonneg y) (q09b_kernel_nonneg hs (x - y)))
    hrhs (Filter.Eventually.of_forall hpt)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((hhI.comp_sub_left x).const_mul Λ) hρint, integral_const_mul,
    integral_sub_left_eq_self (fun z => h z) volume x, hρ.integral_one]
  simp only [hh, q09b_I]
  rw [integral_indicator Metric.isOpen_ball.measurableSet]

theorem q09b_oN_nonneg {s : ℝ} (hs : 0 < s) {C₀ Λ : ℝ} (hC₀ : 0 ≤ C₀) (hΛ : 0 ≤ Λ) (N : ℕ) :
    0 ≤ oNΛ d s C₀ Λ N := by
  simp only [oNΛ, hs.ne', ite_false, zero_add]
  have h1 : 0 ≤ Λ ^ (s / (d : ℝ)) := Real.rpow_nonneg hΛ _
  have h2 : 0 ≤ (N : ℝ) ^ (s / (d : ℝ) - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

theorem q09b_u_energy_bound {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) (hsd : s < d) {Mn : ℝ}
    (hMn : 0 ≤ Mn) {C₀ Λ : ℝ} (hC₀ : 0 ≤ C₀) (hΛ : 0 ≤ Λ) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ) (x : EucConfig d N) :
    q09b_u d s Mn N x ≤ 2 * Mn * s * (rieszModulatedEnergy d s x (withDensityReal ρ) +
        oNΛ d s C₀ Λ N) + 2 * Mn * s * (Λ * q09b_I d s + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j) with hP
  set B : ℝ := Λ * q09b_I d s + 1 with hB
  have hconv : (1 / (N : ℝ)) * ∑ i, convMeasure (rieszKernel d s) (withDensityReal ρ) (x i) ≤ B := by
    have h1 : ∑ i, convMeasure (rieszKernel d s) (withDensityReal ρ) (x i) ≤ N * B := by
      calc ∑ i, convMeasure (rieszKernel d s) (withDensityReal ρ) (x i) ≤ ∑ _i : Fin N, B :=
            Finset.sum_le_sum fun i _ => q09b_conv_le hs hsd hρ hρΛ (x i)
        _ = N * B := by simp
    calc (1 / (N : ℝ)) * ∑ i, convMeasure (rieszKernel d s) (withDensityReal ρ) (x i)
        ≤ (1 / (N : ℝ)) * (N * B) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by field_simp
  have hEP : 0 ≤ energyPairing (rieszKernel d s) (withDensityReal ρ) (withDensityReal ρ) :=
    integral_nonneg fun a => integral_nonneg fun b => q09b_kernel_nonneg hs _
  have ho := q09b_oN_nonneg (d := d) hs hC₀ hΛ N
  have hF : rieszModulatedEnergy d s x (withDensityReal ρ) =
      (1 / (2 * (N : ℝ) ^ 2)) * P - (1 / (N : ℝ)) * ∑ i,
        convMeasure (rieszKernel d s) (withDensityReal ρ) (x i) +
      (1 / 2) * energyPairing (rieszKernel d s) (withDensityReal ρ) (withDensityReal ρ) := rfl
  have hu : q09b_u d s Mn N x = Mn * s * (((N : ℝ) ^ 2)⁻¹ * P) := by
    simp only [q09b_u, hs.ne', ite_false, hP]; ring
  have hP2 : ((N : ℝ) ^ 2)⁻¹ * P ≤ 2 * (rieszModulatedEnergy d s x (withDensityReal ρ) +
      oNΛ d s C₀ Λ N) + 2 * B := by
    have : ((N : ℝ) ^ 2)⁻¹ * P = 2 * ((1 / (2 * (N : ℝ) ^ 2)) * P) := by field_simp
    rw [this, hF] at *
    nlinarith
  rw [hu]
  have hMs : 0 ≤ Mn * s := mul_nonneg hMn hs.le
  calc Mn * s * (((N : ℝ) ^ 2)⁻¹ * P) ≤ Mn * s * (2 * (rieszModulatedEnergy d s x (withDensityReal ρ) +
        oNΛ d s C₀ Λ N) + 2 * B) := mul_le_mul_of_nonneg_left hP2 hMs
    _ = _ := by ring

theorem q09b_jbracket_bound {r : ℕ} {L : ℝ} {f : Euc d → ℝ} (hfin : weightedSupE r L f < ⊤)
    (x : Euc d) : jbracket x ^ L * |f x| ≤ (weightedSupE r L f).toReal := by
  have h : ENNReal.ofReal (jbracket x ^ L * |f x|) ≤ weightedSupE r L f := by
    unfold weightedSupE derivSupE
    refine le_trans ?_ (le_iSup _ (0 : Fin (r + 1)))
    refine le_trans ?_ (le_iSup _ (fun l : Fin ((0 : Fin (r + 1)) : ℕ) =>
      (Fin.elim0 (by simpa using l) : Fin d)))
    refine le_trans ?_ (le_iSup _ x)
    have e : partialDeriv (fun l : Fin ((0 : Fin (r + 1)) : ℕ) =>
        (Fin.elim0 (by simpa using l) : Fin d)) f x = f x :=
      iteratedFDeriv_zero_apply _
    rw [e]
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h

/-- `K_d = ∫ (1+|x|²)^{-(d+1)/2} dx`. -/
def q09b_K (d : ℕ) : ℝ := ∫ x : Euc d, (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2)

theorem q09b_mf_second_moment {s : ℝ} {r : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hreg : IsRegularMFRd s r Λ T ρ) (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ t))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    secondMomentOf (withDensityReal (ρ t)) ≤ Λ * q09b_K d := by
  obtain ⟨hmem, hfin, hΛ⟩ := hreg.1 t ht
  have hρ := hprob t ht
  have hcb : 0 ≤ cbNorm r (ρ t) :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hΛ' : (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ := by linarith
  have hpt : ∀ x : Euc d, ρ t x * ‖x‖ ^ 2 ≤ Λ * (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2) := by
    intro x
    have ha : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hw := q09b_jbracket_bound hfin x
    have hjb : jbracket x ^ ((d : ℝ) + 3) = (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) := by
      unfold jbracket
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
      congr 1
      ring
    rw [hjb, abs_of_nonneg (hρ.nonneg x)] at hw
    have h1 : (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) * ρ t x ≤ Λ := hw.trans hΛ'
    have h2 : (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) =
        (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * (1 + ‖x‖ ^ 2) := by
      rw [← Real.rpow_add_one ha.ne']
      congr 1
      ring
    set a : ℝ := 1 + ‖x‖ ^ 2 with hadef
    have hb : a ^ (-((d : ℝ) + 1) / 2) * a ^ (((d : ℝ) + 1) / 2) = 1 := by
      rw [← Real.rpow_add ha]
      have : -((d : ℝ) + 1) / 2 + ((d : ℝ) + 1) / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    have hbpos : 0 < a ^ (-((d : ℝ) + 1) / 2) := Real.rpow_pos_of_pos ha _
    have hρa : ρ t x * ‖x‖ ^ 2 ≤ ρ t x * a := by
      have := hρ.nonneg x
      nlinarith [sq_nonneg ‖x‖]
    have h3 : ρ t x * a * a ^ (((d : ℝ) + 1) / 2) ≤ Λ := by
      rw [h2] at h1; nlinarith [h1]
    calc ρ t x * ‖x‖ ^ 2 ≤ ρ t x * a := hρa
      _ = (ρ t x * a * a ^ (((d : ℝ) + 1) / 2)) * a ^ (-((d : ℝ) + 1) / 2) := by
          rw [mul_assoc, mul_assoc, mul_comm (a ^ (((d : ℝ) + 1) / 2)), hb]; ring
      _ ≤ Λ * a ^ (-((d : ℝ) + 1) / 2) := mul_le_mul_of_nonneg_right h3 hbpos.le
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2)) := by
    have := integrable_rpow_neg_one_add_norm_sq (E := Euc d) (μ := volume) (r := (d : ℝ) + 1)
      (by simp)
    exact this
  unfold secondMomentOf
  rw [Q09A.pair_withDensityReal hρ]
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (sq_nonneg ‖x‖))
    (hint.const_mul Λ) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  exact hmono

end HRS.Whole.Q09B
