import HRS.Energy.Commutator.RoughAux

/-!
# Heat kernel on the torus as an approximate identity (packet CM-S3, helpers for `stress_rough`)

`hk ε = ∑_k e^{-4π²ε|k|²} cos(2π k·x) = 1 + Ψ(x, 4π²ε)`: nonnegative, even, of mass one, a convolution
semigroup, with off-diagonal tail bound `hk ε z ≲ ε^{(n-d)/2} tdist(z)^{-n}`; and the abstract
approximate-identity lemma used to take the limit of the mollified kernels.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux

namespace HRS.Commutator.RoughHeat

variable {d : ℕ}

/-- The torus heat kernel at time `ε`. -/
def hk (ε : ℝ) : Torus d → ℝ := ser (aW ε)

theorem aW_gauss {ε : ℝ} (hε : 0 < ε) : GaussDecay (aW (d := d) ε) :=
  ⟨4 * Real.pi ^ 2 * ε, 1, by positivity, fun k => by
    have := aW_bound (ε := ε) k
    simpa [neg_mul] using this⟩

theorem aW_bound' (ε : ℝ) :
    ∀ k : Lattice d, |aW ε k| ≤ 1 * Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) :=
  fun k => aW_bound k

theorem enorm_zero' : Lattice.enorm (0 : Lattice d) = 0 := by
  unfold Lattice.enorm; simp [Lattice.toEuc]; rfl

theorem hk_eq {ε : ℝ} (hε : 0 < ε) (x : Torus d) : hk ε x = 1 + psiFn x (4 * Real.pi ^ 2 * ε) := by
  have hu : 0 < 4 * Real.pi ^ 2 * ε := by positivity
  unfold hk ser psiFn
  have hs := psi_summable x hu
  have hind : Summable fun k : Lattice d => if k = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])
  have h1 : ∀ k : Lattice d, aW ε k * Torus.cosMode k x =
      (if k = 0 then (1 : ℝ) else 0) +
        (if k = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) * Torus.cosMode k x) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [aW, Torus.cosMode, Torus.mode_zero, enorm_zero']
    · simp [aW, hk]
  simp_rw [h1]
  rw [(hind.hasSum.add hs.hasSum).tsum_eq, tsum_ite_eq]

theorem hk_nonneg {ε : ℝ} (hε : 0 < ε) (x : Torus d) : 0 ≤ hk ε x := by
  rw [hk_eq hε]; exact EnergyAux.one_add_psiFn_nonneg' x (by positivity)

theorem hk_neg (ε : ℝ) (x : Torus d) : hk ε (-x) = hk ε x := ser_neg _ x

theorem continuous_hk {ε : ℝ} (hε : 0 < ε) : Continuous (hk (d := d) ε) :=
  continuous_ser (aW_gauss hε).summable

theorem integral_hk {ε : ℝ} (hε : 0 < ε) : ∫ x : Torus d, hk ε x = 1 := by
  simp_rw [hk_eq hε]
  exact EnergyAux.integral_one_add_psiFn_aux (by positivity)

theorem integrable_hk {ε : ℝ} (hε : 0 < ε) : Integrable (hk (d := d) ε) :=
  (continuous_hk hε).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem hk_bdd {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, ∀ x : Torus d, hk ε x ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_hk (d := d) hε).continuousOn
  exact ⟨M, fun x => (le_abs_self _).trans (by simpa using hM x (mem_univ _))⟩

/-- Semigroup property: `hk a ⋆ hk b = hk (a+b)`. -/
theorem hk_semigroup {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : Torus d) :
    ∫ y, hk a (x - y) * hk b y = hk (a + b) x := by
  have h := convS_ser_ser (aW_gauss (d := d) ha) (aW_gauss (d := d) hb) (aW_even a) (aW_even b)
  have h2 := congrFun h x
  have e : (fun k : Lattice d => aW a k * aW b k) = aW (a + b) := by
    funext k
    unfold aW
    rw [← Real.exp_add]
    congr 1; ring
  rw [e] at h2
  exact h2


/-! ### Off-diagonal bounds -/

theorem theta_tdist_pow (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (z : Torus d) {u : ℝ}, 0 < u →
    KernelGrad.tdist z 0 ^ n * (1 + psiFn z u) ≤
      c * Real.sqrt u ^ n * (1 + psiFn z (2 ^ n * u)) := by
  induction n with
  | zero => exact ⟨1, zero_le_one, fun z u hu => by simp⟩
  | succ n ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    refine ⟨c * (Real.sqrt 2 ^ d / Real.pi) * Real.sqrt 2 ^ n,
      mul_nonneg (mul_nonneg hc0 (div_nonneg (by positivity) Real.pi_pos.le)) (by positivity), fun z u hu => ?_⟩
    have h1 := HeatAux.tdist_theta_le z hu
    have h2 := hc z (by positivity : 0 < 2 * u)
    have ht0 : 0 ≤ KernelGrad.tdist z 0 ^ n := pow_nonneg (KernelGrad.tdist_nonneg z 0) n
    have hsq : Real.sqrt (2 * u) = Real.sqrt 2 * Real.sqrt u := Real.sqrt_mul (by norm_num) u
    calc KernelGrad.tdist z 0 ^ (n + 1) * (1 + psiFn z u)
        = KernelGrad.tdist z 0 ^ n * (KernelGrad.tdist z 0 * (1 + psiFn z u)) := by ring
      _ ≤ KernelGrad.tdist z 0 ^ n * (Real.sqrt u / Real.pi * Real.sqrt 2 ^ d * (1 + psiFn z (2 * u))) :=
          mul_le_mul_of_nonneg_left h1 ht0
      _ = (Real.sqrt u / Real.pi * Real.sqrt 2 ^ d) * (KernelGrad.tdist z 0 ^ n * (1 + psiFn z (2 * u))) := by ring
      _ ≤ (Real.sqrt u / Real.pi * Real.sqrt 2 ^ d) * (c * Real.sqrt (2 * u) ^ n * (1 + psiFn z (2 ^ n * (2 * u)))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c * (Real.sqrt 2 ^ d / Real.pi) * Real.sqrt 2 ^ n * Real.sqrt u ^ (n + 1) *
            (1 + psiFn z (2 ^ (n + 1) * u)) := by
          rw [hsq, mul_pow, pow_succ 2 n, show (2 : ℝ) ^ n * 2 * u = 2 ^ n * (2 * u) by ring]
          ring

theorem theta_sup (d : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : Torus d) {U : ℝ}, 0 < U → U ≤ 1 →
    1 + psiFn z U ≤ B * U ^ (-((d : ℝ) / 2)) := by
  obtain ⟨K, hK0, hK⟩ := HeatAux.abs_psiFn_le_exp d
  refine ⟨1 + K, by positivity, fun z U hU hU1 => ?_⟩
  have h1 := HeatAux.theta_mono z hU hU1
  have h2 : 1 + psiFn z 1 ≤ 1 + K := by
    have := hK z 1 le_rfl
    have h3 : |psiFn z 1| ≤ K := by
      calc |psiFn z 1| ≤ K * Real.exp (-1) := this
        _ ≤ K * 1 := by gcongr; rw [Real.exp_le_one_iff]; norm_num
        _ = K := mul_one K
    linarith [(le_abs_self (psiFn z 1))]
  calc 1 + psiFn z U ≤ (1 / U) ^ ((d : ℝ) / 2) * (1 + psiFn z 1) := h1
    _ ≤ (1 / U) ^ ((d : ℝ) / 2) * (1 + K) := by gcongr
    _ = (1 + K) * U ^ (-((d : ℝ) / 2)) := by
        rw [one_div, Real.inv_rpow hU.le, ← Real.rpow_neg hU.le]; ring

theorem hk_sup (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → 4 * Real.pi ^ 2 * ε ≤ 1 →
    ∀ z : Torus d, hk ε z ≤ C * ε ^ (-((d : ℝ) / 2)) := by
  obtain ⟨B, hB0, hB⟩ := theta_sup d
  refine ⟨B * (4 * Real.pi ^ 2) ^ (-((d : ℝ) / 2)), by positivity, fun ε hε hε1 z => ?_⟩
  rw [hk_eq hε]
  refine (hB z (by positivity) hε1).trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) hε.le]; ring

theorem hk_tail (d n : ℕ) {r : ℝ} (hr : 0 < r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
    2 ^ n * (4 * Real.pi ^ 2 * ε) ≤ 1 → ∀ z : Torus d, r ≤ KernelGrad.tdist z 0 →
      hk ε z ≤ C * ε ^ (((n : ℝ) - d) / 2) := by
  obtain ⟨c, hc0, hc⟩ := theta_tdist_pow (d := d) n
  obtain ⟨B, hB0, hB⟩ := theta_sup d
  refine ⟨(r ^ n)⁻¹ * c * B * (4 * Real.pi ^ 2) ^ (((n : ℝ) - d) / 2) * 2 ^ (-((n : ℝ) * d / 2)),
    by positivity, fun ε hε hε1 z hz => ?_⟩
  have hu : 0 < 4 * Real.pi ^ 2 * ε := by positivity
  set u := 4 * Real.pi ^ 2 * ε with hu_def
  have hrn : 0 < r ^ n := by positivity
  have hθ0 : 0 ≤ 1 + psiFn z u := EnergyAux.one_add_psiFn_nonneg' z hu
  have h1 := hc z hu
  have h2 := hB z (by positivity : 0 < 2 ^ n * u) hε1
  have h3 : r ^ n * (1 + psiFn z u) ≤ KernelGrad.tdist z 0 ^ n * (1 + psiFn z u) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hz n) hθ0
  have hc3 : 0 ≤ c * Real.sqrt u ^ n := by positivity
  have h4 : r ^ n * (1 + psiFn z u) ≤ c * Real.sqrt u ^ n * (B * (2 ^ n * u) ^ (-((d : ℝ) / 2))) :=
    h3.trans (h1.trans (mul_le_mul_of_nonneg_left h2 hc3))
  have hk' : hk ε z = 1 + psiFn z u := hk_eq hε z
  rw [hk']
  have h5 : 1 + psiFn z u ≤ (r ^ n)⁻¹ * (c * Real.sqrt u ^ n * (B * (2 ^ n * u) ^ (-((d : ℝ) / 2)))) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hrn]
    linarith
  refine h5.trans (le_of_eq ?_)
  -- rpow bookkeeping
  have e1 : Real.sqrt u ^ n = u ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; congr 1; ring
  have e2 : (2 ^ n * u : ℝ) ^ (-((d : ℝ) / 2)) = 2 ^ (-((n : ℝ) * d / 2)) * u ^ (-((d : ℝ) / 2)) := by
    rw [Real.mul_rpow (by positivity) hu.le, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 2; ring
  have e3 : u ^ ((n : ℝ) / 2) * u ^ (-((d : ℝ) / 2)) = (4 * Real.pi ^ 2) ^ (((n : ℝ) - d) / 2) *
      ε ^ (((n : ℝ) - d) / 2) := by
    rw [← Real.rpow_add hu, hu_def, Real.mul_rpow (by positivity) hε.le]
    congr 2 <;> ring
  rw [e1, e2]
  calc (r ^ n)⁻¹ * (c * u ^ ((n : ℝ) / 2) * (B * (2 ^ (-((n : ℝ) * d / 2)) * u ^ (-((d : ℝ) / 2)))))
      = (r ^ n)⁻¹ * c * B * 2 ^ (-((n : ℝ) * d / 2)) * (u ^ ((n : ℝ) / 2) * u ^ (-((d : ℝ) / 2))) := by ring
    _ = _ := by rw [e3]; ring


theorem tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Abstract approximate identity -/

/-- Approximate identity: if `ψ i ≥ 0` integrates to one, is bounded, and is uniformly small away
from `x₀`, then `∫ F ψ i → F x₀` for `F ∈ L¹` continuous at `x₀` (all hypotheses eventual in `l`). -/
theorem approx_identity {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (lam : Measure X) [IsFiniteMeasure lam] {F : X → ℝ} (hF : Integrable F lam) {x₀ : X}
    (hc : ContinuousAt F x₀) {ι : Type*} (l : Filter ι) (δ₀ : X → ℝ) (hδ : ∀ x, dist x x₀ ≤ δ₀ x)
    (ψ : ι → X → ℝ) (hψ0 : ∀ᶠ i in l, ∀ x, 0 ≤ ψ i x) (hψm : ∀ᶠ i in l, Measurable (ψ i))
    (hψ1 : ∀ᶠ i in l, ∫ x, ψ i x ∂lam = 1) (hψb : ∀ᶠ i in l, ∃ M, ∀ x, ψ i x ≤ M)
    (htail : ∀ r : ℝ, 0 < r → ∃ b : ι → ℝ, Tendsto b l (𝓝 0) ∧
      ∀ᶠ i in l, ∀ x, r ≤ δ₀ x → ψ i x ≤ b i) :
    Tendsto (fun i => ∫ x, F x * ψ i x ∂lam) l (𝓝 (F x₀)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set Cn : ℝ := ∫ x, |F x| ∂lam + |F x₀| * lam.real Set.univ with hCn
  have hCn0 : 0 ≤ Cn := by
    have : 0 ≤ ∫ x, |F x| ∂lam := integral_nonneg fun x => abs_nonneg _
    positivity
  obtain ⟨r, hr, hrF⟩ := Metric.continuousAt_iff.mp hc (η / 3) (by positivity)
  obtain ⟨b, hb, hbψ⟩ := htail r hr
  have hb' : ∀ᶠ i in l, |b i| * Cn < η / 3 := by
    have h1 : Tendsto (fun i => |b i| * Cn) l (𝓝 (|0| * Cn)) :=
      (continuous_abs.continuousAt.tendsto.comp hb).mul_const Cn
    simp only [abs_zero, zero_mul] at h1
    exact h1.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hb', hψ0, hψm, hψ1, hψb, hbψ] with i hi hψ0i hψmi hψ1i hψbi hbψi
  obtain ⟨M, hM⟩ := hψbi
  have hψi : Integrable (ψ i) lam := by
    by_contra h
    have := hψ1i
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hFψ : Integrable (fun x => F x * ψ i x) lam :=
    Integrable.mul_bdd (c := M) hF (hψmi).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ0i x)]; exact hM x)
  -- the pointwise bound
  have hpt : ∀ x, |F x - F x₀| * ψ i x ≤ (η / 3) * ψ i x + (|F x| + |F x₀|) * |b i| := by
    intro x
    by_cases hx : r ≤ δ₀ x
    · have h1 : ψ i x ≤ |b i| := (hbψi x hx).trans (le_abs_self _)
      calc |F x - F x₀| * ψ i x ≤ (|F x| + |F x₀|) * ψ i x :=
            mul_le_mul_of_nonneg_right (abs_sub _ _) (hψ0i x)
        _ ≤ (|F x| + |F x₀|) * |b i| := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ _ := by have := mul_nonneg (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 3)) (hψ0i x); linarith
    · push_neg at hx
      have h1 : dist x x₀ < r := (hδ x).trans_lt hx
      have h2 := hrF h1
      rw [Real.dist_eq] at h2
      calc |F x - F x₀| * ψ i x ≤ (η / 3) * ψ i x := mul_le_mul_of_nonneg_right h2.le (hψ0i x)
        _ ≤ _ := by have := mul_nonneg (add_nonneg (abs_nonneg (F x)) (abs_nonneg (F x₀))) (abs_nonneg (b i)); linarith
  have hFd : Integrable (fun x => F x - F x₀) lam := hF.sub (integrable_const _)
  have hint1 : Integrable (fun x => |F x - F x₀| * ψ i x) lam :=
    Integrable.mul_bdd (c := M) hFd.abs (hψmi).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ0i x)]; exact hM x)
  have hint2 : Integrable (fun x => (η / 3) * ψ i x + (|F x| + |F x₀|) * |b i|) lam :=
    (hψi.const_mul _).add ((hF.abs.add (integrable_const _)).mul_const _)
  have hkey : ∫ x, F x * ψ i x ∂lam - F x₀ = ∫ x, (F x - F x₀) * ψ i x ∂lam := by
    have : ∫ x, (F x - F x₀) * ψ i x ∂lam = ∫ x, F x * ψ i x ∂lam - F x₀ * ∫ x, ψ i x ∂lam := by
      simp_rw [sub_mul]
      rw [integral_sub hFψ (hψi.const_mul _), integral_const_mul]
    rw [this, hψ1i]; ring
  rw [Real.dist_eq, hkey]
  calc |∫ x, (F x - F x₀) * ψ i x ∂lam| ≤ ∫ x, |(F x - F x₀) * ψ i x| ∂lam := by
        simpa using norm_integral_le_integral_norm (μ := lam) (fun x => (F x - F x₀) * ψ i x)
    _ = ∫ x, |F x - F x₀| * ψ i x ∂lam := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [abs_mul, abs_of_nonneg (hψ0i x)]
    _ ≤ ∫ x, ((η / 3) * ψ i x + (|F x| + |F x₀|) * |b i|) ∂lam :=
        integral_mono hint1 hint2 hpt
    _ = η / 3 + |b i| * Cn := by
        have h1 : Integrable (fun x => (|F x| + |F x₀|) * |b i|) lam :=
          (hF.abs.add (integrable_const _)).mul_const _
        have h2 : ∫ x, (|F x| + |F x₀|) * |b i| ∂lam = (∫ x, |F x| ∂lam + |F x₀| * lam.real Set.univ) * |b i| := by
          rw [integral_mul_const, integral_add hF.abs (integrable_const _), integral_const]
          simp only [smul_eq_mul, Measure.real]
          ring
        rw [integral_add (hψi.const_mul _) h1, integral_const_mul, hψ1i, h2, hCn]
        ring
    _ < η := by linarith

end HRS.Commutator.RoughHeat
