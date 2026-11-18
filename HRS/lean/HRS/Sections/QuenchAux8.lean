import HRS.Sections.QuenchAux7

/-!
# Packet QUENCH (Q27), part 8: the discrete approximants `V_m` of `c₀Y + ∑ c_i B_{t_i}`

`V_m = c₀ Y + ∑_i c_i σ⁻¹ ∑_{k<N_i} ξ_k` is a centred Gaussian with explicit variance.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

section Approx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

lemma integral_sq_sum_eq {ι : Type*} (S : Finset ι) (X : ι → Ω → ℝ) (hX : ∀ i ∈ S, MemLp (X i) 2 P) :
    ∫ ω, (∑ i ∈ S, X i ω) ^ 2 ∂P = ∑ i ∈ S, ∑ j ∈ S, ∫ ω, X i ω * X j ω ∂P := by
  have e : ∀ ω, (∑ i ∈ S, X i ω) ^ 2 = ∑ i ∈ S, ∑ j ∈ S, X i ω * X j ω := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finset_sum]
    intro j hj
    exact (hX i hi).integrable_mul (hX j hj)
  · intro i hi
    exact integrable_finset_sum _ fun j hj => (hX i hi).integrable_mul (hX j hj)

/-- Grid step `h = 1/(m+1)`. -/
def gh (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

lemma gh_pos (m : ℕ) : 0 < gh m := by unfold gh; positivity

/-- Number of grid steps up to time `t`. -/
def gN (m : ℕ) (t : ℝ) : ℕ := ⌊t * ((m : ℝ) + 1)⌋₊

/-- The discrete approximant of `c₀ Y + ∑_i c_i B_{t_i}` (without the `σ⁻¹`: `σ` is a parameter). -/
def Vapp (lam σ : ℝ) (G : ℝ → Ω → ℝ) (Y : Ω → ℝ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) (c₀ : ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  c₀ * Y ω + ∑ i, c i * ((1 / σ) * ∑ k ∈ Finset.range (gN m (ts i)),
    xi G (gh m) (Real.exp (-lam * gh m)) k ω)

/-- Total number of grid steps. -/
def gK (m : ℕ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) : ℕ := ∑ i, gN m (ts i)

/-- The coefficient of `ξ_k` in `V_m`. -/
def galpha (σ : ℝ) (m : ℕ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if k < gN m (ts i) then c i / σ else 0

lemma Vapp_eq (lam σ : ℝ) (G : ℝ → Ω → ℝ) (Y : Ω → ℝ) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ)
    (c₀ : ℝ) (m : ℕ) (ω : Ω) :
    Vapp lam σ G Y ts c c₀ m ω = c₀ * Y ω + ∑ k ∈ Finset.range (gK m ts),
      galpha σ m ts c k * xi G (gh m) (Real.exp (-lam * gh m)) k ω := by
  unfold Vapp galpha
  congr 1
  have hle : ∀ i, gN m (ts i) ≤ gK m ts := fun i =>
    Finset.single_le_sum (f := fun i => gN m (ts i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have e1 : ∀ i, c i * ((1 / σ) * ∑ k ∈ Finset.range (gN m (ts i)),
      xi G (gh m) (Real.exp (-lam * gh m)) k ω) =
      ∑ k ∈ Finset.range (gK m ts), (if k < gN m (ts i) then c i / σ else 0) *
        xi G (gh m) (Real.exp (-lam * gh m)) k ω := by
    intro i
    have : ∑ k ∈ Finset.range (gK m ts), (if k < gN m (ts i) then c i / σ else 0) *
        xi G (gh m) (Real.exp (-lam * gh m)) k ω =
        ∑ k ∈ Finset.range (gN m (ts i)), c i / σ * xi G (gh m) (Real.exp (-lam * gh m)) k ω := by
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      have := hle i
      omega
    rw [this, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

variable (hN : OUNoise lam v vY P Y G)
include hN

lemma Vapp_gauss {σ : ℝ} {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ) (c₀ : ℝ)
    (m : ℕ) : HasGaussianLaw (Vapp lam σ G Y ts c c₀ m) P := by
  classical
  set h := gh m with hh
  set x := Real.exp (-lam * h) with hx
  have hh0 : 0 ≤ h := (gh_pos m).le
  let τ : ℕ × Bool → ℝ≥0 := fun q => Real.toNNReal (((q.1 : ℝ) + (if q.2 then 1 else 0)) * h)
  let a : ℕ × Bool → ℝ := fun q => galpha σ m ts c q.1 * (if q.2 then 1 else -x)
  have h1 := hN.gauss_comb (Finset.range (gK m ts) ×ˢ (Finset.univ : Finset Bool)) τ a c₀
  refine h1.congr (Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [Vapp_eq, Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  have c1 : ((Real.toNNReal (((k : ℝ) + 1) * h) : ℝ≥0) : ℝ) = ((k : ℝ) + 1) * h :=
    Real.coe_toNNReal _ (by positivity)
  have c3 : ((Real.toNNReal ((k : ℝ) * h) : ℝ≥0) : ℝ) = (k : ℝ) * h :=
    Real.coe_toNNReal _ (by positivity)
  simp only [a, τ, xi, Bool.false_eq_true, ite_false, ite_true, add_zero]
  rw [c1, c3, ← hh, ← hx]
  ring

lemma integral_Y_xi {h : ℝ} (hh : 0 ≤ h) (x : ℝ) (k : ℕ) :
    ∫ ω, Y ω * xi G h x k ω ∂P = 0 := by
  have h1 := hN.memLpG' (t := ((k : ℝ) + 1) * h) (by positivity)
  have h2 := hN.memLpG' (t := (k : ℝ) * h) (by positivity)
  have e : ∀ ω, Y ω * xi G h x k ω = Y ω * G (((k : ℝ) + 1) * h) ω - x * (Y ω * G ((k : ℝ) * h) ω) := by
    intro ω; unfold xi; ring
  simp_rw [e]
  rw [integral_sub (f := fun ω => Y ω * G (((k : ℝ) + 1) * h) ω) (g := fun ω => x * (Y ω * G ((k : ℝ) * h) ω))
      (hN.memLpY.integrable_mul h1) ((hN.memLpY.integrable_mul h2).const_mul x),
    integral_const_mul]
  have c1 : ∫ ω, Y ω * G (((k : ℝ) + 1) * h) ω ∂P = 0 := hN.covYG ⟨((k : ℝ) + 1) * h, by positivity⟩
  have c2 : ∫ ω, Y ω * G ((k : ℝ) * h) ω ∂P = 0 := hN.covYG ⟨(k : ℝ) * h, by positivity⟩
  rw [c1, c2]
  simp

lemma Vapp_mean {σ : ℝ} {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) (c₀ : ℝ) (m : ℕ) :
    ∫ ω, Vapp lam σ G Y ts c c₀ m ω ∂P = 0 := by
  have hh0 : 0 ≤ gh m := (gh_pos m).le
  simp_rw [Vapp_eq]
  rw [integral_add (hN.memLpY.integrable one_le_two |>.const_mul c₀)
    (integrable_finset_sum _ fun k _ => ((hN.memLp_xi hh0 _ k).integrable one_le_two).const_mul _),
    integral_const_mul, integral_finset_sum _ fun k _ =>
      ((hN.memLp_xi hh0 _ k).integrable one_le_two).const_mul _, hN.meanY]
  simp [integral_const_mul, hN.integral_xi hh0]

lemma Vapp_sq {σ : ℝ} {ι : Type*} [Fintype ι] (ts : ι → ℝ) (c : ι → ℝ) (c₀ : ℝ) (m : ℕ) :
    ∫ ω, Vapp lam σ G Y ts c c₀ m ω ^ 2 ∂P =
      c₀ ^ 2 * vY + v * (1 - Real.exp (-lam * gh m) ^ 2) *
        ∑ k ∈ Finset.range (gK m ts), galpha σ m ts c k ^ 2 := by
  have hh0 : 0 ≤ gh m := (gh_pos m).le
  set x := Real.exp (-lam * gh m) with hx
  set K := gK m ts
  set α := galpha σ m ts c with hα
  have hxi : ∀ k, MemLp (fun ω => α k * xi G (gh m) x k ω) 2 P := fun k =>
    (hN.memLp_xi hh0 x k).const_mul _
  set Z : Ω → ℝ := fun ω => ∑ k ∈ Finset.range K, α k * xi G (gh m) x k ω with hZ
  have hZm : MemLp Z 2 P := memLp_finsetSum (Finset.range K) fun k _ => hxi k
  have e : ∀ ω, Vapp lam σ G Y ts c c₀ m ω ^ 2 =
      c₀ ^ 2 * (Y ω * Y ω) + 2 * c₀ * (Y ω * Z ω) + Z ω ^ 2 := by
    intro ω; rw [Vapp_eq]; simp only [hZ, hα, hx]; ring
  simp_rw [e]
  have iYY : Integrable (fun ω => Y ω * Y ω) P := hN.memLpY.integrable_mul hN.memLpY
  have iYZ : Integrable (fun ω => Y ω * Z ω) P := hN.memLpY.integrable_mul hZm
  have iZZ : Integrable (fun ω => Z ω ^ 2) P := by
    have : Integrable (fun ω => Z ω * Z ω) P := hZm.integrable_mul hZm
    simpa [sq] using this
  have i1 : Integrable (fun ω => c₀ ^ 2 * (Y ω * Y ω)) P := iYY.const_mul _
  have i2 : Integrable (fun ω => 2 * c₀ * (Y ω * Z ω)) P := iYZ.const_mul _
  rw [integral_add (f := fun ω => c₀ ^ 2 * (Y ω * Y ω) + 2 * c₀ * (Y ω * Z ω)) (g := fun ω => Z ω ^ 2)
      (i1.add i2) iZZ,
    integral_add (f := fun ω => c₀ ^ 2 * (Y ω * Y ω)) (g := fun ω => 2 * c₀ * (Y ω * Z ω)) i1 i2,
    integral_const_mul, integral_const_mul, hN.covYY]
  have hYZ : ∫ ω, Y ω * Z ω ∂P = 0 := by
    have : ∀ ω, Y ω * Z ω = ∑ k ∈ Finset.range K, α k * (Y ω * xi G (gh m) x k ω) := by
      intro ω; simp only [hZ, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [this]
    rw [integral_finset_sum (Finset.range K) (f := fun k ω => α k * (Y ω * xi G (gh m) x k ω))
      fun k _ => ((hN.memLpY.integrable_mul (hN.memLp_xi hh0 x k))).const_mul _]
    simp [integral_const_mul, integral_Y_xi hN hh0]
  have hZZ : ∫ ω, Z ω ^ 2 ∂P = v * (1 - x ^ 2) * ∑ k ∈ Finset.range K, α k ^ 2 := by
    have := integral_sq_sum_eq (P := P) (Finset.range K) (fun k ω => α k * xi G (gh m) x k ω)
      (fun k _ => hxi k)
    simp only [hZ]
    rw [this]
    have e2 : ∀ k l : ℕ, ∫ ω, α k * xi G (gh m) x k ω * (α l * xi G (gh m) x l ω) ∂P =
        α k * α l * (if k = l then v * (1 - x ^ 2) else 0) := by
      intro k l
      rw [← hN.integral_xi_mul hh0 k l, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hx]; ring
    simp_rw [e2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k]
    · simp; ring
    · intro l _ hl; simp [Ne.symm hl]
    · intro hk'; exact absurd hk hk'
  rw [hYZ, hZZ]
  ring

end Approx

end Qch

end HRS
