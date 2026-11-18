import HRS.MC.IID1
import HRS.MC.IID2

/-!
# Packet iid3, step K: the correlated finite section is the iid chaos of the conjugated truncation

For a contraction factor `S`, the `L²` limits `G_i` of the partial sums `∑_{k<n} S_ik g_k`, and a symmetric
Hilbert–Schmidt `B`, the correlated finite section `½ ∑_{i,j<L} B_ij (G_i G_j - C_ij)` equals almost everywhere
the iid chaos of `Sᵀ B_L S` (`section_ae_eq`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.IID

open HRS

section Finite

variable (S B : ℕ → ℕ → ℝ)

/-- The exact finite identity (pointwise in the sample). -/
theorem finite_identity (L n : ℕ) (x : ℕ → ℝ) :
    (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, B i j *
      ((∑ k ∈ range n, S i k * x k) * (∑ k ∈ range n, S j k * x k) - ∑ k ∈ range n, S i k * S j k) =
    (1 / 2) * ∑ k ∈ range n, ∑ l ∈ range n,
      s7_conjCoeff S (trunc L B) k l * (x k * x l - if k = l then 1 else 0) := by
  have key : ∀ i j, (∑ k ∈ range n, S i k * x k) * (∑ k ∈ range n, S j k * x k) -
      ∑ k ∈ range n, S i k * S j k =
      ∑ k ∈ range n, ∑ l ∈ range n, S i k * S j l * (x k * x l - if k = l then 1 else 0) := by
    intro i j
    have h1 : ∑ k ∈ range n, ∑ l ∈ range n, S i k * S j l * (x k * x l - if k = l then 1 else 0) =
        ∑ k ∈ range n, ∑ l ∈ range n, S i k * S j l * (x k * x l) -
          ∑ k ∈ range n, ∑ l ∈ range n, S i k * S j l * (if k = l then 1 else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h1, Finset.sum_mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [Finset.sum_ite_eq, hk]
  congr 1
  simp_rw [key, conj_trunc, Finset.sum_mul, Finset.mul_sum]
  -- both sides are quadruple sums
  calc ∑ i ∈ range L, ∑ j ∈ range L, ∑ k ∈ range n, ∑ l ∈ range n,
        B i j * (S i k * S j l * (x k * x l - if k = l then 1 else 0))
      = ∑ k ∈ range n, ∑ l ∈ range n, ∑ i ∈ range L, ∑ j ∈ range L,
        B i j * (S i k * S j l * (x k * x l - if k = l then 1 else 0)) := by
        simp_rw [Finset.sum_comm (s := range L) (t := range n)]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

end Finite


section Analytic

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A `TendstoL2` limit of `MemLp 2` functions is `MemLp 2`. -/
theorem memLp_of_tendstoL2 {Fn : ℕ → Ω → ℝ} {F : Ω → ℝ} (hFn : ∀ n, MemLp (Fn n) 2 P)
    (hF : TendstoL2 P Fn F) : MemLp F 2 P := by
  have h := hF.tendsto_eLpNorm fun n => (hFn n).aestronglyMeasurable
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).exists
  have h1 : MemLp (Fn n - F) 2 P :=
    lt_trans (b := (1 : ℝ≥0∞)) hn ENNReal.one_lt_top
  have := (hFn n).sub h1
  simpa using this

/-- Products of `L²`-convergent sequences converge in `L¹`. -/
theorem prod_tendsto_L1 {Fn Hn : ℕ → Ω → ℝ} {F H : Ω → ℝ} (hFn : ∀ n, MemLp (Fn n) 2 P)
    (hHn : ∀ n, MemLp (Hn n) 2 P) (hF : TendstoL2 P Fn F) (hH : TendstoL2 P Hn H) :
    Tendsto (fun n => eLpNorm (fun ω => Fn n ω * Hn n ω - F ω * H ω) 1 P) atTop (𝓝 0) := by
  have hFm := memLp_of_tendstoL2 hFn hF
  have hHm := memLp_of_tendstoL2 hHn hH
  have ha := hF.tendsto_eLpNorm fun n => (hFn n).aestronglyMeasurable
  have hd := hH.tendsto_eLpNorm fun n => (hHn n).aestronglyMeasurable
  have hbound : ∀ n, eLpNorm (fun ω => Fn n ω * Hn n ω - F ω * H ω) 1 P ≤
      eLpNorm (Fn n - F) 2 P * (eLpNorm H 2 P + eLpNorm (Hn n - H) 2 P) +
        eLpNorm F 2 P * eLpNorm (Hn n - H) 2 P := by
    intro n
    have e : (fun ω => Fn n ω * Hn n ω - F ω * H ω) =
        (Fn n - F) • (Hn n) + F • (Hn n - H) := by
      funext ω; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]; ring
    rw [e]
    refine (eLpNorm_add_le le_rfl).trans ?_
    refine add_le_add ?_ ?_
    · refine (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) (r := 1) one_pos).trans ?_
      refine mul_le_mul' le_rfl ?_
      have e2 : Hn n = H + (Hn n - H) := by abel
      calc eLpNorm (Hn n) 2 P = eLpNorm (H + (Hn n - H)) 2 P := by rw [← e2]
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    · exact eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) (r := 1) one_pos
  have hHtop : eLpNorm H 2 P ≠ ⊤ := hHm.eLpNorm_ne_top
  have hFtop : eLpNorm F 2 P ≠ ⊤ := hFm.eLpNorm_ne_top
  have h1 : Tendsto (fun n => eLpNorm (Fn n - F) 2 P * (eLpNorm H 2 P + eLpNorm (Hn n - H) 2 P))
      atTop (𝓝 (0 * (eLpNorm H 2 P + 0))) :=
    ENNReal.Tendsto.mul ha (Or.inr (by simpa using hHtop)) (tendsto_const_nhds.add hd)
      (Or.inr ENNReal.zero_ne_top)
  have h2 : Tendsto (fun n => eLpNorm F 2 P * eLpNorm (Hn n - H) 2 P) atTop
      (𝓝 (eLpNorm F 2 P * 0)) := ENNReal.Tendsto.const_mul hd (Or.inr hFtop)
  have h3 := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) hbound

end Analytic

section L1

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `fn → f` in `L¹(P)` (as a statement about the seminorms). -/
def L1Conv (P : Measure Ω) (fn : ℕ → Ω → ℝ) (f : Ω → ℝ) : Prop :=
  Tendsto (fun n => eLpNorm (fn n - f) 1 P) atTop (𝓝 0)

theorem L1Conv.add {fn hn : ℕ → Ω → ℝ} {f h : Ω → ℝ} (hf : L1Conv P fn f) (hh : L1Conv P hn h) :
    L1Conv P (fun n ω => fn n ω + hn n ω) (fun ω => f ω + h ω) := by
  have h3 := Filter.Tendsto.add hf hh
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) fun n => ?_
  have e : (fun ω => fn n ω + hn n ω) - (fun ω => f ω + h ω) = (fn n - f) + (hn n - h) := by
    funext ω; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [e]
  exact eLpNorm_add_le le_rfl

theorem L1Conv.sub {fn hn : ℕ → Ω → ℝ} {f h : Ω → ℝ} (hf : L1Conv P fn f) (hh : L1Conv P hn h) :
    L1Conv P (fun n ω => fn n ω - hn n ω) (fun ω => f ω - h ω) := by
  have h3 := Filter.Tendsto.add hf hh
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) fun n => ?_
  have e : (fun ω => fn n ω - hn n ω) - (fun ω => f ω - h ω) = (fn n - f) - (hn n - h) := by
    funext ω; simp only [Pi.sub_apply]; ring
  rw [e]
  refine (eLpNorm_sub_le le_rfl).trans le_rfl

theorem L1Conv.const_mul {fn : ℕ → Ω → ℝ} {f : Ω → ℝ} (c : ℝ) (hf : L1Conv P fn f) :
    L1Conv P (fun n ω => c * fn n ω) (fun ω => c * f ω) := by
  have h3 : Tendsto (fun n => ‖c‖ₑ * eLpNorm (fn n - f) 1 P) atTop (𝓝 (‖c‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul hf (Or.inr enorm_ne_top)
  rw [mul_zero] at h3
  refine h3.congr fun n => ?_
  have e : (fun ω => c * fn n ω) - (fun ω => c * f ω) = c • (fn n - f) := by
    funext ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, eLpNorm_const_smul]

theorem L1Conv.sum {ι : Type*} (s : Finset ι) {fn : ι → ℕ → Ω → ℝ} {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, L1Conv P (fn i) (f i)) :
    L1Conv P (fun n ω => ∑ i ∈ s, fn i n ω) (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold L1Conv
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem L1Conv.const {cn : ℕ → ℝ} {c : ℝ} (h : Tendsto cn atTop (𝓝 c)) :
    L1Conv P (fun n _ => cn n) (fun _ => c) := by
  unfold L1Conv
  have h2 : Tendsto (fun n => ‖cn n - c‖ₑ) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 h)
    have h3 := ENNReal.tendsto_ofReal this
    simp only [ENNReal.ofReal_zero] at h3
    exact h3.congr fun n => ofReal_norm_eq_enorm _
  refine h2.congr fun n => ?_
  have e : (fun _ : Ω => cn n) - (fun _ => c) = fun _ => cn n - c := by
    funext ω; simp
  rw [e, eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero P)]
  simp

theorem L1Conv.of_L2 {fn : ℕ → Ω → ℝ} {f : Ω → ℝ} (hm : ∀ n, AEStronglyMeasurable (fn n) P)
    (h : TendstoL2 P fn f) : L1Conv P fn f := by
  have h2 := h.tendsto_eLpNorm hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le) fun n => ?_
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

theorem L1Conv.ae_unique {fn : ℕ → Ω → ℝ} {f f' : Ω → ℝ}
    (h : L1Conv P fn f) (h' : L1Conv P fn f') : f =ᵐ[P] f' := by
  have hle : ∀ n, eLpNorm (f - f') 1 P ≤ eLpNorm (fn n - f) 1 P + eLpNorm (fn n - f') 1 P := by
    intro n
    have e : f - f' = -(fn n - f) + (fn n - f') := by abel
    rw [e]
    refine (eLpNorm_add_le le_rfl).trans ?_
    rw [eLpNorm_neg]
  have hz : eLpNorm (f - f') 1 P = 0 := by
    have ht := Filter.Tendsto.add h h'
    rw [add_zero] at ht
    exact le_antisymm (ge_of_tendsto' ht hle) bot_le
  have := (eLpNorm_eq_zero_iff one_ne_zero).1 hz
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω

end L1

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

/-- **Step K.**  The correlated finite section `½ ∑_{i,j<L} B_ij (G_i G_j - C_ij)` equals almost everywhere the
iid chaos of `Sᵀ B_L S`, where `G_i` is the `L²`-limit of the partial sums `∑_{k<n} S_ik g_k`. -/
theorem section_ae_eq (hg : IsStdGaussianSeq P g) {S Cm : ℕ → ℕ → ℝ} (hbound : ContrBound S)
    (hS : ∀ i j, HasSum (fun k => S i k * S j k) (Cm i j)) {G : ℕ → Ω → ℝ}
    (hG : ∀ i, TendstoL2 P (fun n ω => ∑ k ∈ range n, S i k * g k ω) (G i))
    {B : ℕ → ℕ → ℝ} (hB : IsSymmetricHS B) (L : ℕ) :
    (fun ω => (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, B i j * (G i ω * G j ω - Cm i j)) =ᵐ[P]
      chaos P (s7_conjCoeff S (trunc L B)) g := by
  set A := s7_conjCoeff S (trunc L B) with hA
  have hAs : IsSymmetricHS A := (conj_isSymmetricHS hbound (isSymmetricHS_trunc L hB)).1
  have hmem : ∀ i n, MemLp (fun ω => ∑ k ∈ range n, S i k * g k ω) 2 P := fun i n =>
    memLp_lin hg (S i) (range n)
  -- the sections are the finite correlated sections of the partial sums
  have hY : ∀ n, chaosSection A g n = fun ω => (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, B i j *
      ((∑ k ∈ range n, S i k * g k ω) * (∑ k ∈ range n, S j k * g k ω) -
        ∑ k ∈ range n, S i k * S j k) := by
    intro n
    funext ω
    rw [finite_identity S B L n (fun k => g k ω)]
    rfl
  have hprod : ∀ i j, L1Conv P (fun n ω => (∑ k ∈ range n, S i k * g k ω) *
      (∑ k ∈ range n, S j k * g k ω)) (fun ω => G i ω * G j ω) := fun i j =>
    prod_tendsto_L1 (hmem i) (hmem j) (hG i) (hG j)
  have hcc : ∀ i j, L1Conv P (fun n (_ : Ω) => ∑ k ∈ range n, S i k * S j k) (fun _ => Cm i j) :=
    fun i j => L1Conv.const (hS i j).tendsto_sum_nat
  have hX : L1Conv P (chaosSection A g)
      (fun ω => (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, B i j * (G i ω * G j ω - Cm i j)) := by
    rw [funext hY]
    refine L1Conv.const_mul (1 / 2) ?_
    refine L1Conv.sum _ fun i _ => L1Conv.sum _ fun j _ => ?_
    exact L1Conv.const_mul _ ((hprod i j).sub (hcc i j))
  have hC : L1Conv P (chaosSection A g) (chaos P A g) :=
    L1Conv.of_L2 (fun n => (memLp_quadSum hg A n).const_mul (1 / 2) |>.aestronglyMeasurable)
      (chaos_tendsto P A hAs g hg)
  exact hX.ae_unique hC

end Main

end HRS.MC.IID
