import Mathlib
import HRS.Sections.Q41Aux10

/-!
# Packet Q41, helper 11: Kolmogorov continuity for the dyadic `E_m`-valued process
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

open HRS

variable {d : ℕ} {r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ}

/-- Almost surely, all dyadic increments of level `n ≥ n₀(ω, N)` are at most `(9/10)^n`. -/
lemma Q41Fam.ae_incr (F : Q41Fam d r) (hd : 1 ≤ d) {m : ℝ} (hm : (d : ℝ) + 2 < 2 * m) {B Bi : ℝ}
    (hB : ∀ (q : q41_D) (k : NonzeroLattice d), r q q k k ≤ B)
    (hBi : ∀ (q q' : q41_D) (k : NonzeroLattice d),
      r q' q' k k + r q q k k - 2 * r q' q k k ≤ Bi * Lattice.jp k.1 ^ 2 * |(q' : ℝ) - q|) :
    ∀ᵐ ω ∂gpP, ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ℕ, j < N * 2 ^ n →
      ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖ ≤ (9 / 10 : ℝ) ^ n := by
  set M : ℝ := 48 * Real.exp (1 / 2) *
    (|Bi| * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1)))) ^ 2 with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1))) :=
      tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
    positivity
  rw [ae_all_iff]
  intro N
  set s : ℕ → Set (ℕ → ℝ) := fun n => {ω | ∃ j, j < N * 2 ^ n ∧
    (9 / 10 : ℝ) ^ n < ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖} with hs
  have hsb : ∀ n, gpP (s n) ≤ ENNReal.ofReal (N * M * q41_rho ^ n) := by
    intro n
    have hsub : s n ⊆ ⋃ j ∈ Finset.range (N * 2 ^ n),
        {ω | (9 / 10 : ℝ) ^ n <
          ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖} := by
      intro ω hω
      obtain ⟨j, hj, h⟩ := hω
      simp only [Set.mem_iUnion]
      exact ⟨j, Finset.mem_range.2 hj, h⟩
    calc gpP (s n) ≤ gpP (⋃ j ∈ Finset.range (N * 2 ^ n), {ω | (9 / 10 : ℝ) ^ n <
          ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖}) := measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (N * 2 ^ n), gpP {ω | (9 / 10 : ℝ) ^ n <
          ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖} :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (N * 2 ^ n), ENNReal.ofReal (M * (q41_rho / 2) ^ n) :=
        Finset.sum_le_sum fun j _ => F.tail_bound hd hm hB hBi n j
      _ = ENNReal.ofReal (N * M * q41_rho ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        rw [div_pow]
        field_simp
  have hsum : ∑' n, gpP (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsb)
    have hg : Summable fun n : ℕ => (N : ℝ) * M * q41_rho ^ n :=
      (summable_geometric_of_lt_one q41_rho_pos.le q41_rho_lt_one).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := q41_rho_pos; positivity) hg]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hω
  refine ⟨n₀, fun n hn j hj => ?_⟩
  by_contra hcon
  exact hn₀ n hn ⟨j, hj, not_le.1 hcon⟩

/-- The good event: dyadic increments are eventually small, on every `[0, N)`. -/
def Q41Fam.good (F : Q41Fam d r) (m : ℝ) : Set (ℕ → ℝ) :=
  {ω | ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ℕ, j < N * 2 ^ n →
    ‖F.Zbar m (((j : ℝ) + 1) / 2 ^ n) ω - F.Zbar m ((j : ℝ) / 2 ^ n) ω‖ ≤ (9 / 10 : ℝ) ^ n}

lemma Q41Fam.measurableSet_good (F : Q41Fam d r) (hd : 1 ≤ d) (m : ℝ) :
    MeasurableSet (F.good m) := by
  unfold Q41Fam.good
  simp only [Set.setOf_forall, Set.setOf_exists]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n₀ => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (((F.measurable_Zbar hd m _).sub (F.measurable_Zbar hd m _)).norm)
    measurable_const

/-- The continuous extension. -/
def Q41Fam.Zc (F : Q41Fam d r) (m : ℝ) (t : ℝ) (ω : ℕ → ℝ) : NegSobolev d m :=
  open Classical in
  if ω ∈ F.good m then limUnder atTop (fun n : ℕ => F.Zbar m ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) ω) else 0

lemma Q41Fam.Zc_spec (F : Q41Fam d r) (m : ℝ) {ω : ℕ → ℝ} (hω : ω ∈ F.good m) (N : ℕ) :
    ∃ f : ℝ → NegSobolev d m, ContinuousOn f (Set.Ico 0 (N : ℝ)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) N, f t = F.Zc m t ω) ∧
      ∀ n j : ℕ, (j : ℝ) / 2 ^ n < N → f ((j : ℝ) / 2 ^ n) = F.Zbar m ((j : ℝ) / 2 ^ n) ω := by
  obtain ⟨n₀, hn₀⟩ := hω N
  obtain ⟨f, hfc, hft, hfn⟩ := q41_kc_det (fun s => F.Zbar m s ω) N (9 / 10) (by norm_num)
    (by norm_num) n₀ hn₀
  refine ⟨f, hfc, fun t ht => ?_, hfn⟩
  unfold Q41Fam.Zc
  rw [if_pos hω]
  exact ((hft t ht).limUnder_eq).symm

lemma Q41Fam.tendsto_Zc (F : Q41Fam d r) (m : ℝ) {ω : ℕ → ℝ} (hω : ω ∈ F.good m) (t : ℝ) :
    Tendsto (fun n : ℕ => F.Zbar m ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) ω) atTop (𝓝 (F.Zc m t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · have : ∀ n : ℕ, ⌊(2 : ℝ) ^ n * t⌋₊ = 0 := fun n =>
      Nat.floor_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht.le)
    have hz : ∀ n : ℕ, F.Zbar m ((⌊(2 : ℝ) ^ n * t⌋₊ : ℝ) / 2 ^ n) ω = F.Zbar m 0 ω := fun n => by
      rw [this n]; simp
    have hZc : F.Zc m t ω = F.Zbar m 0 ω := by
      unfold Q41Fam.Zc
      rw [if_pos hω]
      simp_rw [hz]
      exact tendsto_const_nhds.limUnder_eq
    rw [hZc]
    simp_rw [hz]
    exact tendsto_const_nhds
  · obtain ⟨n₀, hn₀⟩ := hω (⌈t⌉₊ + 1)
    have htN : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil t]
    obtain ⟨f, hfc, hft, hfn⟩ := q41_kc_det (fun s => F.Zbar m s ω) (⌈t⌉₊ + 1) (9 / 10)
      (by norm_num) (by norm_num) n₀ hn₀
    have := hft t ⟨ht, htN⟩
    have e : F.Zc m t ω = f t := by
      unfold Q41Fam.Zc
      rw [if_pos hω]
      exact this.limUnder_eq
    rw [e]; exact this

lemma Q41Fam.continuousOn_Zc (F : Q41Fam d r) (m : ℝ) {ω : ℕ → ℝ} (hω : ω ∈ F.good m) :
    ContinuousOn (fun t => F.Zc m t ω) (Set.Ici 0) := by
  intro t ht
  obtain ⟨f, hfc, hft, -⟩ := F.Zc_spec m hω (⌈t⌉₊ + 1)
  have htN : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil t]
  have h1 : ContinuousWithinAt (fun t => F.Zc m t ω) (Set.Ico 0 ((⌈t⌉₊ + 1 : ℕ) : ℝ)) t :=
    (hfc t ⟨ht, htN⟩).congr (fun s hs => (hft s hs).symm) (hft t ⟨ht, htN⟩).symm
  refine h1.mono_of_mem_nhdsWithin ?_
  rw [← Set.Ici_inter_Iio]
  exact inter_mem_nhdsWithin _ (Iio_mem_nhds htN)

lemma Q41Fam.Zc_dyadic (F : Q41Fam d r) (m : ℝ) {ω : ℕ → ℝ} (hω : ω ∈ F.good m) (n j : ℕ) :
    F.Zc m ((j : ℝ) / 2 ^ n) ω = F.Zbar m ((j : ℝ) / 2 ^ n) ω := by
  obtain ⟨f, -, hft, hfn⟩ := F.Zc_spec m hω (j + 1)
  have hlt : (j : ℝ) / 2 ^ n < ((j + 1 : ℕ) : ℝ) := by
    push_cast
    have : (j : ℝ) / 2 ^ n ≤ j := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
    linarith
  rw [← hft _ ⟨by positivity, hlt⟩, hfn n j hlt]

lemma Q41Fam.measurable_Zc (F : Q41Fam d r) (hd : 1 ≤ d) (m : ℝ) (t : ℝ) :
    Measurable (F.Zc m t) := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (ω : ℕ → ℝ) =>
    if ω ∈ F.good m then F.Zbar m ((⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n) ω else 0) (fun n => ?_) ?_
  · exact Measurable.ite (F.measurableSet_good hd m) (F.measurable_Zbar hd m _) measurable_const
  · refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hω : ω ∈ F.good m
    · simp only [if_pos hω]; exact F.tendsto_Zc m hω t
    · simp only [if_neg hω]
      have : F.Zc m t ω = 0 := by unfold Q41Fam.Zc; rw [if_neg hω]
      rw [this]; exact tendsto_const_nhds

end HRS.Q41
