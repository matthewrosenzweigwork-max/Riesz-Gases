import HRS.MS.S11Q2C1

/-!
# S11.3 Liouville (worker S11Q2), C5: the measurable limit of the Euler maps

For a drift `b~`, a noise coefficient `σ`, a time `t` and a "grid vector" `v : ℕ × ℕ → E` (the noise values `v (j,k) = W(j t / 2^k)`):
`s11q2_eK k (x,v)` is the `2^k`-step Euler scheme (step `t/2^k`, increments `σ (v(j+1,k) - v(j,k))`), `s11q2_Fs` the limit.  They are measurable in `(x,v)`,
the convergence set `s11q2_Sset` is measurable, `s11q2_Fs (·, v)` is lower Lipschitz (constant `e^{-2Lt}`) on its slice of the convergence set,
and a solution `y` with noise `c` is recovered: `s11q2_Fs (y 0, v) = y t`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S11Q2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The `2^k`-step Euler map. -/
def s11q2_eK (bt : E → E) (σ t : ℝ) (k : ℕ) (p : E × (ℕ × ℕ → E)) : E :=
  s11q2_eul (t / 2 ^ k) bt (fun i => σ • (p.2 (i + 1, k) - p.2 (i, k))) p.1 (2 ^ k)

theorem s11q2_eul_measurable {α : Type*} [MeasurableSpace α] {bt : E → E} (hbc : Continuous bt) (h : ℝ)
    (inc : α → ℕ → E) (hinc : ∀ j, Measurable fun a => inc a j) {x : α → E} (hx : Measurable x) (j : ℕ) :
    Measurable fun a => s11q2_eul h bt (inc a) (x a) j := by
  induction j with
  | zero => simpa [s11q2_eul] using hx
  | succ j ih =>
    simp only [s11q2_eul]
    exact (ih.add ((hbc.measurable.comp ih).const_smul h)).add (hinc j)

theorem s11q2_eK_measurable {bt : E → E} (hbc : Continuous bt) (σ t : ℝ) (k : ℕ) :
    Measurable (s11q2_eK bt σ t k) := by
  unfold s11q2_eK
  refine s11q2_eul_measurable hbc _ (fun (p : E × (ℕ × ℕ → E)) j => σ • (p.2 (j + 1, k) - p.2 (j, k))) (fun j => ?_) measurable_fst _
  exact (((measurable_pi_apply (j + 1, k)).comp measurable_snd).sub
    ((measurable_pi_apply (j, k)).comp measurable_snd)).const_smul σ

/-- The convergence set of the Euler maps. -/
def s11q2_Sset (bt : E → E) (σ t : ℝ) : Set (E × (ℕ × ℕ → E)) :=
  {p | ∃ c, Tendsto (fun k => s11q2_eK bt σ t k p) atTop (𝓝 c)}

/-- The limit of the Euler maps. -/
def s11q2_Fs (bt : E → E) (σ t : ℝ) (p : E × (ℕ × ℕ → E)) : E :=
  limUnder atTop (fun k => s11q2_eK bt σ t k p)

theorem s11q2_Sset_measurable {bt : E → E} (hbc : Continuous bt) (σ t : ℝ) : MeasurableSet (s11q2_Sset bt σ t) :=
  MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto (fun k => (s11q2_eK_measurable hbc σ t k).stronglyMeasurable)

theorem s11q2_Fs_measurable {bt : E → E} (hbc : Continuous bt) (σ t : ℝ) : Measurable (s11q2_Fs bt σ t) :=
  (MeasureTheory.StronglyMeasurable.limUnder (fun k => (s11q2_eK_measurable hbc σ t k).stronglyMeasurable)).measurable

theorem s11q2_Fs_lower {bt : E → E} {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖) (σ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) {x x' : E} {v : ℕ × ℕ → E} (hx : (x, v) ∈ s11q2_Sset bt σ t) (hx' : (x', v) ∈ s11q2_Sset bt σ t) :
    Real.exp (-2 * L * t) * ‖x - x'‖ ≤ ‖s11q2_Fs bt σ t (x, v) - s11q2_Fs bt σ t (x', v)‖ := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨c', hc'⟩ := hx'
  have e1 : s11q2_Fs bt σ t (x, v) = c := hc.limUnder_eq
  have e2 : s11q2_Fs bt σ t (x', v) = c' := hc'.limUnder_eq
  rw [e1, e2]
  have hh0 : Tendsto (fun k : ℕ => t / 2 ^ k * L) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => t / 2 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    simpa using this.mul_const L
  have hev : ∀ᶠ k : ℕ in atTop, t / 2 ^ k * L ≤ 1 / 2 := hh0.eventually (ge_mem_nhds (by norm_num))
  refine ge_of_tendsto (hc.sub hc').norm ?_
  filter_upwards [hev] with k hk
  have hu0 : 0 ≤ t / 2 ^ k * L := by positivity
  have h1 := s11q2_eul_lower (bt := bt) (L := L) (h := t / 2 ^ k) (by positivity) hL hL0 hk
    (fun i => σ • (v (i + 1, k) - v (i, k))) x x' (2 ^ k)
  have h2 := s11q2_pow_lower hu0 hk (2 ^ k)
  have h3 : -2 * (t / 2 ^ k * L) * ((2 ^ k : ℕ) : ℝ) = -2 * L * t := by
    push_cast; field_simp
  rw [h3] at h2
  show _ ≤ ‖s11q2_eul (t / 2 ^ k) bt (fun i => σ • (v (i + 1, k) - v (i, k))) x (2 ^ k) -
    s11q2_eul (t / 2 ^ k) bt (fun i => σ • (v (i + 1, k) - v (i, k))) x' (2 ^ k)‖
  exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1

/-- Recovering a solution. -/
theorem s11q2_Fs_sol {bt : E → E} {L M t : ℝ} {y c : ℝ → E} (H : s11q2_Sol bt L M t y c) (ht : 0 ≤ t) (σ : ℝ)
    {v : ℕ × ℕ → E} (hv : ∀ i k : ℕ, σ • (v (i + 1, k) - v (i, k)) = c (((i : ℝ) + 1) * (t / 2 ^ k)) - c (i * (t / 2 ^ k))) :
    (y 0, v) ∈ s11q2_Sset bt σ t ∧ s11q2_Fs bt σ t (y 0, v) = y t := by
  have hT := s11q2_eul_tendsto H ht
  have e : (fun k => s11q2_eK bt σ t k (y 0, v)) =
      fun k : ℕ => s11q2_eul (t / 2 ^ k) bt (fun i => c ((i + 1) * (t / 2 ^ k)) - c (i * (t / 2 ^ k))) (y 0) (2 ^ k) := by
    funext k
    simp only [s11q2_eK]
    congr 1
    funext i
    exact hv i k
  rw [← e] at hT
  exact ⟨⟨_, hT⟩, hT.limUnder_eq⟩

end HRS.MS.S11Q2

end
