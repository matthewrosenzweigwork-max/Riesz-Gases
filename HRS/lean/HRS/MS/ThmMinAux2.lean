import HRS.MS.ThmMinAux1

/-!
# THM-3 (part 2): existence of a minimiser of `G` on `C_M`

Main result `HRS.MS.Thm.exists_min_Cset`: for `ThmSetting K r B`, `1 ≤ M`, `0 < β`, there is `μ ∈ Cset r M` with
`Gfun K r β μ ≤ Gfun K r β l` for all `l ∈ Cset r M`.

Route (see `docs/SUPP_FOUND_PACKETS.md`, THM-3): `G` is bounded below on `C_M`; the midpoint inequality of
`ThmMinAux1` (strong convexity of `t log t` on `[0, M]` plus (K2)) shows that a minimising sequence is Cauchy in
`L²(dx)` after the substitution `S ρ = ρ / √r` (so that `‖S ρ₁ - S ρ₂‖² = ∫ (ρ₁ - ρ₂)² / r`); completeness of
`Lp` gives an almost-everywhere convergent subsequence; the limit is clamped to `min (max · 0) (M r)` so that it
lies in `C_M` everywhere; `G` is continuous along bounded almost-everywhere convergent sequences by dominated
convergence (so no Lipschitz estimate is needed: `t log t` is not Lipschitz at `0`).

Adjustments relative to the sketch (all recorded in `docs/THM_REVIEW_NOTES.md`): `1 ≤ M` (otherwise `C_M = ∅`)
and `0 < β` are assumed instead of `0 < M`.  All Bochner integrals of `G` on `C_M` are genuine (Aux1).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

section Continuity

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}

lemma t3_cont_ent {c : ℝ} (hc : 0 < c) : Continuous fun t : ℝ => t * Real.log (t / c) := by
  have h : (fun t : ℝ => t * Real.log (t / c)) = fun t => c * ((t / c) * Real.log (t / c)) := by
    funext t
    field_simp
  rw [h]
  exact (Real.continuous_mul_log.comp (continuous_id.div_const c)).const_mul c

/-- `G` is continuous along bounded almost-everywhere convergent sequences in `C_M`. -/
lemma t3_G_tendsto (hS : ThmSetting K r B) (hM : 1 ≤ M) (β : ℝ) {ρ : ℕ → Euc d → ℝ} {ρ₀ : Euc d → ℝ}
    (hρ : ∀ n, ρ n ∈ Cset r M) (hρ₀ : ρ₀ ∈ Cset r M)
    (hae : ∀ᵐ x, Tendsto (fun n => ρ n x) atTop (𝓝 (ρ₀ x))) :
    Tendsto (fun n => Gfun K r β (ρ n)) atTop (𝓝 (Gfun K r β ρ₀)) := by
  have hr : Measurable r := hS.r_prob.measurable
  -- entropy part
  have hent : Tendsto (fun n => relEnt (ρ n) r) atTop (𝓝 (relEnt ρ₀ r)) := by
    unfold relEnt
    refine tendsto_integral_of_dominated_convergence (fun x => M ^ 2 * r x) (fun n => ?_)
      ((t3_r_integrable hS).const_mul _) (fun n => ?_) ?_
    · exact ((hρ n).1.measurable.mul (Real.measurable_log.comp
        ((hρ n).1.measurable.div hr))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact t3_ent_abs hS hM (hρ n) x
    · filter_upwards [hae] with x hx
      exact ((t3_cont_ent (hS.r_pos x)).tendsto (ρ₀ x)).comp hx
  -- pair part
  have hpair : Tendsto (fun n => pairE K (ρ n) (ρ n)) atTop (𝓝 (pairE K ρ₀ ρ₀)) := by
    have e : ∀ n, pairE K (ρ n) (ρ n) = ∫ p : Euc d × Euc d, K p.1 p.2 * ρ n p.1 * ρ n p.2
        ∂((volume : Measure (Euc d)).prod volume) := fun n =>
      t3_pairE_eq (t3_pairE_integrable hS (hρ n) (hρ n))
    rw [t3_pairE_eq (t3_pairE_integrable hS hρ₀ hρ₀)]
    simp only [e]
    refine tendsto_integral_of_dominated_convergence (fun p => M * M * (K p.1 p.2 * r p.1 * r p.2))
      (fun n => ?_) ((t3_W_integrable hS).const_mul _) (fun n => ?_) ?_
    · exact (t3_pairE_integrable hS (hρ n) (hρ n)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      have hk := hS.nonneg p.1 p.2
      have a1 := (hρ n).1.nonneg p.1
      have a2 := (hρ n).1.nonneg p.2
      have b1 := (hρ n).2 p.1
      have b2 := (hρ n).2 p.2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hk a1) a2)]
      calc K p.1 p.2 * ρ n p.1 * ρ n p.2 ≤ K p.1 p.2 * (M * r p.1) * (M * r p.2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left b1 hk) b2 a2 (mul_nonneg hk (a1.trans b1))
        _ = M * M * (K p.1 p.2 * r p.1 * r p.2) := by ring
    · have h1 : ∀ᵐ p : Euc d × Euc d ∂((volume : Measure (Euc d)).prod volume),
          Tendsto (fun n => ρ n p.1) atTop (𝓝 (ρ₀ p.1)) :=
        Measure.quasiMeasurePreserving_fst.ae hae
      have h2 : ∀ᵐ p : Euc d × Euc d ∂((volume : Measure (Euc d)).prod volume),
          Tendsto (fun n => ρ n p.2) atTop (𝓝 (ρ₀ p.2)) :=
        Measure.quasiMeasurePreserving_snd.ae hae
      filter_upwards [h1, h2] with p hp1 hp2
      exact (tendsto_const_nhds.mul hp1).mul hp2
  unfold Gfun
  exact (hent.const_mul _).add (hpair.const_mul _)

end Continuity

section LpPart

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}

/-- `S ρ = ρ / √r`, so that `‖S ρ₁ - S ρ₂‖²_{L²(dx)} = ∫ (ρ₁ - ρ₂)² / r`. -/
def t3S (r ρ : Euc d → ℝ) : Euc d → ℝ := fun x => ρ x / Real.sqrt (r x)

lemma t3_S_sq (hS : ThmSetting K r B) (ρ : Euc d → ℝ) (x : Euc d) :
    (t3S r ρ x) ^ 2 = ρ x ^ 2 / r x := by
  unfold t3S
  rw [div_pow, Real.sq_sqrt (hS.r_pos x).le]

lemma t3_S_sub_sq (hS : ThmSetting K r B) (ρ₁ ρ₂ : Euc d → ℝ) (x : Euc d) :
    (t3S r ρ₁ x - t3S r ρ₂ x) ^ 2 = (ρ₁ x - ρ₂ x) ^ 2 / r x := by
  unfold t3S
  rw [← sub_div, div_pow, Real.sq_sqrt (hS.r_pos x).le]

lemma t3_S_measurable (hS : ThmSetting K r B) {ρ : Euc d → ℝ} (hρ : Measurable ρ) :
    Measurable (t3S r ρ) :=
  hρ.div (hS.r_prob.measurable.sqrt)

lemma t3_S_memLp (hS : ThmSetting K r B) {ρ : Euc d → ℝ} (hρ : ρ ∈ Cset r M) :
    MemLp (t3S r ρ) 2 (volume : Measure (Euc d)) := by
  have hm := t3_S_measurable hS hρ.1.measurable
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine ((t3_r_integrable hS).const_mul (M ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hrx := hS.r_pos x
  rw [Real.norm_of_nonneg (sq_nonneg _), t3_S_sq hS, div_le_iff₀ hrx]
  have a := hρ.1.nonneg x
  have b := hρ.2 x
  nlinarith

lemma t3_Lp_norm_sq (F : Lp ℝ 2 (volume : Measure (Euc d))) : ‖F‖ ^ 2 = ∫ x, (F x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

lemma t3_Lp_dist_sq (hS : ThmSetting K r B) {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M)
    (h₂ : ρ₂ ∈ Cset r M) :
    ‖(t3_S_memLp hS h₁).toLp (t3S r ρ₁) - (t3_S_memLp hS h₂).toLp (t3S r ρ₂)‖ ^ 2 = t3D r ρ₁ ρ₂ := by
  rw [t3_Lp_norm_sq]
  unfold t3D
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((t3_S_memLp hS h₁).toLp (t3S r ρ₁)) ((t3_S_memLp hS h₂).toLp (t3S r ρ₂)),
    (t3_S_memLp hS h₁).coeFn_toLp, (t3_S_memLp hS h₂).coeFn_toLp] with x hx hx1 hx2
  rw [hx, Pi.sub_apply, hx1, hx2, t3_S_sub_sq hS]

/-- A minimising sequence is Cauchy in `L²`. -/
lemma t3_cauchy (hS : ThmSetting K r B) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < β) {ρ : ℕ → Euc d → ℝ}
    (hρ : ∀ n, ρ n ∈ Cset r M) {m : ℝ} (hm : ∀ l ∈ Cset r M, m ≤ Gfun K r β l)
    (hlim : Tendsto (fun n => Gfun K r β (ρ n)) atTop (𝓝 m)) :
    CauchySeq (fun n => (t3_S_memLp hS (hρ n)).toLp (t3S r (ρ n))) := by
  have hM0 : 0 < M := by linarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hδ : 0 < ε ^ 2 / (8 * M * β) := by positivity
  have hev := (hlim.eventually (gt_mem_nhds (show m < m + ε ^ 2 / (8 * M * β) by linarith)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun a ha b hb => ?_⟩
  rw [dist_eq_norm]
  have hmid := t3_G_mid hS hM hβ (hρ a) (hρ b)
  have hmm := hm _ (t3_mid_mem hS (hρ a) (hρ b))
  have hD := t3_Lp_dist_sq hS (hρ a) (hρ b)
  have h1 := hN a ha
  have h2 := hN b hb
  have hq : t3D r (ρ a) (ρ b) / (8 * M * β) < ε ^ 2 / (8 * M * β) := by linarith
  have hq' := (div_lt_div_iff_of_pos_right (by positivity : 0 < 8 * M * β)).1 hq
  by_contra hcon
  rw [not_lt] at hcon
  have : ε ^ 2 ≤ ‖(t3_S_memLp hS (hρ a)).toLp (t3S r (ρ a)) - (t3_S_memLp hS (hρ b)).toLp (t3S r (ρ b))‖ ^ 2 :=
    pow_le_pow_left₀ hε.le hcon 2
  linarith

/-- Almost-everywhere limit in `C_M`. -/
lemma t3_limit_mem (hS : ThmSetting K r B) {ρ : ℕ → Euc d → ℝ} (hρ : ∀ n, ρ n ∈ Cset r M)
    {ρ₀ : Euc d → ℝ} (hm : Measurable ρ₀) (h0 : ∀ x, 0 ≤ ρ₀ x) (hle : ∀ x, ρ₀ x ≤ M * r x)
    (hae : ∀ᵐ x, Tendsto (fun n => ρ n x) atTop (𝓝 (ρ₀ x))) : ρ₀ ∈ Cset r M := by
  refine ⟨⟨h0, hm, ?_⟩, hle⟩
  have hT := tendsto_integral_of_dominated_convergence (fun x => M * r x)
    (fun n => (hρ n).1.measurable.aestronglyMeasurable) ((t3_r_integrable hS).const_mul M)
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg ((hρ n).1.nonneg x)]; exact (hρ n).2 x) hae
  have h1 : Tendsto (fun n => ∫ x, ρ n x) atTop (𝓝 1) := by
    simp only [(hρ _).1.integral_one]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hT h1

/-- Extraction of an almost-everywhere convergent subsequence, with limit in `C_M` everywhere. -/
lemma t3_limit (hS : ThmSetting K r B) {ρ : ℕ → Euc d → ℝ} (hρ : ∀ n, ρ n ∈ Cset r M)
    (hC : CauchySeq (fun n => (t3_S_memLp hS (hρ n)).toLp (t3S r (ρ n)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ ρ₀ ∈ Cset r M,
      ∀ᵐ x, Tendsto (fun i => ρ (ns i) x) atTop (𝓝 (ρ₀ x)) := by
  have hM0 : 0 ≤ M := by
    have := hρ 0
    have a := this.1.nonneg 0
    have b := this.2 0
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [hS.r_pos 0]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hall : ∀ᵐ x, ∀ n, (((t3_S_memLp hS (hρ n)).toLp (t3S r (ρ n)) : Lp ℝ 2 (volume : Measure (Euc d))) x
      = t3S r (ρ n) x) :=
    ae_all_iff.2 fun n => (t3_S_memLp hS (hρ n)).coeFn_toLp
  have hLm : Measurable (fun x => (L : Euc d → ℝ) x) := (Lp.stronglyMeasurable L).measurable
  have hsq : Measurable (fun x => Real.sqrt (r x)) := hS.r_prob.measurable.sqrt
  set ρ₀ : Euc d → ℝ := fun x => min (max ((L : Euc d → ℝ) x * Real.sqrt (r x)) 0) (M * r x) with hρ₀
  have hlim : ∀ᵐ x, Tendsto (fun i => ρ (ns i) x) atTop (𝓝 ((L : Euc d → ℝ) x * Real.sqrt (r x))) := by
    filter_upwards [hall, hae] with x hx hx2
    have h3 := hx2.mul_const (Real.sqrt (r x))
    refine h3.congr fun i => ?_
    rw [hx (ns i)]
    unfold t3S
    have : Real.sqrt (r x) ≠ 0 := (Real.sqrt_pos.2 (hS.r_pos x)).ne'
    field_simp
  have hmem : ∀ᵐ x, ρ₀ x = (L : Euc d → ℝ) x * Real.sqrt (r x) := by
    filter_upwards [hlim] with x hx
    have h1 : 0 ≤ (L : Euc d → ℝ) x * Real.sqrt (r x) :=
      ge_of_tendsto' hx fun i => (hρ (ns i)).1.nonneg x
    have h2 : (L : Euc d → ℝ) x * Real.sqrt (r x) ≤ M * r x :=
      le_of_tendsto' hx fun i => (hρ (ns i)).2 x
    simp only [hρ₀]
    rw [max_eq_left h1, min_eq_left h2]
  have hae' : ∀ᵐ x, Tendsto (fun i => ρ (ns i) x) atTop (𝓝 (ρ₀ x)) := by
    filter_upwards [hlim, hmem] with x hx hx2
    rw [hx2]; exact hx
  refine ⟨ns, hns, ρ₀, ?_, hae'⟩
  refine t3_limit_mem hS (fun i => hρ (ns i)) ?_ (fun x => ?_) (fun x => ?_) hae'
  · exact ((hLm.mul hsq).max measurable_const).min (measurable_const.mul hS.r_prob.measurable)
  · exact le_min (le_max_right _ _) (mul_nonneg hM0 (hS.r_pos x).le)
  · exact min_le_right _ _

end LpPart

section Main

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B M : ℝ}

/-- A minimising sequence in `C_M`. -/
lemma t3_minseq (hS : ThmSetting K r B) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < β) :
    ∃ (ρ : ℕ → Euc d → ℝ) (m : ℝ), (∀ n, ρ n ∈ Cset r M) ∧ (∀ l ∈ Cset r M, m ≤ Gfun K r β l) ∧
      Tendsto (fun n => Gfun K r β (ρ n)) atTop (𝓝 m) := by
  have hr0 : r ∈ Cset r M :=
    ⟨hS.r_prob, fun x => le_mul_of_one_le_left (hS.r_pos x).le hM⟩
  have : Nonempty {ρ : Euc d → ℝ // ρ ∈ Cset r M} := ⟨⟨r, hr0⟩⟩
  set m : ℝ := ⨅ ρ : {ρ : Euc d → ℝ // ρ ∈ Cset r M}, Gfun K r β ρ.1 with hm
  have hbdd : BddBelow (Set.range fun ρ : {ρ : Euc d → ℝ // ρ ∈ Cset r M} => Gfun K r β ρ.1) :=
    ⟨-β⁻¹, by rintro _ ⟨ρ, rfl⟩; exact t3_G_ge hS hM hβ ρ.2⟩
  have hge : ∀ l ∈ Cset r M, m ≤ Gfun K r β l := fun l hl => ciInf_le hbdd (⟨l, hl⟩ : {ρ // ρ ∈ Cset r M})
  have hex : ∀ n : ℕ, ∃ ρ : {ρ : Euc d → ℝ // ρ ∈ Cset r M}, Gfun K r β ρ.1 < m + 1 / ((n : ℝ) + 1) :=
    fun n => exists_lt_of_ciInf_lt (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                       linarith)
  choose ρ hρ using hex
  refine ⟨fun n => (ρ n).1, m, fun n => (ρ n).2, hge, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds (x := m)).add tendsto_one_div_add_atTop_nhds_zero_nat)
    (fun n => hge _ (ρ n).2) (fun n => (hρ n).le)

/-- **THM-3.**  Existence of a minimiser of `G = β⁻¹ H(· | r) + ½ E_K` on `C_M = {ρ prob. density, ρ ≤ M r}`.
Assumes `1 ≤ M` (otherwise `C_M` is empty) and `0 < β`; the minimiser satisfies `ρ ≤ M r` at every point. -/
theorem exists_min_Cset (hS : ThmSetting K r B) (hM : 1 ≤ M) {β : ℝ} (hβ : 0 < β) :
    ∃ μ ∈ Cset r M, ∀ l ∈ Cset r M, Gfun K r β μ ≤ Gfun K r β l := by
  obtain ⟨ρ, m, hρ, hm, hlim⟩ := t3_minseq hS hM hβ
  obtain ⟨ns, hns, ρ₀, hρ₀, hae⟩ := t3_limit hS hρ (t3_cauchy hS hM hβ hρ hm hlim)
  refine ⟨ρ₀, hρ₀, fun l hl => ?_⟩
  have h1 := t3_G_tendsto hS hM β (ρ := fun i => ρ (ns i)) (fun i => hρ (ns i)) hρ₀ hae
  have h2 := hlim.comp hns.tendsto_atTop
  have : Gfun K r β ρ₀ = m := tendsto_nhds_unique h1 h2
  rw [this]
  exact hm l hl

end Main

end HRS.MS.Thm

end
