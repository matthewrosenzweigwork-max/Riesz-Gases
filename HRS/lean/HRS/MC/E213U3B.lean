import HRS.MC.E213U3A

/-!
# Packet E213U3, part B: the `L¹` version of the series bound (continuous coefficients)

From the bounded theorem `E213M.e213m_series` (sup norm times length) to the `L¹` bound
`‖𝒥(z; (α,β])‖ ≤ C ∫_{(α,β]} ‖z‖` for continuous `z`: one cell estimate (constant coefficient up to `ε`),
and a Riemann-sum induction using uniform continuity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- A coefficient bounded on `[0,G]` has integrable norm on every measurable `I ⊆ (0,G]`. -/
theorem u3_integrableOn_bdd {r : ℝ} {z : ℝ → NegSobolev d r} (hz : Measurable z) {G M : ℝ}
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖z u‖ ≤ M) {I : Set ℝ} (hI : MeasurableSet I)
    (hIsub : I ⊆ Set.Ioc 0 G) : IntegrableOn (fun u => ‖z u‖) I := by
  have hfin : volume I < ∞ :=
    lt_of_le_of_lt (measure_mono hIsub) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
  refine Measure.integrableOn_of_bounded (M := M) hfin.ne hz.norm.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hI]
  refine Filter.Eventually.of_forall fun u hu => ?_
  have := hM u ⟨(hIsub hu).1.le, (hIsub hu).2⟩
  rwa [norm_norm]

theorem u3_intOK_bdd (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) {z : ℝ → NegSobolev d r} (hz : Measurable z) {M : ℝ}
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖z u‖ ≤ M) {I : Set ℝ} (hI : MeasurableSet I)
    (hIsub : I ⊆ Set.Ioc 0 G) : IntOK Rb r m G z I :=
  u3_intOK Rb r hr m hm G hG z hz hI hIsub (u3_integrableOn_bdd hz hM hI hIsub)

/-- **One cell**: if `z` is within `ε` of the constant `x` on `(a,b]`, then `‖𝒥(z;(a,b])‖ ≤ C (‖x‖+ε)(b-a)`. -/
theorem u3_cell (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (g : ℝ → NegSobolev d r), Measurable g → ∀ M : ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) G, ‖g u‖ ≤ M) → ∀ (x : NegSobolev d r) (ε : ℝ), 0 ≤ ε →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ G → (∀ u ∈ Set.Ioc a b, ‖g u - x‖ ≤ ε) →
      ∃ J, SJ (HRS.MC.E213F.shift R b₀ hb₀) r m G g (Set.Ioc a b) J ∧ ‖J‖ ≤ C * (‖x‖ + ε) * (b - a) := by
  classical
  obtain ⟨C₀, hC₀⟩ := u3_bounded R r hr m hm G hG
  refine ⟨|C₀|, abs_nonneg _, fun b₀ hb₀ g hg M hM x ε hε a b ha hab hbG hgx => ?_⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  have hsub : Set.Ioc a b ⊆ Set.Ioc 0 G := fun u hu => ⟨lt_of_le_of_lt ha hu.1, hu.2.trans hbG⟩
  obtain ⟨Jg, hJg, -⟩ := hC₀ b₀ hb₀ g hg M hM a b ha hab hbG
  obtain ⟨Jx, hJx, hJxn⟩ := hC₀ b₀ hb₀ (fun _ => x) measurable_const ‖x‖ (fun u _ => le_rfl) a b ha hab hbG
  set z' : ℝ → NegSobolev d r := fun u => if u ∈ Set.Ioc a b then g u - x else 0 with hz'
  have hz'm : Measurable z' := by
    refine Measurable.ite measurableSet_Ioc (hg.sub measurable_const) measurable_const
  have hz'b : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖z' u‖ ≤ ε := by
    intro u _
    by_cases hu : u ∈ Set.Ioc a b
    · simp only [hz', if_pos hu]; exact hgx u hu
    · simp only [hz', if_neg hu, norm_zero]; exact hε
  obtain ⟨Jz, hJz, hJzn⟩ := hC₀ b₀ hb₀ z' hz'm ε hz'b a b ha hab hbG
  have hdiff : SJ Rb r m G (fun v => g v - (fun _ => x) v) (Set.Ioc a b) (Jg - Jx) :=
    u3_SJ_sub Rb r hr m hm G hG measurableSet_Ioc hJg hJx
      (u3_intOK_bdd Rb r hr m hm G hG hg hM measurableSet_Ioc hsub)
      (u3_intOK_bdd Rb r hr m hm G hG (measurable_const : Measurable fun _ : ℝ => x)
        (fun u _ => le_rfl : ∀ u ∈ Set.Icc (0 : ℝ) G, ‖(fun _ : ℝ => x) u‖ ≤ ‖x‖) measurableSet_Ioc hsub)
  have hdiff' : SJ Rb r m G z' (Set.Ioc a b) (Jg - Jx) :=
    u3_SJ_congr Rb r m G measurableSet_Ioc (fun u hu _ => by simp only [hz', if_pos hu]) hdiff
  have heq : Jg - Jx = Jz := u3_SJ_unique Rb r m G hdiff' hJz
  refine ⟨Jg, hJg, ?_⟩
  have hJg_eq : Jg = Jx + Jz := by rw [← heq]; abel
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  calc ‖Jg‖ = ‖Jx + Jz‖ := by rw [← hJg_eq]
    _ ≤ ‖Jx‖ + ‖Jz‖ := norm_add_le _ _
    _ ≤ C₀ * ‖x‖ * (b - a) + C₀ * ε * (b - a) := add_le_add hJxn hJzn
    _ ≤ |C₀| * ‖x‖ * (b - a) + |C₀| * ε * (b - a) := by
        gcongr <;> exact le_abs_self _
    _ = |C₀| * (‖x‖ + ε) * (b - a) := by ring

/-- **`L¹` bound for continuous coefficients**: `‖𝒥(g;(α,β])‖ ≤ C ∫_{(α,β]} ‖g‖`. -/
theorem u3_cont_L1 (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (g : ℝ → NegSobolev d r), Continuous g →
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ G →
      ∃ J, SJ (HRS.MC.E213F.shift R b₀ hb₀) r m G g (Set.Ioc α β) J ∧
        ‖J‖ ≤ C * ∫ u in Set.Ioc α β, ‖g u‖ := by
  classical
  obtain ⟨C, hC0, hcell⟩ := u3_cell R r hr m hm G hG
  obtain ⟨C₀, hC₀⟩ := u3_bounded R r hr m hm G hG
  refine ⟨C, hC0, fun b₀ hb₀ g hg α β hα hαβ hβG => ?_⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) G)).exists_bound_of_continuousOn hg.continuousOn
  have hgm : Measurable g := hg.measurable
  have hsubG : ∀ a b : ℝ, 0 ≤ a → b ≤ G → Set.Ioc a b ⊆ Set.Ioc 0 G :=
    fun a b ha hb u hu => ⟨lt_of_le_of_lt ha hu.1, hu.2.trans hb⟩
  have hintg : ∀ a b : ℝ, 0 ≤ a → b ≤ G → IntegrableOn (fun u => ‖g u‖) (Set.Ioc a b) :=
    fun a b ha hb => u3_integrableOn_bdd hgm hM measurableSet_Ioc (hsubG a b ha hb)
  have hclaim : ∀ ε : ℝ, 0 < ε → ∃ J, SJ Rb r m G g (Set.Ioc α β) J ∧
      ‖J‖ ≤ C * (∫ u in Set.Ioc α β, ‖g u‖) + 2 * C * ε * (β - α) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc : IsCompact (Set.Icc α β)).uniformContinuousOn_of_continuous hg.continuousOn) ε hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < n ∧ (β - α) / n < δ := by
      refine ⟨⌈(β - α) / δ⌉₊ + 1, Nat.succ_pos _, ?_⟩
      have h1 : (β - α) / δ ≤ ⌈(β - α) / δ⌉₊ := Nat.le_ceil _
      have h2 : (β - α) / δ < ((⌈(β - α) / δ⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hn0 : (0 : ℝ) < ((⌈(β - α) / δ⌉₊ + 1 : ℕ) : ℝ) := by positivity
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hδ] at h2
      linarith
    obtain ⟨hnpos, hnδ⟩ := hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    set h : ℝ := (β - α) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hαβ) hnR.le
    have hnh : (n : ℝ) * h = β - α := by rw [hh]; field_simp
    have key : ∀ k : ℕ, k ≤ n → ∃ J, SJ Rb r m G g (Set.Ioc α (α + k * h)) J ∧
        ‖J‖ ≤ C * (∫ u in Set.Ioc α (α + k * h), ‖g u‖) + 2 * C * ε * (k * h) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨0, ?_, ?_⟩
        · simpa using u3_SJ_empty Rb r m G g
        · simp
      | succ k ih =>
        intro hk
        obtain ⟨J, hJ, hJn⟩ := ih (Nat.le_of_succ_le hk)
        set a : ℝ := α + k * h with ha
        set b : ℝ := α + ((k + 1 : ℕ) : ℝ) * h with hb
        have hkh : (k : ℝ) * h ≥ 0 := by positivity
        have hαa : α ≤ a := by rw [ha]; linarith
        have hab : a ≤ b := by rw [ha, hb]; push_cast; nlinarith
        have hk1 : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
        have hbβ : b ≤ β := by
          rw [hb]
          have : ((k + 1 : ℕ) : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hk1 hh0
          linarith
        have hba : b - a = h := by rw [ha, hb]; push_cast; ring
        have ha0 : 0 ≤ a := hα.trans hαa
        have hbG : b ≤ G := hbβ.trans hβG
        have hgx : ∀ u ∈ Set.Ioc a b, ‖g u - g a‖ ≤ ε := by
          intro u hu
          have hua : u - a ≤ h := by linarith [hu.2]
          have hu1 : u ∈ Set.Icc α β := ⟨hαa.trans hu.1.le, hu.2.trans hbβ⟩
          have ha1 : a ∈ Set.Icc α β := ⟨hαa, hab.trans hbβ⟩
          have hd : dist u a < δ := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
            linarith
          have := hδε u hu1 a ha1 hd
          rw [dist_eq_norm] at this
          exact this.le
        obtain ⟨Jc, hJc, hJcn⟩ := hcell b₀ hb₀ g hgm M hM (g a) ε hε.le a b ha0 hab hbG hgx
        -- integral comparison on the cell
        have hcellint : h * (‖g a‖ - ε) ≤ ∫ u in Set.Ioc a b, ‖g u‖ := by
          have h1 : ∫ u in Set.Ioc a b, (‖g a‖ - ε) ≤ ∫ u in Set.Ioc a b, ‖g u‖ := by
            refine setIntegral_mono_on (integrable_const _) (hintg a b ha0 hbG) measurableSet_Ioc ?_
            intro u hu
            have := hgx u hu
            have h2 : ‖g a‖ ≤ ‖g u‖ + ‖g u - g a‖ := by
              have := norm_sub_norm_le (g a) (g u)
              rw [norm_sub_rev] at this
              linarith [norm_sub_rev (g a) (g u)]
            linarith
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab, hba] at h1
          exact h1
        have hunion : Set.Ioc α a ∪ Set.Ioc a b = Set.Ioc α b := Set.Ioc_union_Ioc_eq_Ioc hαa hab
        have hdisj : Disjoint (Set.Ioc α a) (Set.Ioc a b) := by
          refine Set.disjoint_left.2 fun x hx hx' => ?_
          exact absurd hx.2 (not_le.2 hx'.1)
        refine ⟨J + Jc, ?_, ?_⟩
        · have := u3_SJ_union Rb r m G hdisj measurableSet_Ioc hJ hJc
            (u3_intOK_bdd Rb r hr m hm G hG hgm hM measurableSet_Ioc (hsubG α a hα (hab.trans hbG)))
            (u3_intOK_bdd Rb r hr m hm G hG hgm hM measurableSet_Ioc (hsubG a b ha0 hbG))
          rwa [hunion] at this
        · have hI : ∫ u in Set.Ioc α b, ‖g u‖ =
              (∫ u in Set.Ioc α a, ‖g u‖) + ∫ u in Set.Ioc a b, ‖g u‖ := by
            rw [← hunion]
            exact setIntegral_union hdisj measurableSet_Ioc (hintg α a hα (hab.trans hbG)) (hintg a b ha0 hbG)
          rw [hI]
          have e1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
          have hCn : C * (‖g a‖ + ε) * (b - a) ≤ C * (∫ u in Set.Ioc a b, ‖g u‖) + 2 * C * ε * h := by
            rw [hba]
            nlinarith [mul_le_mul_of_nonneg_left hcellint hC0]
          calc ‖J + Jc‖ ≤ ‖J‖ + ‖Jc‖ := norm_add_le _ _
            _ ≤ (C * (∫ u in Set.Ioc α a, ‖g u‖) + 2 * C * ε * (k * h)) +
                (C * (∫ u in Set.Ioc a b, ‖g u‖) + 2 * C * ε * h) := add_le_add hJn (hJcn.trans hCn)
            _ = C * ((∫ u in Set.Ioc α a, ‖g u‖) + ∫ u in Set.Ioc a b, ‖g u‖) +
                2 * C * ε * (((k + 1 : ℕ) : ℝ) * h) := by rw [e1]; ring
    obtain ⟨J, hJ, hJn⟩ := key n le_rfl
    have hend : α + (n : ℝ) * h = β := by linarith
    rw [hend] at hJ hJn
    exact ⟨J, hJ, by rw [hnh] at hJn; exact hJn⟩
  -- existence from the bounded theorem and uniqueness
  obtain ⟨J₀, hJ₀, -⟩ := hC₀ b₀ hb₀ g hgm M hM α β hα hαβ hβG
  refine ⟨J₀, hJ₀, ?_⟩
  have hall : ∀ ε : ℝ, 0 < ε → ‖J₀‖ ≤ C * (∫ u in Set.Ioc α β, ‖g u‖) + ε * (2 * C * (β - α)) := by
    intro ε hε
    obtain ⟨J, hJ, hJn⟩ := hclaim ε hε
    have : J = J₀ := u3_SJ_unique Rb r m G hJ hJ₀
    rw [← this]
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hz : 2 * C * (β - α) = 0
  · have := hall 1 one_pos
    rw [hz] at this
    linarith
  · have hpos : 0 < 2 * C * (β - α) := by
      have : 0 ≤ 2 * C * (β - α) := by
        have := sub_nonneg.2 hαβ
        positivity
      exact lt_of_le_of_ne this (Ne.symm hz)
    have := hall (ε / (2 * C * (β - α))) (div_pos hε hpos)
    rwa [div_mul_cancel₀ _ hpos.ne'] at this

end HRS.MC.E213U3

end
