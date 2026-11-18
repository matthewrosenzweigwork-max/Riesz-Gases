import HRS.Commutator.Whole.XLIAux29

/-!
# X-LI part 30: Calderón–Zygmund ball selection (Vitali)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Calderón–Zygmund ball selection at height `l` -/
lemma exists_balls (hd : 1 ≤ d) {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) (hfi : ∫⁻ y, f y ≠ ⊤)
    {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ⊤) :
    ∃ (u : Set 𝔼) (r : 𝔼 → ℝ), u.Countable ∧ (∀ b ∈ u, 0 < r b) ∧
      u.PairwiseDisjoint (fun b => closedBall b (r b)) ∧
      (∀ b ∈ u, l * volume (closedBall b (r b)) ≤ ∫⁻ y in closedBall b (r b), f y) ∧
      (∀ b ∈ u, ∫⁻ y in closedBall b (4 * r b), f y ≤ l * volume (closedBall b (4 * r b))) ∧
      {x | l < cmxHLS_Md f x} ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := by
  set S : Set 𝔼 := {x | l < cmxHLS_Md f x} with hS
  set om : ℝ≥0∞ := volume (closedBall (0 : 𝔼) 1) with hom
  have hom0 : om ≠ 0 := cmxHLS_vol_closedBall_ne_zero 0 one_pos
  have homt : om ≠ ⊤ := cmxHLS_vol_closedBall_ne_top 0 1
  have hex : ∀ x ∈ S, ∃ j : ℤ, l * volume (closedBall x ((2 : ℝ) ^ j)) <
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y := by
    intro x hx
    have hx' : l < cmxHLS_Md f x := hx
    unfold cmxHLS_Md at hx'
    obtain ⟨j, hj⟩ := lt_iSup_iff.1 hx'
    refine ⟨j, ?_⟩
    by_contra h
    have h := not_lt.1 h
    have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
    have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
    have : (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤ l :=
      (ENNReal.inv_mul_le_iff h0 h1).2 (by rw [mul_comm]; exact h)
    exact absurd hj (not_lt.2 this)
  set N : ℝ≥0∞ := (∫⁻ y, f y) / (l * om) with hN
  have hlom0 : l * om ≠ 0 := mul_ne_zero hl0 hom0
  have hlomt : l * om ≠ ⊤ := ENNReal.mul_ne_top hlt homt
  have hNt : N ≠ ⊤ := by
    rw [hN]; exact ENNReal.div_ne_top hfi hlom0
  -- bounded above
  have hbd : ∀ x ∈ S, ∀ j : ℤ, l * volume (closedBall x ((2 : ℝ) ^ j)) <
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y → (2 : ℝ) ^ j ≤ max 1 N.toReal := by
    intro x hx j h
    have hle : ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤ ∫⁻ y, f y := setLIntegral_le_lintegral _ _
    have h2 : l * volume (closedBall x ((2 : ℝ) ^ j)) < ∫⁻ y, f y := lt_of_lt_of_le h hle
    rw [cmxHLS_vol_closedBall x (zpow_pos (by norm_num : (0 : ℝ) < 2) j).le] at h2
    have h3 : ENNReal.ofReal (((2 : ℝ) ^ j) ^ d) < N := by
      rw [hN, ENNReal.lt_div_iff_mul_lt (Or.inl hlom0) (Or.inl hlomt)]
      calc ENNReal.ofReal (((2 : ℝ) ^ j) ^ d) * (l * om)
          = l * (ENNReal.ofReal (((2 : ℝ) ^ j) ^ d) * om) := by ring
        _ < _ := h2
    have h4 : ((2 : ℝ) ^ j) ^ d < N.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hNt).1 h3
    by_cases h1 : (2 : ℝ) ^ j ≤ 1
    · exact le_max_of_le_left h1
    · have h1 := not_le.1 h1
      refine le_max_of_le_right ?_
      calc (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ d := le_self_pow₀ h1.le (by omega)
        _ ≤ N.toReal := h4.le
  have hexJ : ∀ x ∈ S, ∃ J : ℤ, (l * volume (closedBall x ((2 : ℝ) ^ J)) <
      ∫⁻ y in closedBall x ((2 : ℝ) ^ J), f y) ∧ ∀ j : ℤ, J < j →
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y ≤ l * volume (closedBall x ((2 : ℝ) ^ j)) := by
    intro x hx
    classical
    set P : ℤ → Prop := fun j => l * volume (closedBall x ((2 : ℝ) ^ j)) <
      ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y with hP
    have hne : ∃ j, P j := hex x hx
    have hub : ∃ b : ℤ, ∀ j, P j → j ≤ b := by
      refine ⟨⌈Real.logb 2 (max 1 N.toReal)⌉, fun j hj => ?_⟩
      have := hbd x hx j hj
      have h2 : (j : ℝ) ≤ Real.logb 2 (max 1 N.toReal) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
        rw [Real.rpow_intCast]; exact this
      have h3 : (j : ℝ) ≤ (⌈Real.logb 2 (max 1 N.toReal)⌉ : ℝ) := h2.trans (Int.le_ceil _)
      exact_mod_cast h3
    obtain ⟨J, hJ, hJmax⟩ := Int.exists_greatest_of_bdd hub hne
    refine ⟨J, hJ, fun j hj => ?_⟩
    by_contra h
    exact absurd (hJmax j (not_le.1 h)) (not_le.2 hj)
  choose! J hJ1 hJ2 using hexJ
  set r : 𝔼 → ℝ := fun x => (2 : ℝ) ^ (J x) with hr
  have hrpos : ∀ x, 0 < r x := fun x => zpow_pos (by norm_num : (0 : ℝ) < 2) _
  obtain ⟨u, huS, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    S id r (max 1 N.toReal) (fun a ha => hbd a ha (J a) (hJ1 a ha)) 4 (by norm_num)
  simp only [id] at hdisj hcov
  refine ⟨u, r, ?_, fun b hb => hrpos b, hdisj, fun b hb => (hJ1 b (huS hb)).le, ?_, ?_⟩
  · refine hdisj.countable_of_nonempty_interior (fun b hb => ?_)
    rw [interior_closedBall b (hrpos b).ne']
    exact nonempty_ball.2 (hrpos b)
  · intro b hb
    have h := hJ2 b (huS hb) (J b + 2) (by omega)
    have e : (4 : ℝ) * r b = (2 : ℝ) ^ (J b + 2) := by
      rw [hr]
      simp only
      rw [zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [e]
    exact h
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    simp only [mem_iUnion]
    exact ⟨b, hb, hab (mem_closedBall_self (hrpos a).le)⟩

/-- Lebesgue differentiation: where the maximal function is `≤ l`, the function is `≤ l` a.e. -/
lemma ae_enorm_le_of_Md_le {F : 𝔼 → ℂ} (hFi : Integrable F) {l : ℝ≥0∞} (hlt : l ≠ ⊤) :
    ∀ᵐ x : 𝔼, cmxHLS_Md (fun y => ‖F y‖ₑ) x ≤ l → ‖F x‖ₑ ≤ l := by
  have hloc : LocallyIntegrable (fun y => ‖F y‖) (volume : Measure 𝔼) := hFi.norm.locallyIntegrable
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure 𝔼)) hloc 1]
    with x hx hMd
  have hδ : Tendsto (fun n : ℕ => ((2 : ℝ) ^ (-(n : ℤ)))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => zpow_pos (by norm_num : (0 : ℝ) < 2) _⟩
    have : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    refine this.congr fun n => ?_
    simp [zpow_neg, one_div]
  have hlim := hx (fun _ => x) (fun n : ℕ => ((2 : ℝ) ^ (-(n : ℤ)))) hδ
    (Eventually.of_forall fun n => by
      rw [one_mul]; exact mem_closedBall_self (zpow_pos (by norm_num) _).le)
  have hle : ∀ n : ℕ, ⨍ y in closedBall x ((2 : ℝ) ^ (-(n : ℤ))), ‖F y‖ ≤ l.toReal := by
    intro n
    set ρ : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hρ
    have hρ0 : 0 < ρ := zpow_pos (by norm_num) _
    have h1 : (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖F y‖ₑ ≤ l :=
      (le_iSup (fun j : ℤ => (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ *
        ∫⁻ y in closedBall x ((2 : ℝ) ^ j), ‖F y‖ₑ) (-(n : ℤ))).trans hMd
    have hvol0 : volume (closedBall x ρ) ≠ 0 := cmxHLS_vol_closedBall_ne_zero x hρ0
    have hvolt : volume (closedBall x ρ) ≠ ⊤ := cmxHLS_vol_closedBall_ne_top x ρ
    rw [setAverage_eq, smul_eq_mul]
    have hI : ∫ y in closedBall x ρ, ‖F y‖ = (∫⁻ y in closedBall x ρ, ‖F y‖ₑ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (closedBall x ρ))
        (Eventually.of_forall fun y => norm_nonneg _) (hFi.norm.aestronglyMeasurable.restrict)]
      congr 1
      refine lintegral_congr fun y => ?_
      rw [ofReal_norm]
    rw [hI]
    have h2 := ENNReal.toReal_mono hlt h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at h2
    simpa [Measure.real] using h2
  have hFx : ‖F x‖ ≤ l.toReal := le_of_tendsto' hlim hle
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖F x‖ ≤ ENNReal.ofReal l.toReal := ENNReal.ofReal_le_ofReal hFx
    _ = l := ENNReal.ofReal_toReal hlt

/-- the disjoint measurable pieces `E_i`, `B_i ⊆ E_i ⊆ 4 B_i`, covering `⋃ 4 B_i` -/
lemma exists_pieces {u : Set 𝔼} (hu : u.Countable) {r : 𝔼 → ℝ} (hr : ∀ b ∈ u, 0 < r b)
    (hdisj : u.PairwiseDisjoint (fun b => closedBall b (r b))) :
    ∃ E : u → Set 𝔼, (∀ i, MeasurableSet (E i)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (∀ i : u, closedBall (i : 𝔼) (r i) ⊆ E i) ∧ (∀ i : u, E i ⊆ closedBall (i : 𝔼) (4 * r i)) ∧
      (⋃ b ∈ u, closedBall b (4 * r b)) ⊆ ⋃ i : u, E i := by
  have : Countable u := hu.to_subtype
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat u
  classical
  set U : Set 𝔼 := ⋃ i : u, closedBall (i : 𝔼) (r i) with hU
  set E : u → Set 𝔼 := fun i => closedBall (i : 𝔼) (r i) ∪
    (closedBall (i : 𝔼) (4 * r i) ∩ Uᶜ ∩
      ⋂ (m : u) (_ : enc m < enc i), (closedBall (m : 𝔼) (4 * r m))ᶜ) with hE
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun i => measurableSet_closedBall
  refine ⟨E, fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_⟩
  · refine measurableSet_closedBall.union ?_
    refine (measurableSet_closedBall.inter hUm.compl).inter ?_
    exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => measurableSet_closedBall.compl
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    have hBd : ∀ a b : u, a ≠ b → ∀ x, x ∈ closedBall (a : 𝔼) (r a) → x ∈ closedBall (b : 𝔼) (r b) → False := by
      intro a b hab x hxa hxb
      have := hdisj a.2 b.2 (fun h => hab (Subtype.ext h))
      exact Set.disjoint_left.1 this hxa hxb
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact hBd i j hij x hxi hxj
    · exact hxj.1.2 (mem_iUnion.2 ⟨i, hxi⟩)
    · exact hxi.1.2 (mem_iUnion.2 ⟨j, hxj⟩)
    · have h1 := hxi.1.1
      have h2 := hxj.1.1
      rcases lt_trichotomy (enc i) (enc j) with h | h | h
      · have := Set.mem_iInter.1 (Set.mem_iInter.1 hxj.2 i) h
        exact this h1
      · exact hij (henc h)
      · have := Set.mem_iInter.1 (Set.mem_iInter.1 hxi.2 j) h
        exact this h2
  · exact Set.subset_union_left
  · intro x hx
    rcases hx with hx | hx
    · exact closedBall_subset_closedBall (by nlinarith [hr i i.2]) hx
    · exact hx.1.1
  · intro x hx
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨b, hb, hxb⟩ := hx
    by_cases hxU : x ∈ U
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hxU
      exact ⟨i, Or.inl hi⟩
    · -- least index
      have hne : ∃ n, ∃ m : u, enc m = n ∧ x ∈ closedBall (m : 𝔼) (4 * r m) :=
        ⟨enc ⟨b, hb⟩, ⟨b, hb⟩, rfl, hxb⟩
      obtain ⟨m, hm⟩ : ∃ m : u, x ∈ closedBall (m : 𝔼) (4 * r m) ∧
          ∀ m' : u, x ∈ closedBall (m' : 𝔼) (4 * r m') → enc m ≤ enc m' := by
        have hw := Nat.find_spec hne
        obtain ⟨m, hm1, hm2⟩ := hw
        refine ⟨m, hm2, fun m' hm' => ?_⟩
        rw [hm1]
        exact Nat.find_min' hne ⟨m', rfl, hm'⟩
      refine ⟨m, Or.inr ⟨⟨hm.1, hxU⟩, ?_⟩⟩
      refine Set.mem_iInter.2 fun m' => Set.mem_iInter.2 fun hlt hx' => ?_
      exact absurd (hm.2 m' hx') (not_le.2 hlt)

end HRS.Commutator.Whole.XLI
