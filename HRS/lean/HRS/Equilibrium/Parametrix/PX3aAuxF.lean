import HRS.Equilibrium.Parametrix.PX3aAuxE
import HRS.Equilibrium.Parametrix.PX1AuxMul

/-!
# Packet PX3a auxiliaries F: smoothness and derivative formulas for the near and far pieces
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma measurable_e0 : Measurable (e0 d) := by
  by_cases h : d = 2
  · have : e0 d = fun s => -(1 / (4 * Real.pi)) * Real.log s := by funext s; simp [e0, h]
    rw [this]; exact Real.measurable_log.const_mul _
  · have : e0 d = fun s => newtonC d / ((d : ℝ) - 2) * s ^ (((2 : ℝ) - d) / 2) := by
      funext s; simp [e0, h]
    rw [this]; exact (measurable_id.pow_const _).const_mul _

lemma measurable_Efund : Measurable (Efund d) :=
  (measurable_e0 (d := d)).comp ((measurable_norm).pow_const 2)

lemma aesm_smul_continuousOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {V : Set (Euc d)}
    (hV : IsOpen V) {h : Euc d → ℝ} (hh : Measurable h) (hh0 : ∀ u, u ∉ V → h u = 0)
    {f : Euc d → G} (hf : ContinuousOn f V) :
    AEStronglyMeasurable (fun u => h u • f u) (volume : Measure (Euc d)) := by
  have e : (fun u => h u • f u) = fun u => h u • V.indicator f u := by
    funext u
    by_cases hu : u ∈ V
    · simp [indicator_of_mem hu]
    · simp [hh0 u hu]
  rw [e]
  refine hh.aestronglyMeasurable.smul ?_
  exact (aestronglyMeasurable_indicator_iff hV.measurableSet).mpr (hf.aestronglyMeasurable hV.measurableSet)

lemma px3a_add_zero_neg (q : Euc d × Euc d) (u : Euc d) :
    q + ((0 : Euc d), -u) = (q.1, q.2 - u) := by
  ext <;> simp [sub_eq_add_neg]

lemma iter_near_eq {m : ℕ} {g : Euc d × Euc d → ℝ} {V : Set (Euc d × Euc d)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ (m : WithTop ℕ∞) g V) {c : ℝ} (u : Euc d) (hcu : c ≠ 0) {k : ℕ} (hk : k ≤ m)
    {p : Euc d × Euc d} (hp : (p.1, p.2 - u) ∈ V) :
    iteratedFDeriv ℝ k (fun q : Euc d × Euc d => c * g (q.1, q.2 - u)) p =
      c • iteratedFDeriv ℝ k g (p.1, p.2 - u) := by
  have hat : ContDiffAt ℝ (k : WithTop ℕ∞) (fun q : Euc d × Euc d => g (q.1, q.2 - u)) p := by
    have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) g (p.1, p.2 - u) := hg.contDiffAt (hV.mem_nhds hp)
    have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => ((q.1, q.2 - u) : Euc d × Euc d)) := by
      fun_prop
    exact (h1.comp p h2.contDiffAt).of_le (by exact_mod_cast hk)
  have e1 : (fun q : Euc d × Euc d => c * g (q.1, q.2 - u)) =
      c • (fun q : Euc d × Euc d => g (q.1, q.2 - u)) := rfl
  rw [e1, iteratedFDeriv_const_smul_apply hat]
  congr 1
  have e2 : (fun q : Euc d × Euc d => g (q.1, q.2 - u)) = fun q => g (q + ((0 : Euc d), -u)) := by
    funext q; rw [px3a_add_zero_neg]
  rw [e2, iteratedFDeriv_comp_add_right, px3a_add_zero_neg]

lemma ParamHypOn.integrable_deriv {α : Type*} [MeasurableSpace α] {ν : Measure α} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {m : ℕ} {K : E → α → F} (h : ParamHypOn U m K ν) {k : ℕ} (hk : k ≤ m) {x : E}
    (hx : x ∈ U) : Integrable (fun w => iteratedFDeriv ℝ k (fun x' => K x' w) x) ν := by
  obtain ⟨bd, hbd, hb⟩ := h.bound k hk
  refine hbd.mono' (h.meas k hk x hx) ?_
  filter_upwards [hb] with w hw using hw x hx

lemma near_param {m : ℕ} {g : Euc d × Euc d → ℝ} {V : Set (Euc d × Euc d)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ (m : WithTop ℕ∞) g V) {Λn : Euc d → ℝ} (hΛm : Measurable Λn)
    (hΛi : Integrable Λn) {U' : Set (Euc d × Euc d)} (hU' : IsOpen U')
    (hmem : ∀ p ∈ U', ∀ u, Λn u ≠ 0 → (p.1, p.2 - u) ∈ V)
    (hbd : ∀ k ≤ m, ∃ M : ℝ, ∀ p ∈ U', ∀ u, Λn u ≠ 0 →
      ‖iteratedFDeriv ℝ k g (p.1, p.2 - u)‖ ≤ M) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun p => ∫ u, Λn u * g (p.1, p.2 - u)) U' ∧
    (∀ k ≤ m, ∀ p ∈ U', iteratedFDeriv ℝ k (fun p' : Euc d × Euc d => ∫ u, Λn u * g (p'.1, p'.2 - u)) p =
        ∫ u, Λn u • iteratedFDeriv ℝ k g (p.1, p.2 - u)) ∧
    (∀ k ≤ m, ∀ p ∈ U', Integrable (fun u => Λn u • iteratedFDeriv ℝ k g (p.1, p.2 - u))) := by
  have hP : ParamHypOn U' m (fun (p : Euc d × Euc d) (u : Euc d) => Λn u * g (p.1, p.2 - u))
      (volume : Measure (Euc d)) := by
    refine ⟨Eventually.of_forall fun u => ?_, fun k hk p hp => ?_, fun k hk => ?_⟩
    · by_cases hu : Λn u = 0
      · simp only [hu, zero_mul]; exact contDiffOn_const
      · have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => ((q.1, q.2 - u) : Euc d × Euc d)) := by
          fun_prop
        exact contDiffOn_const.mul (hg.comp h2.contDiffOn (fun q hq => hmem q hq u hu))
    · have e : ∀ u, iteratedFDeriv ℝ k (fun q : Euc d × Euc d => Λn u * g (q.1, q.2 - u)) p =
          Λn u • iteratedFDeriv ℝ k g (p.1, p.2 - u) := by
        intro u
        by_cases hu : Λn u = 0
        · simp [hu]
        · exact iter_near_eq hV hg u hu hk (hmem p hp u hu)
      simp_rw [e]
      set W : Set (Euc d) := {u | (p.1, p.2 - u) ∈ V} with hW
      have hWo : IsOpen W := hV.preimage (by fun_prop)
      have hcont : ContinuousOn (fun u => iteratedFDeriv ℝ k g (p.1, p.2 - u)) W := by
        have h1 : ContinuousOn (iteratedFDeriv ℝ k g) V :=
          (contDiffOn_iteratedFDeriv_of_isOpen hV hg (m := 0) (i := k) (by
            simpa using (Nat.cast_le.mpr hk : ((k : ℕ) : WithTop ℕ∞) ≤ m)) |>.continuousOn)
        exact h1.comp (by fun_prop : Continuous fun u : Euc d => ((p.1, p.2 - u) : Euc d × Euc d)).continuousOn
          (fun u hu => hu)
      exact aesm_smul_continuousOn hWo hΛm (fun u hu => by
        by_contra h; exact hu (hmem p hp u h)) hcont
    · obtain ⟨M, hM⟩ := hbd k hk
      refine ⟨fun u => |Λn u| * M, hΛi.abs.mul_const M, Eventually.of_forall fun u p hp => ?_⟩
      by_cases hu : Λn u = 0
      · simp [hu]
      · rw [iter_near_eq hV hg u hu hk (hmem p hp u hu), norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM p hp u hu) (abs_nonneg _)
  obtain ⟨h1, h2⟩ := contDiffOn_integral_param hU' hP
  have e : ∀ k ≤ m, ∀ p ∈ U', ∀ u, iteratedFDeriv ℝ k (fun q : Euc d × Euc d => Λn u * g (q.1, q.2 - u)) p =
      Λn u • iteratedFDeriv ℝ k g (p.1, p.2 - u) := by
    intro k hk p hp u
    by_cases hu : Λn u = 0
    · simp [hu]
    · exact iter_near_eq hV hg u hu hk (hmem p hp u hu)
  refine ⟨h1, fun k hk p hp => ?_, fun k hk p hp => ?_⟩
  · rw [h2 k hk p hp]
    exact integral_congr_ae (Eventually.of_forall fun u => e k hk p hp u)
  · exact (hP.integrable_deriv hk hp).congr (Eventually.of_forall fun u => e k hk p hp u)

lemma norm_iteratedFDeriv_comp_clm_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂) (hL : ‖L‖ ≤ 1) {φ : E₂ → ℝ}
    {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) (x : E₁) :
    ‖iteratedFDeriv ℝ i (φ ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i φ (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hφ x hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _j : Fin i, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hL
  calc _ ≤ ‖iteratedFDeriv ℝ i φ (L x)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

lemma iteratedFDeriv_comp_clm_of_open_n {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {n : WithTop ℕ∞} {f : E → F} (hf : ContDiffOn ℝ n f U) (L : G →L[ℝ] E)
    {x : G} (hx : L x ∈ U) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ i (f ∘ L) x = (iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap fun _ => L := by
  have h1 := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    (hU.preimage L.continuous).uniqueDiffOn hx hi
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ L) i (hU.preimage L.continuous)
    (show x ∈ L ⁻¹' U from hx)
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hU hx
  rw [e1, e2] at h1
  exact h1

lemma iteratedFDeriv_slice_inl_n {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {U : Set (E₁ × E₂)} (hU : IsOpen U) {n : WithTop ℕ∞}
    {G : E₁ × E₂ → ℝ} (hG : ContDiffOn ℝ n G U) {e₁ : E₁} {e₂ : E₂} (hx : (e₁, e₂) ∈ U)
    {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ i (fun x => G (x, e₂)) e₁ =
      (iteratedFDeriv ℝ i G (e₁, e₂)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂) := by
  have hfun : (fun x : E₁ => G (x, e₂)) =
      (fun p : E₁ × E₂ => G (p + (0, e₂))) ∘ (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    funext x; simp
  have hU' : IsOpen {p : E₁ × E₂ | p + (0, e₂) ∈ U} := hU.preimage (by fun_prop)
  have hcd : ContDiffOn ℝ n (fun p : E₁ × E₂ => G (p + (0, e₂))) {p | p + (0, e₂) ∈ U} :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  rw [hfun, iteratedFDeriv_comp_clm_of_open_n hU' hcd (ContinuousLinearMap.inl ℝ E₁ E₂)
    (x := e₁) (by simpa using hx) hi, iteratedFDeriv_comp_add_right]
  simp

lemma far_param (hd : 1 ≤ d) {m : ℕ} {g : Euc d × Euc d → ℝ}
    (hg : ContDiffOn ℝ (m : WithTop ℕ∞) g {p | p.2 ≠ 0})
    {Λf : Euc d → ℝ} (hΛ : ContDiff ℝ (m : WithTop ℕ∞) Λf)
    (hΛb : ∀ i ≤ m, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i Λf y‖ ≤ B)
    (hgb : ∀ j ≤ m, ∃ bd : Euc d → ℝ, Integrable bd ∧ ∀ᵐ w ∂(volume : Measure (Euc d)),
      ∀ X, ‖iteratedFDeriv ℝ j (fun X' => g (X', w)) X‖ ≤ bd w)
    {U' : Set (Euc d × Euc d)} (hU' : IsOpen U') :
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun p => ∫ w, Λf (p.2 - w) * g (p.1, w)) U' ∧
    (∀ k ≤ m, ∀ p ∈ U', iteratedFDeriv ℝ k (fun p' : Euc d × Euc d => ∫ w, Λf (p'.2 - w) * g (p'.1, w)) p =
      ∫ w, iteratedFDeriv ℝ k (fun q : Euc d × Euc d => Λf (q.2 - w) * g (q.1, w)) p) ∧
    (∀ k ≤ m, ∀ p ∈ U', Integrable (fun w => iteratedFDeriv ℝ k
      (fun q : Euc d × Euc d => Λf (q.2 - w) * g (q.1, w)) p)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hO : IsOpen {r : (Euc d × Euc d) × Euc d | r.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hO' : IsOpen {p : Euc d × Euc d | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hae0 : ∀ᵐ w : Euc d, w ≠ 0 := by
    have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
    filter_upwards [this] with w hw using by simpa using hw
  -- joint smoothness away from `w = 0`
  have hΨ : ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun r : (Euc d × Euc d) × Euc d => Λf (r.1.2 - r.2) * g (r.1.1, r.2)) {r | r.2 ≠ 0} := by
    refine ContDiffOn.mul (hΛ.comp (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞)
      (fun r : (Euc d × Euc d) × Euc d => r.1.2 - r.2))).contDiffOn ?_
    exact hg.comp (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞)
      (fun r : (Euc d × Euc d) × Euc d => ((r.1.1, r.2) : Euc d × Euc d))).contDiffOn (fun r hr => hr)
  have hP : ParamHypOn U' m (fun (p : Euc d × Euc d) (w : Euc d) => Λf (p.2 - w) * g (p.1, w))
      (volume : Measure (Euc d)) := by
    refine ⟨?_, fun k hk p hp => ?_, fun k hk => ?_⟩
    · filter_upwards [hae0] with w hw
      have h1 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => Λf (q.2 - w)) :=
        hΛ.comp (by fun_prop)
      have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => g (q.1, w)) := by
        have := hg.comp (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞)
          (fun q : Euc d × Euc d => ((q.1, w) : Euc d × Euc d))).contDiffOn (s := Set.univ) (fun q _ => hw)
        exact contDiffOn_univ.mp this
      exact (h1.mul h2).contDiffOn
    · -- measurability
      have hcont : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k
          (fun q : Euc d × Euc d => Λf (q.2 - w) * g (q.1, w)) p) {w | w ≠ 0} := by
        have e : ∀ w ∈ {w : Euc d | w ≠ 0}, iteratedFDeriv ℝ k
            (fun q : Euc d × Euc d => Λf (q.2 - w) * g (q.1, w)) p =
            (iteratedFDeriv ℝ k (fun r : (Euc d × Euc d) × Euc d => Λf (r.1.2 - r.2) * g (r.1.1, r.2)) (p, w)).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inl ℝ (Euc d × Euc d) (Euc d)) := fun w hw =>
          iteratedFDeriv_slice_inl_n (G := fun r : (Euc d × Euc d) × Euc d => Λf (r.1.2 - r.2) * g (r.1.1, r.2))
            hO hΨ (e₁ := p) (e₂ := w) hw (by exact_mod_cast hk)
        refine ContinuousOn.congr ?_ e
        have h1 : ContinuousOn (iteratedFDeriv ℝ k
            (fun r : (Euc d × Euc d) × Euc d => Λf (r.1.2 - r.2) * g (r.1.1, r.2))) {r | r.2 ≠ 0} :=
          (contDiffOn_iteratedFDeriv_of_isOpen hO hΨ (m := 0) (i := k) (by
            simpa using (Nat.cast_le.mpr hk : ((k : ℕ) : WithTop ℕ∞) ≤ m))).continuousOn
        have h2 : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ k
            (fun r : (Euc d × Euc d) × Euc d => Λf (r.1.2 - r.2) * g (r.1.1, r.2)) (p, w))
            {w | w ≠ 0} :=
          h1.comp (by fun_prop : Continuous fun w : Euc d => ((p, w) : (Euc d × Euc d) × Euc d)).continuousOn
            (fun w hw => hw)
        exact (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ (Euc d × Euc d) (Euc d))).continuous.comp_continuousOn h2
      have := hcont.aestronglyMeasurable (isOpen_ne.measurableSet) (μ := volume)
      rwa [show {w : Euc d | w ≠ 0} = ({0}ᶜ : Set (Euc d)) from rfl, restrict_compl_singleton] at this
    · -- bounds
      choose! B hB using hΛb
      choose! bd hbdi hbdb using hgb
      refine ⟨fun w => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * bd (k - i) w,
        integrable_finset_sum _ (fun i hi => (hbdi (k - i) (by omega)).const_mul _), ?_⟩
      have hall : ∀ᵐ w : Euc d ∂volume, ∀ j, j ≤ m → ∀ X, ‖iteratedFDeriv ℝ j (fun X' => g (X', w)) X‖ ≤ bd j w := by
        rw [ae_all_iff]
        intro j
        by_cases hj : j ≤ m
        · filter_upwards [hbdb j hj] with w hw _ using hw
        · exact Eventually.of_forall fun w h => absurd h hj
      filter_upwards [hall, hae0] with w hw hw0 q _
      have h1 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => Λf (q.2 - w)) :=
        hΛ.comp (by fun_prop)
      have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun q : Euc d × Euc d => g (q.1, w)) := by
        have := hg.comp (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞)
          (fun q : Euc d × Euc d => ((q.1, w) : Euc d × Euc d))).contDiffOn (s := Set.univ) (fun q _ => hw0)
        exact contDiffOn_univ.mp this
      refine (norm_iteratedFDeriv_mul_le h1 h2 q (by exact_mod_cast hk)).trans ?_
      refine Finset.sum_le_sum fun i hi => ?_
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      have hA : ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Λf (q.2 - w)) q‖ ≤ B i := by
        have e : (fun q : Euc d × Euc d => Λf (q.2 - w)) = (fun y : Euc d => Λf (y - w)) ∘ (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) := rfl
        rw [e]
        refine (norm_iteratedFDeriv_comp_clm_le _ (by simpa using ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := Euc d) (F := Euc d))
          (n := (m : WithTop ℕ∞)) (hΛ.comp (by fun_prop)) (by exact_mod_cast (by omega : i ≤ m)) q).trans ?_
        simp only [ContinuousLinearMap.coe_snd']
        have e2 : iteratedFDeriv ℝ i (Λf ∘ fun y => y - w) q.2 = iteratedFDeriv ℝ i Λf (q.2 - w) :=
          iteratedFDeriv_comp_sub i w q.2
        rw [e2]
        exact hB i (by omega) _
      have hG : ‖iteratedFDeriv ℝ (k - i) (fun q : Euc d × Euc d => g (q.1, w)) q‖ ≤ bd (k - i) w := by
        have e : (fun q : Euc d × Euc d => g (q.1, w)) = (fun X' : Euc d => g (X', w)) ∘ (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) := rfl
        rw [e]
        refine (norm_iteratedFDeriv_comp_clm_le _ (by simpa using ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := Euc d) (F := Euc d))
          (n := (m : WithTop ℕ∞)) (by
            have := hg.comp (by fun_prop : ContDiff ℝ (m : WithTop ℕ∞)
              (fun X' : Euc d => ((X', w) : Euc d × Euc d))).contDiffOn (s := Set.univ) (fun q _ => hw0)
            exact contDiffOn_univ.mp this) (by exact_mod_cast (by omega : k - i ≤ m)) q).trans ?_
        exact hw (k - i) (by omega) _
      have hb0 : 0 ≤ B i := (norm_nonneg _).trans (hB i (by omega) 0)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)) hG (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hb0)
  obtain ⟨h1, h2⟩ := contDiffOn_integral_param hU' hP
  exact ⟨h1, fun k hk p hp => h2 k hk p hp, fun k hk p hp => hP.integrable_deriv hk hp⟩

end HRS.Parx

end
