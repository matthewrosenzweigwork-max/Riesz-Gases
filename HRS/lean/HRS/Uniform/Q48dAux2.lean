import HRS.Uniform.Q48dAux1

/-!
# Q48d, part 2: concatenation of stochastic convolutions and stopping (infrastructure for Lemma 3.31)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Concatenation of two partitions meeting at the common point. -/
lemma exists_concat {a : ℝ} {n m : ℕ} (p : Fin (n + 1) → ℝ) (q : Fin (m + 1) → ℝ)
    (hp : p (Fin.last n) = a) (hq : q 0 = a) (hpm : Monotone p) (hqm : Monotone q) :
    ∃ r : Fin (n + m + 1) → ℝ, r 0 = p 0 ∧ r (Fin.last _) = q (Fin.last m) ∧ Monotone r ∧
      (∀ i : Fin n, r (Fin.castAdd m i).castSucc = p i.castSucc ∧ r (Fin.castAdd m i).succ = p i.succ) ∧
      (∀ j : Fin m, r (Fin.natAdd n j).castSucc = q j.castSucc ∧ r (Fin.natAdd n j).succ = q j.succ) := by
  classical
  let r : Fin (n + m + 1) → ℝ := fun k =>
    if h : k.val ≤ n then p ⟨k.val, by omega⟩ else q ⟨k.val - n, by omega⟩
  have hpa : ∀ x, p x ≤ a := fun x => hp ▸ hpm (Fin.le_last x)
  have haq : ∀ y, a ≤ q y := fun y => hq ▸ hqm (Fin.zero_le y)
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [r]
    split_ifs with h
    · rfl
    · exfalso; apply h; simp
  · simp only [r]
    split_ifs with h
    · have hm0 : m = 0 := by simp at h; omega
      subst hm0
      have e : (⟨(Fin.last (n + 0)).val, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
      rw [e, hp]
      have : (Fin.last 0 : Fin 1) = 0 := rfl
      rw [this, hq]
    · congr 1
      exact Fin.ext (by simp)
  · intro i j hij
    have hij' : i.val ≤ j.val := hij
    simp only [r]
    by_cases hj : j.val ≤ n
    · have hi : i.val ≤ n := hij'.trans hj
      rw [dif_pos hi, dif_pos hj]
      exact hpm hij'
    · by_cases hi : i.val ≤ n
      · rw [dif_pos hi, dif_neg hj]
        exact (hpa _).trans (haq _)
      · rw [dif_neg hi, dif_neg hj]
        exact hqm (by show i.val - n ≤ j.val - n; omega)
  · intro i
    have h1 : (Fin.castAdd m i).castSucc.val ≤ n := by simp <;> omega
    have h2 : (Fin.castAdd m i).succ.val ≤ n := by simp <;> omega
    simp only [r, dif_pos h1, dif_pos h2]
    exact ⟨rfl, rfl⟩
  · intro j
    refine ⟨?_, ?_⟩
    · simp only [r]
      by_cases hj : j.val = 0
      · have h1 : (Fin.natAdd n j).castSucc.val ≤ n := by simp <;> omega
        rw [dif_pos h1]
        have e1 : (⟨(Fin.natAdd n j).castSucc.val, by omega⟩ : Fin (n + 1)) = Fin.last n :=
          Fin.ext (by simp <;> omega)
        have e2 : j.castSucc = 0 := Fin.ext (by simp [hj])
        simp only [e1, hp, e2, hq]
      · have h1 : ¬ (Fin.natAdd n j).castSucc.val ≤ n := by simp <;> omega
        rw [dif_neg h1]
        congr 1
        exact Fin.ext (by simp)
    · simp only [r]
      have h1 : ¬ (Fin.natAdd n j).succ.val ≤ n := by simp
      rw [dif_neg h1]
      congr 1
      exact Fin.ext (by simp <;> omega)

/-- The concatenation identity for stochastic convolutions. -/
lemma sc_concat {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (hD : ∀ τ ∈ Icc 0 t, AEStronglyMeasurable (D τ) P)
    (hcoc : ∀ r, 0 ≤ r → r ≤ a → (V t a).comp (V a r) = V t r) {Y Za W : Ω → E}
    (hY : AEStronglyMeasurable Y P) (hZ : AEStronglyMeasurable Za P) (hW : AEStronglyMeasurable W P)
    (hSY : SC P V D 0 t Y) (hSZ : SC P V D 0 a Za) (hSW : SC P V D a t W) :
    Y =ᵐ[P] fun ω => V t a (Za ω) + W ω := by
  have hcand : AEStronglyMeasurable (fun ω => V t a (Za ω) + W ω) P :=
    ((V t a).continuous.comp_aestronglyMeasurable hZ).add hW
  have hz : eLpNorm (fun ω => Y ω - (V t a (Za ω) + W ω)) 2 P = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) bot_le
    set c : ℝ := ‖V t a‖ with hc
    have hc0 : 0 ≤ c := norm_nonneg _
    have hη3 : (0 : ℝ) < (η : ℝ) / (3 * (c + 1)) := by positivity
    set η' : ℝ := (η : ℝ) / (3 * (c + 1)) with hη'
    obtain ⟨δ1, hδ1, h1⟩ := hSY η' hη3
    obtain ⟨δ2, hδ2, h2⟩ := hSZ η' hη3
    obtain ⟨δ3, hδ3, h3⟩ := hSW η' hη3
    obtain ⟨n, p, hp0, hpl, hpm, hpmesh⟩ := exists_part ha (lt_min hδ1 (lt_min hδ2 hδ3))
    obtain ⟨m, q, hq0, hql, hqm, hqmesh⟩ := exists_part hat (lt_min hδ1 (lt_min hδ2 hδ3))
    obtain ⟨r, hr0, hrl, hrm, hrp, hrq⟩ := exists_concat (a := a) p q hpl hq0 hpm hqm
    have hmesh : ∀ i : Fin (n + m), r i.succ - r i.castSucc < min δ1 (min δ2 δ3) := by
      intro i
      refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
      · rw [(hrp i0).1, (hrp i0).2]; exact hpmesh i0
      · rw [(hrq j).1, (hrq j).2]; exact hqmesh j
    have e1 := h1 (n + m) r (hr0.trans hp0) (hrl.trans hql) hrm
      fun i => (hmesh i).trans_le (min_le_left _ _)
    have e2 := h2 n p hp0 hpl hpm fun i =>
      (hpmesh i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have e3 := h3 m q hq0 hql hqm fun i =>
      (hqmesh i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    -- the Riemann sum splits
    have hsplit : ∀ ω, riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω =
        V t a (riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω) +
          riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω := by
      intro ω
      simp_rw [riemannSum_id]
      rw [Fin.sum_univ_add, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hrp i).1, (hrp i).2]
        have hmem : p i.castSucc ∈ Icc 0 a := by
          have := mem_Icc_of_part hp0 hpl hpm i.castSucc
          exact this
        rw [← hcoc _ hmem.1 hmem.2]
        rfl
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [(hrq j).1, (hrq j).2]
    have hRp := aesm_riemannSum V (fun τ hτ => hD τ ⟨hτ.1, hτ.2.trans hat⟩) hp0 hpl hpm
    have hRq := aesm_riemannSum V (fun τ hτ => hD τ ⟨ha.trans hτ.1, hτ.2⟩) hq0 hql hqm
    have hRr := aesm_riemannSum V hD (hr0.trans hp0) (hrl.trans hql) hrm
    have hdecomp : (fun ω => Y ω - (V t a (Za ω) + W ω)) =
        (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) -
        (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) -
        (fun ω => W ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) := by
      funext ω
      simp only [Pi.sub_apply, hsplit ω, map_sub]
      abel
    have hm1 : AEStronglyMeasurable
        (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) P := hY.sub hRr
    have hm2 : AEStronglyMeasurable
        (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) P :=
      (V t a).continuous.comp_aestronglyMeasurable (hZ.sub hRp)
    have hm3 : AEStronglyMeasurable
        (fun ω => W ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) P := hW.sub hRq
    have e2' : eLpNorm (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) 2 P ≤
        ENNReal.ofReal c * ENNReal.ofReal η' := by
      calc _ ≤ ENNReal.ofReal c * eLpNorm (fun ω => Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω) 2 P :=
            eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm2
              (Eventually.of_forall fun ω => (V t a).le_opNorm _) 2
        _ ≤ _ := by gcongr
    rw [hdecomp]
    calc eLpNorm _ 2 P ≤ eLpNorm ((fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) -
            (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω))) 2 P +
          eLpNorm (fun ω => W ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) 2 P :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ (eLpNorm (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P +
            eLpNorm (fun ω => V t a (Za ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a p ω)) 2 P) +
          eLpNorm (fun ω => W ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t q ω) 2 P := by
          gcongr; exact eLpNorm_sub_le (by norm_num)
      _ ≤ (ENNReal.ofReal η' + ENNReal.ofReal c * ENNReal.ofReal η') + ENNReal.ofReal η' := by
          exact add_le_add (add_le_add e1.le e2') e3.le
      _ = ENNReal.ofReal ((2 + c) * η') := by
          rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ 0 + (η : ℝ≥0∞) := by
          rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hη', ← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hc0 (NNReal.coe_nonneg η), NNReal.coe_nonneg η]
  have := (eLpNorm_eq_zero_iff (by norm_num)).1 hz
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω

/-- Stopping does not change the Riemann sums before the stopping time. -/
lemma isStochConv_stop_iff {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t S : ℝ}
    (htS : t ≤ S) {Y : Ω → E} :
    IsStochConv P V (ContinuousLinearMap.id ℝ E) (fun τ ω => D (min τ S) ω) a t Y ↔
      IsStochConv P V (ContinuousLinearMap.id ℝ E) D a t Y := by
  have hrs : ∀ {n : ℕ} {r : Fin (n + 1) → ℝ}, r (Fin.last n) = t → Monotone r → ∀ ω,
      riemannSum V (ContinuousLinearMap.id ℝ E) (fun τ ω => D (min τ S) ω) t r ω =
        riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω := by
    intro n r hl hm ω
    simp_rw [riemannSum_id]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hle : ∀ k : Fin (n + 1), r k ≤ t := fun k => hl ▸ hm (Fin.le_last k)
    have h1 : r i.succ ≤ S := (hle _).trans htS
    have h2 : r i.castSucc ≤ S := (hle _).trans htS
    simp only [min_eq_left h1, min_eq_left h2]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, fun n r h0 hl hm hmesh => ?_⟩
    have := hδ' n r h0 hl hm hmesh
    simpa [hrs hl hm] using this
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, fun n r h0 hl hm hmesh => ?_⟩
    have := hδ' n r h0 hl hm hmesh
    simpa [hrs hl hm] using this

end HRS.Uniform.Q48d
