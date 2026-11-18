import HRS.MC.E213Defs
import HRS.MC.S7PICMain
import HRS.MC.S7PIG1Int
import HRS.MC.S7PIDSAsm
import HRS.Main.A33Aux14

/-!
# Packet E213U2 (Wave 1, W1-B): the covariance tensor on the near window, `winJ_near` and `winJ_add`

Proofs of `HRS.MC.E213Plan.winJ_near` and `HRS.MC.E213Plan.winJ_add` (relocation pattern: the statements are copied
verbatim from `HRS/MC/E213Plan.lean`, the tie file `E213U2Tie.lean` checks equality of the types).

Route for `winJ_near`: the window `[b, a+T]` is transferred to the shifted regime `R_b` (`ρ_b(t) = ρ(b+t)`) on the
horizon `G = Rw + T`: `e213_PID_unif` gives the tensor `J^{(b)}` for the cut-off coefficient `zr'`; the operator
`P : 𝒳_{m,G} → 𝒳_{m,a+T}`, `(P w)(t) = w((t-b)_+)`, pushes it to a tensor `J' = P^{⊗2} J^{(b)}` on the horizon `a+T`
which is a `𝒥`-value of the coefficient `nearCoef b zr` for the original regime (propagator covariance `E213G`);
uniqueness of `J` (`s7_PI_C_J_unique_proof`) identifies `jTensor` with `J'`; finally `winRestr a ∘ P` is a contraction.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U2

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-! ### The operator `P_b : 𝒳_{m,G} →L 𝒳_{m,H}`, `(P_b w)(t) = w((t-b)_+)` -/

/-- the time change `t ↦ max (t-b) 0` from `[0,H]` into `[0,G]` (needs `0 ≤ G`, `H ≤ b + G`). -/
def e213u2_sh (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) (t : Set.Icc (0 : ℝ) H) : Set.Icc (0 : ℝ) G :=
  ⟨max (t.1 - b) 0, le_max_right _ _, max_le (by linarith [t.2.2]) hG⟩

theorem e213u2_continuous_sh (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) :
    Continuous (e213u2_sh b G H hG hHG) := by
  unfold e213u2_sh
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.sub continuous_const).max continuous_const

def e213u2_shLM (m : ℝ) (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) :
    PathSpace d m G →ₗ[ℝ] PathSpace d m H where
  toFun w := (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w).comp
    ⟨e213u2_sh b G H hG hHG, e213u2_continuous_sh b G H hG hHG⟩
  map_add' w w' := e213o_ext (fun t => rfl)
  map_smul' c w := e213o_ext (fun t => rfl)

/-- The operator `P_b : 𝒳_{m,G} →L 𝒳_{m,H}`, `(P_b w)(t) = w((t-b)_+)`, a contraction. -/
def e213u2_shiftOp (m : ℝ) (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) :
    PathSpace d m G →L[ℝ] PathSpace d m H :=
  LinearMap.mkContinuous (e213u2_shLM m b G H hG hHG) 1 (fun w => by
    rw [one_mul]
    refine ContinuousMap.norm_le _ (norm_nonneg _) |>.2 (fun t => ?_)
    exact ContinuousMap.norm_coe_le_norm
      (show C(Set.Icc (0 : ℝ) G, NegSobolev d m) from w) (e213u2_sh b G H hG hHG t))

theorem e213u2_shiftOp_at' (m : ℝ) (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) (w : PathSpace d m G)
    (t : Set.Icc (0 : ℝ) H) :
    (e213u2_shiftOp m b G H hG hHG w).at' t = w.at' (e213u2_sh b G H hG hHG t) := rfl

theorem e213u2_shiftOp_norm_le (m : ℝ) (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) :
    ‖(e213u2_shiftOp (d := d) m b G H hG hHG)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem e213u2_shiftOp_pathAt (m : ℝ) (b G H : ℝ) (hG : 0 ≤ G) (hHG : H ≤ b + G) (w : PathSpace d m G)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) :
    pathAt (e213u2_shiftOp m b G H hG hHG w) t = pathAt w (max (t - b) 0) := by
  have h2 : max (t - b) 0 ∈ Set.Icc (0 : ℝ) G := (e213u2_sh b G H hG hHG ⟨t, ht⟩).2
  unfold pathAt
  rw [dif_pos ht, dif_pos h2]
  rfl

/-! ### `tensorPow'` preserves the projective tensor power -/

section TP

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup B'] [NormedSpace ℝ B']

set_option maxSynthPendingDepth 3 in
theorem e213u2_tensorPow'_mem (j : ℕ) (P : B →L[ℝ] B') {v : TensorDual B j} (hv : v ∈ projTensor B j) :
    tensorPow' j P v ∈ projTensor B' j := by
  have hspan : Submodule.span ℝ (Set.range (elemTensor (B := B) (k := j))) ≤
      (projTensor B' j).comap (tensorPow' j P).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show tensorPow' j P (elemTensor w) ∈ projTensor B' j
    rw [tensorPow'_elem]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)
  have hcl : IsClosed (((projTensor B' j).comap (tensorPow' j P).toLinearMap : Submodule ℝ (TensorDual B j)) :
      Set (TensorDual B j)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage (tensorPow' j P).continuous
  exact Submodule.topologicalClosure_minimal _ hspan hcl hv

end TP

/-! ### Propagator covariance in the form used here -/

open HRS.PDE HRS.PDE.MFSemigroup in
/-- `U_{ρ_b}^{w,t} φ = U_ρ^{b+w,b+t} φ` for smooth `φ`, `0 ≤ w ≤ t ≤ G`, for the regime `R` (uniform `AdjointData`). -/
theorem e213u2_propagator_shift (R : Regime d) {b G : ℝ} (hb : 0 ≤ b) (hG : 0 < G) {w t : ℝ}
    (hw : 0 ≤ w) (hwt : w ≤ t) (htG : t ≤ G) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    propagator R.D (fun τ => R.ρ (b + τ)) w t φ = propagator R.D R.ρ (b + w) (b + t) φ := by
  obtain ⟨Rg₁, MB₁, Λ₁, VB₁, ν₁, h₁⟩ := HRS.MC.E213F.adjointData_uniform R (mStar d)
  obtain ⟨Rg₂, MB₂, Λ₂, VB₂, ν₂, h₂⟩ := HRS.MC.E213F.adjointData_uniform R 1
  have hA := h₁ (b + G) (by linarith) 0 le_rfl
  have hB := h₂ G hG b hb
  have h0 : (fun τ : ℝ => R.ρ (0 + τ)) = R.ρ := by funext τ; simp
  rw [h0] at hA
  have hc : Continuous (φ : Torus d → ℝ) :=
    ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hφ)
  exact HRS.MC.E213G.propagator_shift R.hd hb hA hB le_rfl le_rfl hw hwt htG hc (memSobolev_of_isSmooth hφ _)

/-! ### Transfer of the `𝒥`-value from the shifted regime to the window horizon -/

theorem e213u2_eval_zero {m : ℝ} (φ : Torus d → ℝ) : NegSobolev.eval (0 : NegSobolev d m) φ = 0 := by
  have : ∀ k, NegSobolev.coord (0 : NegSobolev d m) k = 0 := fun k => rfl
  simp [NegSobolev.eval, NegSobolev.fourierCoeff, this]

/-- The cut-off coefficient on the shifted clock: `zr(b+w)` for `b + w ∈ (u,u']`, `w > 0`, and `0` otherwise. -/
def e213u2_cut (b u u' : ℝ) (zr : ℝ → NegSobolev d (rLvl d)) (w : ℝ) : NegSobolev d (rLvl d) :=
  open Classical in if (b + w ∈ Set.Ioc u u' ∧ 0 < w) then zr (b + w) else 0

theorem e213u2_transfer (R : Regime d) (m : ℝ) {b G H : ℝ} (hb : 0 ≤ b) (hG : 0 < G) (hHG : H ≤ b + G)
    (zr : ℝ → NegSobolev d (rLvl d)) (u u' : ℝ) (Jb : TensorDual (PathSpace d m G) 2)
    (hJb : IsJValue R.D (fun t => R.ρ (b + t)) m G
      (fun w => NegSobolev.embed m (e213u2_cut b u u' zr w)) (Set.Ioc (max (u - b) 0) (max (u' - b) 0)) Jb) :
    IsJValue R.D R.ρ m H (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u')
      (tensorPow' 2 (e213u2_shiftOp m b G H hG.le hHG) Jb) := by
  classical
  refine ⟨e213u2_tensorPow'_mem 2 _ hJb.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  set P := e213u2_shiftOp m b G H hG.le hHG with hP
  have hta' : max (ta - b) 0 ∈ Set.Icc (0 : ℝ) G := (e213u2_sh b G H hG.le hHG ⟨ta, hta⟩).2
  have htb' : max (tb - b) 0 ∈ Set.Icc (0 : ℝ) G := (e213u2_sh b G H hG.le hHG ⟨tb, htb⟩).2
  have hl₁' : ∀ w, (l₁.comp P) w = NegSobolev.eval (pathAt w (max (ta - b) 0)) φa := fun w => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hl₁, e213u2_shiftOp_pathAt m b G H hG.le hHG w hta]
  have hl₂' : ∀ w, (l₂.comp P) w = NegSobolev.eval (pathAt w (max (tb - b) 0)) φb := fun w => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hl₂, e213u2_shiftOp_pathAt m b G H hG.le hHG w htb]
  have hM : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]).compContinuousLinearMap
      (fun _ => P) = (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₁.comp P, l₂.comp P] := by
    ext x
    simp [Fin.prod_univ_two]
  rw [tensorPow'_apply, hM]
  rw [hJb.2 _ _ φa φb _ _ hφa hφb hta' htb' hl₁' hl₂']
  congr 1
  have hmA : MeasurableSet (Set.Ioc (max (u - b) 0) (max (u' - b) 0) ∩
      Set.Icc 0 (min (max (ta - b) 0) (max (tb - b) 0))) := measurableSet_Ioc.inter measurableSet_Icc
  have hmS : MeasurableSet (Set.Ioc u u' ∩ Set.Icc 0 (min ta tb)) := measurableSet_Ioc.inter measurableSet_Icc
  rw [← integral_indicator hmA, ← integral_indicator hmS]
  rw [← integral_add_left_eq_self
    (fun x => (Set.Ioc u u' ∩ Set.Icc 0 (min ta tb)).indicator (fun x =>
      (nearCoef b (fun v => NegSobolev.embed m (zr v)) x).eval fun y =>
        inner ℝ (Torus.grad (propagator R.D R.ρ x ta φa) y) (Torus.grad (propagator R.D R.ρ x tb φb) y)) x) b]
  refine integral_congr_ae ?_
  filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with w hw0
  have hw0' : w ≠ 0 := by simpa using hw0
  by_cases hA : w ∈ Set.Ioc (max (u - b) 0) (max (u' - b) 0) ∩
      Set.Icc 0 (min (max (ta - b) 0) (max (tb - b) 0))
  · have hA0 := hA
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hA
    have hwpos : 0 < w := lt_of_le_of_lt (le_max_right _ _) h1
    have hub : u - b < w := lt_of_le_of_lt (le_max_left _ _) h1
    have hu'b : w ≤ u' - b := by
      rcases le_total (u' - b) 0 with h | h
      · rw [max_eq_right h] at h2; linarith
      · rw [max_eq_left h] at h2; exact h2
    have hta1 : w ≤ max (ta - b) 0 := h4.trans (min_le_left _ _)
    have htb1 : w ≤ max (tb - b) 0 := h4.trans (min_le_right _ _)
    have htaeq : max (ta - b) 0 = ta - b := max_eq_left (by
      by_contra hcon; rw [max_eq_right (not_le.1 hcon).le] at hta1; linarith)
    have htbeq : max (tb - b) 0 = tb - b := max_eq_left (by
      by_contra hcon; rw [max_eq_right (not_le.1 hcon).le] at htb1; linarith)
    have hS : b + w ∈ Set.Ioc u u' ∩ Set.Icc 0 (min ta tb) := by
      refine ⟨⟨by linarith, by linarith⟩, by linarith, ?_⟩
      rw [htaeq] at hta1; rw [htbeq] at htb1
      exact le_min (by linarith) (by linarith)
    rw [Set.indicator_of_mem hA0, Set.indicator_of_mem hS]
    have e1 : e213u2_cut b u u' zr w = zr (b + w) := by
      unfold e213u2_cut; rw [if_pos ⟨⟨by linarith, by linarith⟩, hwpos⟩]
    have e2 : nearCoef b (fun v => NegSobolev.embed m (zr v)) (b + w) = NegSobolev.embed m (zr (b + w)) := by
      unfold nearCoef; rw [if_pos (by linarith)]
    have htaG : max (ta - b) 0 ≤ G := hta'.2
    have htbG : max (tb - b) 0 ≤ G := htb'.2
    have pa := e213u2_propagator_shift R hb hG hwpos.le hta1 htaG hφa
    have pb := e213u2_propagator_shift R hb hG hwpos.le htb1 htbG hφb
    rw [htaeq] at pa; rw [htbeq] at pb
    simp only [add_sub_cancel] at pa pb
    beta_reduce
    rw [htaeq, htbeq, e1, e2, pa, pb]
  · rw [Set.indicator_of_notMem hA]
    by_cases hS : b + w ∈ Set.Ioc u u' ∩ Set.Icc 0 (min ta tb)
    · rw [Set.indicator_of_mem hS]
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hS
      have hneg : w < 0 := by
        by_contra hcon
        have hwpos : 0 < w := lt_of_le_of_ne (not_lt.1 hcon) (Ne.symm hw0')
        apply hA
        have hta1 : w ≤ max (ta - b) 0 := le_max_of_le_left (by have := h4.trans (min_le_left _ _); linarith)
        have htb1 : w ≤ max (tb - b) 0 := le_max_of_le_left (by have := h4.trans (min_le_right _ _); linarith)
        exact ⟨⟨max_lt (by linarith) hwpos, le_max_of_le_left (by linarith)⟩, hwpos.le, le_min hta1 htb1⟩
      beta_reduce
      have e2 : nearCoef b (fun v => NegSobolev.embed m (zr v)) (b + w) = 0 := by
        unfold nearCoef; rw [if_neg (by linarith)]
      rw [e2, e213u2_eval_zero]
    · rw [Set.indicator_of_notMem hS]


/-! ### `winJ_near` -/

theorem e213u2_cut_measurable (b u u' : ℝ) (hb : 0 ≤ b) (zr : ℝ → NegSobolev d (rLvl d))
    (hzm : Measurable (nearCoef 0 zr)) : Measurable (e213u2_cut b u u' zr) := by
  classical
  have e : e213u2_cut b u u' zr = fun w =>
      if (b + w ∈ Set.Ioc u u' ∧ 0 < w) then nearCoef 0 zr (b + w) else 0 := by
    funext w
    unfold e213u2_cut
    by_cases h : (b + w ∈ Set.Ioc u u' ∧ 0 < w)
    · rw [if_pos h, if_pos h]; unfold nearCoef; rw [if_pos (by linarith [h.2])]
    · rw [if_neg h, if_neg h]
  rw [e]
  refine Measurable.ite ?_ (hzm.comp (measurable_const_add b)) measurable_const
  exact (measurableSet_Ioc.preimage (measurable_const_add b)).inter measurableSet_Ioi

variable {S : PreparedData d} {β₀ m : ℝ}

theorem winJ_near_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (Rw : ℝ) (hRw : 0 < Rw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (b : ℝ), 0 ≤ b → b ≤ a → a - b ≤ Rw →
      ∀ (zr : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 zr) → ∀ M : ℝ,
      (∀ v ∈ Set.Icc b (a + T), ‖zr v‖ ≤ M) →
      ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        (∃ J, IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
            (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') J) ∧
        ‖winJ (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u')‖ ≤
          C * M * (u' - u) := by
  classical
  obtain ⟨C0, hC0⟩ := HRS.MC.E213M.e213_PID_unif (regime S β₀ hE) (rLvl d) rfl m hE.m_gt (Rw + T)
    (by linarith)
  refine ⟨|C0| + 1, by positivity, ?_⟩
  intro a ha b hb hba hab zr hzm M hM u u' hu huu hu'
  have hG : 0 < Rw + T := by linarith
  have hHG : a + T ≤ b + (Rw + T) := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b ⟨le_rfl, by linarith⟩)
  have hbd : ∀ w ∈ Set.Icc (0 : ℝ) (Rw + T), ‖e213u2_cut b u u' zr w‖ ≤ M := by
    intro w hw
    unfold e213u2_cut
    by_cases h : (b + w ∈ Set.Ioc u u' ∧ 0 < w)
    · rw [if_pos h]; exact hM _ ⟨by linarith [h.2], by linarith [h.1.2]⟩
    · rw [if_neg h]; simpa using hM0
  have ha1 : 0 ≤ max (u - b) 0 := le_max_right _ _
  have ha12 : max (u - b) 0 ≤ max (u' - b) 0 := max_le_max (by linarith) le_rfl
  have ha2 : max (u' - b) 0 ≤ Rw + T := max_le (by linarith) hG.le
  obtain ⟨Jb, hJb, hJn⟩ := hC0 b hb (e213u2_cut b u u' zr) (e213u2_cut_measurable b u u' hb zr hzm) M hbd
    (max (u - b) 0) (max (u' - b) 0) ha1 ha12 ha2
  have hJ' := e213u2_transfer (regime S β₀ hE) m hb hG hHG zr u u' Jb hJb
  refine ⟨⟨_, hJ'⟩, ?_⟩
  set R := regime S β₀ hE with hR
  set P := e213u2_shiftOp (d := d) m b (Rw + T) (a + T) hG.le hHG with hP
  have hjt : jTensor R.D R.ρ m (a + T) (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u') =
      tensorPow' 2 P Jb := by
    have hex : ∃ J, IsJValue R.D R.ρ m (a + T) (nearCoef b (fun v => NegSobolev.embed m (zr v)))
        (Set.Ioc u u') J := ⟨_, hJ'⟩
    unfold jTensor
    rw [dif_pos hex]
    exact HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m (a + T) _ _ _ _ hex.choose_spec hJ'
  unfold winJ
  rw [hjt, ← tensorPow'_comp]
  have hQP : ‖(winRestr (d := d) (m := m) (T := T) a ha).comp P‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖(winRestr (d := d) (m := m) (T := T) a ha)‖ * ‖P‖ ≤ 1 * 1 :=
          mul_le_mul (winRestr_norm_le a ha) (e213u2_shiftOp_norm_le m b _ _ _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hdiff : max (u' - b) 0 - max (u - b) 0 ≤ u' - u := by
    rcases le_total (u - b) 0 with h1 | h1 <;> rcases le_total (u' - b) 0 with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2]; linarith
    · rw [max_eq_right h1, max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_right h2]; linarith
    · rw [max_eq_left h1, max_eq_left h2]; linarith
  calc ‖tensorPow' 2 ((winRestr (d := d) (m := m) (T := T) a ha).comp P) Jb‖
      ≤ ‖(winRestr (d := d) (m := m) (T := T) a ha).comp P‖ ^ 2 * ‖Jb‖ := tensorPow'_norm_le _ _ _
    _ ≤ 1 * ‖Jb‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hQP) (ContinuousLinearMap.opNorm_nonneg _)
    _ = ‖Jb‖ := one_mul _
    _ ≤ C0 * M * (max (u' - b) 0 - max (u - b) 0) := hJn
    _ ≤ (|C0| + 1) * M * (max (u' - b) 0 - max (u - b) 0) := by
        have : 0 ≤ M * (max (u' - b) 0 - max (u - b) 0) := mul_nonneg hM0 (by linarith)
        nlinarith [le_abs_self C0]
    _ ≤ (|C0| + 1) * M * (u' - u) :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg (by positivity) hM0)

/-! ### `winJ_add` -/

theorem e213u2_fc_add {M : ℝ} (F G : NegSobolev d M) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F + G) k = NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff NegSobolev.coord
  rw [← mul_add]; rfl

theorem e213u2_ext_fc {M : ℝ} {F G : NegSobolev d M}
    (h : ∀ k, NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k) : F = G := by
  refine lp.ext (funext fun k => ?_)
  have h1 := h k
  unfold NegSobolev.fourierCoeff at h1
  have hp : 0 < Lattice.jp k.1 ^ M := Real.rpow_pos_of_pos (Torus.jp_pos k.1) M
  exact mul_left_cancel₀ hp.ne' h1

theorem e213u2_rLvl_le {m : ℝ} (hm : 3 * (d : ℝ) + 8 < m) : rLvl d ≤ m := by
  unfold rLvl; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem e213u2_fc_embed {m : ℝ} (hrm : rLvl d ≤ m) (F : NegSobolev d (rLvl d)) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m F) k = NegSobolev.fourierCoeff F k :=
  HRS.MC.Sec7.S7PIDS.S7PIDS_fc_embed hrm F k

theorem e213u2_embed_add {m : ℝ} (hrm : rLvl d ≤ m) (z z' : NegSobolev d (rLvl d)) :
    NegSobolev.embed m (z + z') = NegSobolev.embed m z + NegSobolev.embed m z' := by
  refine e213u2_ext_fc fun k => ?_
  rw [e213u2_fc_add, e213u2_fc_embed hrm, e213u2_fc_embed hrm, e213u2_fc_embed hrm, e213u2_fc_add]

/-- Pointwise additivity of the integrand of `IsJValue` in the coefficient (via the mode expansion). -/
theorem e213u2_eval_add (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb)
    (u ta tb : ℝ) (hu : 0 ≤ u) (hua : u ≤ ta) (hub : u ≤ tb) (hta : ta ≤ T) (htb : tb ≤ T)
    (z z' : NegSobolev d (rLvl d)) :
    NegSobolev.eval (NegSobolev.embed m (z + z'))
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x)) =
      NegSobolev.eval (NegSobolev.embed m z)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x)) +
      NegSobolev.eval (NegSobolev.embed m z')
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x)) := by
  have hrm : rLvl d ≤ m := e213u2_rLvl_le hm
  have hz : ∀ w : NegSobolev d (rLvl d), Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(rLvl d)) *
      NegSobolev.fourierCoeff (NegSobolev.embed m w : NegSobolev d m) k) 2 := fun w => by
    refine (Torus.memℓp_two_iff _).2 ?_
    refine (HRS.MC.Sec7.PIE.pie_coeff_summable w).congr fun k => ?_
    rw [e213u2_fc_embed hrm w k]
  have H : ∀ w : NegSobolev d (rLvl d), HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
        NegSobolev.eval (NegSobolev.embed m w : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) *
          NegSobolev.eval (Vprop R.D R.ρ m ta u (HRS.MC.Sec7.PID.modeVec m p.1)) φa *
          NegSobolev.eval (Vprop R.D R.ρ m tb u (HRS.MC.Sec7.PID.modeVec m p.2)) φb)
      (NegSobolev.eval (NegSobolev.embed m w : NegSobolev d m)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x))) := fun w =>
    HRS.MC.Sec7.S7PIDE.s7_PID_expansion_proof R (rLvl d) rfl m hm T hT φa φb hφa hφb u ta tb hu hua hub hta htb
      _ (hz w)
  obtain ⟨Cg, -, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) m (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hadd : ∀ p : NonzeroLattice d × NonzeroLattice d,
      NegSobolev.eval (NegSobolev.embed m (z + z') : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) =
        NegSobolev.eval (NegSobolev.embed m z : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) +
        NegSobolev.eval (NegSobolev.embed m z' : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) := fun p => by
    rw [e213u2_embed_add hrm]
    exact HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_of_memSobolev (hCg p.1 p.2).1)
  have hf : (fun p : NonzeroLattice d × NonzeroLattice d =>
        NegSobolev.eval (NegSobolev.embed m (z + z') : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) *
          NegSobolev.eval (Vprop R.D R.ρ m ta u (HRS.MC.Sec7.PID.modeVec m p.1)) φa *
          NegSobolev.eval (Vprop R.D R.ρ m tb u (HRS.MC.Sec7.PID.modeVec m p.2)) φb) =
      fun p => (NegSobolev.eval (NegSobolev.embed m z : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) *
          NegSobolev.eval (Vprop R.D R.ρ m ta u (HRS.MC.Sec7.PID.modeVec m p.1)) φa *
          NegSobolev.eval (Vprop R.D R.ρ m tb u (HRS.MC.Sec7.PID.modeVec m p.2)) φb) +
        (NegSobolev.eval (NegSobolev.embed m z' : NegSobolev d m) (HRS.MC.Sec7.PID.gradProd p.1 p.2) *
          NegSobolev.eval (Vprop R.D R.ρ m ta u (HRS.MC.Sec7.PID.modeVec m p.1)) φa *
          NegSobolev.eval (Vprop R.D R.ρ m tb u (HRS.MC.Sec7.PID.modeVec m p.2)) φb) := by
    funext p
    rw [hadd p]; ring
  have h3 := H (z + z')
  rw [hf] at h3
  exact h3.unique ((H z).add (H z'))

theorem e213u2_isJValue_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z z' : ℝ → NegSobolev d m)
    (I : Set ℝ) (hI : MeasurableSet I) (h : ∀ v, 0 ≤ v → z v = z' v) (J : TensorDual (PathSpace d m T) 2)
    (hJ : IsJValue D ρ m T z I J) : IsJValue D ρ m T z' I J := by
  refine ⟨hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine setIntegral_congr_fun (hI.inter measurableSet_Icc) fun u hu => ?_
  beta_reduce
  rw [h u hu.2.1]

theorem e213u2_jTensor_eq (R : Regime d) (m T : ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (J : TensorDual (PathSpace d m T) 2) (h : IsJValue R.D R.ρ m T z I J) : jTensor R.D R.ρ m T z I = J := by
  have hex : ∃ J, IsJValue R.D R.ρ m T z I J := ⟨_, h⟩
  unfold jTensor
  rw [dif_pos hex]
  exact HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m T _ _ _ _ hex.choose_spec h

theorem e213u2_isJValue_add (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (z₁ z₂ : ℝ → NegSobolev d (rLvl d)) (h₁ : Measurable (nearCoef 0 z₁)) (h₂ : Measurable (nearCoef 0 z₂))
    (M₁ M₂ : ℝ) (hM₁ : ∀ v ∈ Set.Icc (0 : ℝ) T, ‖z₁ v‖ ≤ M₁) (hM₂ : ∀ v ∈ Set.Icc (0 : ℝ) T, ‖z₂ v‖ ≤ M₂)
    (I : Set ℝ) (hIm : MeasurableSet I) (hI : I ⊆ Set.Ioc 0 T)
    (J₁ J₂ : TensorDual (PathSpace d m T) 2)
    (hJ₁ : IsJValue R.D R.ρ m T (fun v => NegSobolev.embed m (z₁ v)) I J₁)
    (hJ₂ : IsJValue R.D R.ρ m T (fun v => NegSobolev.embed m (z₂ v)) I J₂) :
    IsJValue R.D R.ρ m T (fun v => NegSobolev.embed m (z₁ v + z₂ v)) I (J₁ + J₂) := by
  refine ⟨add_mem hJ₁.1 hJ₂.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [ContinuousLinearMap.add_apply, hJ₁.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂,
    hJ₂.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  have hnb : ∀ (z : ℝ → NegSobolev d (rLvl d)) (M : ℝ), (∀ v ∈ Set.Icc (0 : ℝ) T, ‖z v‖ ≤ M) →
      ∀ v ∈ Set.Icc (0 : ℝ) T, ‖nearCoef 0 z v‖ ≤ M := fun z M hM v hv => by
    unfold nearCoef; rw [if_pos hv.1]; exact hM v hv
  have hint : ∀ (z : ℝ → NegSobolev d (rLvl d)) (hz : Measurable (nearCoef 0 z)) (M : ℝ),
      (∀ v ∈ Set.Icc (0 : ℝ) T, ‖z v‖ ≤ M) →
      IntegrableOn (fun u => NegSobolev.eval (NegSobolev.embed m (z u) : NegSobolev d m)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x))) (I ∩ Set.Icc 0 (min ta tb)) := by
    intro z hz M hM
    have h0 := HRS.MC.Sec7.S7PIG1.S7PIG1_integrand_integrable R (rLvl d) rfl m hm T hT (nearCoef 0 z) hz M
      (hnb z M hM) ta tb hta htb φa φb hφa hφb
    refine (h0.mono_set (Set.inter_subset_inter_left _ hI)).congr_fun (fun u hu => ?_)
      (hIm.inter measurableSet_Icc)
    beta_reduce
    have : nearCoef 0 z u = z u := by unfold nearCoef; rw [if_pos hu.2.1]
    rw [this]; rfl
  have i₁ := hint z₁ h₁ M₁ hM₁
  have i₂ := hint z₂ h₂ M₂ hM₂
  rw [← mul_add, ← integral_add i₁ i₂]
  congr 1
  refine setIntegral_congr_fun (hIm.inter measurableSet_Icc) fun u hu => ?_
  beta_reduce
  have hu0 : 0 ≤ u := hu.2.1
  exact (e213u2_eval_add R m hm T hT φa φb hφa hφb u ta tb hu0 (hu.2.2.trans (min_le_left _ _))
    (hu.2.2.trans (min_le_right _ _)) hta.2 htb.2 (z₁ u) (z₂ u)).symm

theorem winJ_add_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (z₁ z₂ : ℝ → NegSobolev d (rLvl d)) (h₁ : Measurable (nearCoef 0 z₁)) (h₂ : Measurable (nearCoef 0 z₂)) (M₁ M₂ : ℝ)
    (hM₁ : ∀ v ∈ Set.Icc 0 (a + T), ‖z₁ v‖ ≤ M₁) (hM₂ : ∀ v ∈ Set.Icc 0 (a + T), ‖z₂ v‖ ≤ M₂)
    (u u' : ℝ) (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' ≤ a + T) :
    winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (z₁ v + z₂ v)) (Set.Ioc u u') =
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (z₁ v)) (Set.Ioc u u') +
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (z₂ v)) (Set.Ioc u u') := by
  set R := regime S β₀ hE with hR
  have hH : 0 < a + T := by linarith
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIDS.s7_PI_D_J_exists_assembly_proof R (rLvl d) rfl m hE.m_gt (a + T) hH
  have hex : ∀ (z : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 z) → ∀ M : ℝ,
      (∀ v ∈ Set.Icc (0 : ℝ) (a + T), ‖z v‖ ≤ M) →
      ∃ J, IsJValue R.D R.ρ m (a + T) (fun v => NegSobolev.embed m (z v)) (Set.Ioc u u') J := by
    intro z hz M hM
    have hnb : ∀ v ∈ Set.Icc (0 : ℝ) (a + T), ‖nearCoef 0 z v‖ ≤ M := fun v hv => by
      unfold nearCoef; rw [if_pos hv.1]; exact hM v hv
    obtain ⟨J, hJ, -⟩ := hC (nearCoef 0 z) hz M hnb u u' hu huu hu'
    refine ⟨J, e213u2_isJValue_congr R.D R.ρ m (a + T) _ _ _ measurableSet_Ioc (fun v hv => ?_) J hJ⟩
    show NegSobolev.embed m (nearCoef 0 z v) = NegSobolev.embed m (z v)
    unfold nearCoef; rw [if_pos hv]
  obtain ⟨J₁, hJ₁⟩ := hex z₁ h₁ M₁ hM₁
  obtain ⟨J₂, hJ₂⟩ := hex z₂ h₂ M₂ hM₂
  have hI : Set.Ioc u u' ⊆ Set.Ioc 0 (a + T) := fun x hx => ⟨lt_of_le_of_lt hu hx.1, hx.2.trans hu'⟩
  have hJ₃ := e213u2_isJValue_add R m hE.m_gt (a + T) hH z₁ z₂ h₁ h₂ M₁ M₂ hM₁ hM₂ _ measurableSet_Ioc hI
    J₁ J₂ hJ₁ hJ₂
  unfold winJ
  rw [e213u2_jTensor_eq R m (a + T) _ _ _ hJ₃, e213u2_jTensor_eq R m (a + T) _ _ _ hJ₁,
    e213u2_jTensor_eq R m (a + T) _ _ _ hJ₂, map_add]

end HRS.MC.E213U2

end
