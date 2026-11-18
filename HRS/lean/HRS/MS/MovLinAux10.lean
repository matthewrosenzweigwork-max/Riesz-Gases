import HRS.MS.MovLinAux9

/-!
# MOV-LIN, part 1: density of the Schwartz core in `L²_0` and uniqueness of the semigroup

Namespace `HRS.MS.MovLin`, helpers `movlin_`/`mov2d_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Dense

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-- The Schwartz core is dense in `L²_0`. -/
lemma mov2d_dense_core (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    Dense {v : MovL2Zero ρ | ∃ φ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x} := by
  intro v
  rw [Metric.mem_closure_iff]
  intro ε hε
  set y : OscSpace d 0 := (mov2d_Phi d).symm (v : Lp ℝ 2 (volume : Measure (Euc d))) with hy
  set e1 : OscSpace d 0 := OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ) with he1
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := Metric.mem_closure_iff.1 (mov2d_e_dense (d := d) 0 y) (ε / 3) hδ
  set g : OscSpace d 0 := mov2d_e d 0 c with hg
  obtain ⟨φc, hφc⟩ := mov2d_hs_schwartz (d := d) c
  have hv0 : inner ℝ e1 y = 0 := by
    have := (mov2d_mem_zero_iff (ρ := ρ)).1 v.2
    rw [mov2d_sqrtLp H ψ0 hψ0] at this
    rw [hy, ← LinearIsometryEquiv.inner_map_map (mov2d_Phi d), LinearIsometryEquiv.apply_symm_apply]
    exact this
  set a : ℝ := inner ℝ e1 g with ha
  set k : ℝ := a / ‖e1‖ ^ 2 with hk
  set z' : OscSpace d 0 := g - k • e1 with hz'
  have hz0 : inner ℝ e1 z' = 0 := by
    by_cases he : e1 = 0
    · simp [he]
    · have : ‖e1‖ ^ 2 ≠ 0 := by positivity
      rw [hz', inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hk, ha]
      field_simp
      ring
  have hmem : mov2d_Phi d z' ∈ MovL2Zero ρ := by
    rw [mov2d_mem_zero_iff, mov2d_sqrtLp H ψ0 hψ0, LinearIsometryEquiv.inner_map_map]
    exact hz0
  have hz : z' = OscSpace.ofFun 0 (⇑(φc - k • ψ0) : Euc d → ℝ) := by
    have h1 : (⇑(φc - k • ψ0) : Euc d → ℝ) = fun x => (⇑φc : Euc d → ℝ) x - k * (⇑ψ0 : Euc d → ℝ) x := by
      funext x; simp
    have hφo : OscSpace.ofFun 0 (⇑φc : Euc d → ℝ) = g := by
      rw [hφc]; rfl
    rw [h1, mov2d_ofFun_sub (memOsc_schwartz 0 φc)
      (HRS.MS.MovC1.movc1_osc_smul 0 k (memOsc_schwartz 0 ψ0)).1,
      mov2d_ofFun_smul k (memOsc_schwartz 0 ψ0), hφo, hz']
  refine ⟨⟨mov2d_Phi d z', hmem⟩, ⟨φc - k • ψ0, ?_⟩, ?_⟩
  · have hL : MemLp (fun x => (φc - k • ψ0) x) 2 (volume : Measure (Euc d)) := (φc - k • ψ0).memLp 2
    have : mov2d_Phi d z' = hL.toLp _ := by
      rw [hz]; exact mov2d_Phi_ofFun hL
    show (⇑(mov2d_Phi d z') : Euc d → ℝ) =ᵐ[volume] _
    rw [this]
    exact hL.coeFn_toLp
  · -- distance
    have hPy : mov2d_Phi d y = (v : Lp ℝ 2 (volume : Measure (Euc d))) := by
      rw [hy]; exact LinearIsometryEquiv.apply_symm_apply _ _
    have hnorm : dist v ⟨mov2d_Phi d z', hmem⟩ = ‖y - z'‖ := by
      have e1' : dist v ⟨mov2d_Phi d z', hmem⟩ = ‖(v : Lp ℝ 2 (volume : Measure (Euc d))) - mov2d_Phi d z'‖ := by
        rw [dist_eq_norm]; rfl
      rw [e1', ← hPy, ← (mov2d_Phi d).map_sub, (mov2d_Phi d).norm_map]
    rw [hnorm]
    have hyg : ‖y - g‖ < ε / 3 := by rw [← dist_eq_norm]; exact hc
    have hkn : ‖k • e1‖ ≤ ‖y - g‖ := by
      by_cases he : e1 = 0
      · simp [hk, he]
      · have hpos : 0 < ‖e1‖ := norm_pos_iff.2 he
        have h1 : a = inner ℝ e1 (g - y) := by
          rw [inner_sub_right, hv0, ha]; ring
        have h2 : |a| ≤ ‖e1‖ * ‖y - g‖ := by
          rw [h1]
          refine (abs_real_inner_le_norm _ _).trans ?_
          rw [norm_sub_rev]
        rw [norm_smul, hk, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖e1‖ ^ 2)]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [h2, hpos]
    calc ‖y - z'‖ = ‖(y - g) + k • e1‖ := by rw [hz']; congr 1; abel
      _ ≤ ‖y - g‖ + ‖k • e1‖ := norm_add_le _ _
      _ < ε := by linarith

/-- Uniqueness on all of `L²_0`: any `MovIsSemigroup` family coincides with the constructed one. -/
lemma movlin_uniq (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {T' : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)} (hT' : MovIsSemigroup d s β ρ T') {t : ℝ} (ht : 0 ≤ t) :
    T' t = mov2d_T H ψ0 hψ0 t := by
  have hd := mov2d_dense_core H ψ0 hψ0
  ext1 v
  have key : Set.EqOn (fun v => T' t v) (fun v => mov2d_T H ψ0 hψ0 t v)
      {v : MovL2Zero ρ | ∃ φ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x} := by
    rintro v ⟨φ, hφ⟩
    exact mov2d_uniq_core H ψ0 hψ0 hT' φ v hφ ht
  exact congrFun (Continuous.ext_on hd (T' t).continuous (mov2d_T H ψ0 hψ0 t).continuous key) v

end Dense

end HRS.MS.MovLin
