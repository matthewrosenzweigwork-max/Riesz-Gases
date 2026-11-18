import HRS.PDE.TorusFPExistAux4

/-!
# EQ-LZ packet SG-1: `P_t` maps smooth data to smooth data (`eqlz_sg_smooth`), proof

Route: the classical backward solution of `d1_backward_classical` is, at every Sobolev level `m ≥ mStar n`, the function
`toFun (propagatorCoeff ...)`; by the Sobolev embedding (`toFun_isCk_le`) it is `C^k` for `m` large.  By uniqueness
(`d1_P_eq`), `d1_P t φ` is the value at `T - t` of every backward solution, hence `C^k` for all `k`.
This is the argument of `HRS.MC.L2C0.l2c0_isCk_of_adjointData` transferred to `D1BackwardSolution`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE

namespace HRS.MD.EQLZSgSmooth

variable {n : ℕ}

/-- For every `k` there is a backward solution which is `C^k` in space for each `r ∈ [0,t]`. -/
theorem eqlzsg_ck (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {t : ℝ} (ht : 0 < t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) (k : ℕ) :
    ∃ f : ℝ → Torus n → ℝ, D1BackwardSolution κ (d1_gradDrift U) t φ f ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk k (f r) := by
  classical
  set m : ℕ := PDE.mStar n + k with hm
  have hmS : PDE.mStar n ≤ m := Nat.le_add_right _ _
  have hm3 := ClassicalPart.one_le_of_mStar hmS
  have hm1 : 1 ≤ m := by omega
  obtain ⟨R, hR⟩ := d1_exists_regime hn
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨C, Cs, -, -, h⟩ := PDE.adjoint_torus_classical hn 0 hs0 hsd m hmS R 0
    (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ))) (Torus.cbNorm (m + 3) U)
  have hle : ((m : WithTop ℕ∞) + 3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h0 : (((m + 3 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.2 le_top
    push_cast at h0 ⊢
    exact h0
  have hUm : Torus.IsCk ((m : WithTop ℕ∞) + 3) U :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) from hU).of_le hle
  have hconst : Torus.IsCk ((m : WithTop ℕ∞) + 3) (fun _ : Torus n => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift
    exact contDiff_const
  let D := d1_dyn hn κ hκ.le U
  have hA : PDE.AdjointData 0 m R 0 (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ)))
      (Torus.cbNorm (m + 3) U) D 0 t (fun _ _ => (1 : ℝ)) :=
    { hs := rfl
      hM := fun i j => by simp [PDE.MatBound, D, d1_dyn]
      hV := ⟨hUm, le_rfl⟩
      hμ := { prob := fun r _ => ⟨fun _ => zero_le_one, measurable_const, by simp⟩
              smooth := fun r _ => hconst
              bound := fun r _ => le_rfl
              cont := fun ψ _ => by simpa using continuousOn_const }
      hT := ht
      regime := hR D.M rfl D.invβ 0 t _ }
  have hcont : Continuous φ := StaticLimitAux.continuous_of_smooth hφ
  have hmem : MemSobolev (m : ℝ) φ :=
    ⟨hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
      StaticLimitAux.summable_weighted_smooth (m : ℝ) hφ⟩
  obtain ⟨hcl, -⟩ := h D 0 t (fun _ _ => (1 : ℝ)) hA t ⟨ht, le_rfl⟩ φ hcont hmem
  have hgen : ∀ (g : Torus n → ℝ) (x : Torus n),
      backwardGenerator D (fun _ => (1 : ℝ)) g x = d1_gen κ (d1_gradDrift U) g x :=
    fun g x => d1_backwardGenerator_eq hn hκ.le U _ g x
  refine ⟨fun r x => PDE.toFun (PDE.propagatorCoeff D (fun _ _ => (1 : ℝ)) m t (PDE.coeffOf φ) (t - r)) x,
    ⟨hcl.c2, hcl.cont_c2, hcl.terminal, fun x r hr => ?_, ?_⟩, ?_⟩
  · have := hcl.time_deriv x r hr
    rwa [hgen] at this
  · exact hcl.cont_time_deriv.congr fun p => hgen _ _
  · intro r hr
    obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (m : ℝ) φ hmem
    have hre : IsRealCoeff (coeffOf φ) :=
      isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hcont)
    have hreal := ClassicalPart.propagatorCoeff_real hn 0 hs0 hsd m hm1 R 0
      (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ))) (Torus.cbNorm (m + 3) U) D 0 t
      (fun _ _ => (1 : ℝ)) hA t ⟨ht, le_rfl⟩ (coeffOf φ) hcm hre
    obtain ⟨C0, hC0, hspec⟩ := propagatorCoeff_spec hn 0 hs0 hsd m hm1 R 0
      (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ))) (Torus.cbNorm (m + 3) U)
    obtain ⟨-, hw, -⟩ := hspec D 0 t (fun _ _ => (1 : ℝ)) hA t ⟨ht, le_rfl⟩ (coeffOf φ) hcm
    have hτ := ClassicalAux.mem_Icc_sub t hr
    have hnm : (n : ℝ) / 2 + k < m := by
      have h3 : (n : ℝ) / 2 < mStar n := by
        unfold mStar; push_cast
        have := Nat.lt_floor_add_one ((n : ℝ) / 2)
        linarith
      rw [hm]; push_cast; linarith
    obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := n) k (m : ℝ) hnm
    exact (hC2 _ (hw.1 _ hτ) (hreal _ hτ)).1

/-- (SG-1, `eqlz_sg_smooth`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_sg_smooth`. -/
theorem eqlz_sg_smooth_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    Torus.IsSmooth (d1_P hn hκ hU t φ) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have : d1_P hn hκ hU 0 φ = φ := by
      funext x
      unfold d1_P
      simp
    rw [this]; exact hφ
  · have hT : 0 < t + 1 := by linarith
    have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
    have key : ∀ k : ℕ, ContDiff ℝ k (Torus.lift (d1_P hn hκ hU t φ)) := by
      intro k
      obtain ⟨f, hf, hk⟩ := eqlzsg_ck hn hκ hU hT hφ k
      have hfun : d1_P hn hκ hU t φ = f (t + 1 - t) := by
        funext x
        exact d1_P_eq hn hκ hU hT hφ hf htT x
      rw [hfun]
      exact hk _ ⟨by linarith, by linarith⟩
    exact contDiff_infty.2 key

end HRS.MD.EQLZSgSmooth

end
