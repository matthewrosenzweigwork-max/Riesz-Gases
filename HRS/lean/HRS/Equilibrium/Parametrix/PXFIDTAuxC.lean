import HRS.Equilibrium.Parametrix.PXFIDTAuxB

/-!
# Packet PX-FID-T, file C: tangential derivatives of the smooth part, `PsiSize` of `tanIter`

* `contDiff_tanL`, `norm_iteratedFDeriv_tanL_le`: `tanL es` lowers the differentiability by `|es|`
  and multiplies the norms of the jets by `∏ ‖e_i‖`;
* `isCk2_tanIter`, `cbNorm2_tanIter_le`: the same for `IsCk2` kernels and `cbNorm2`;
* `PsiSize.congr_offDiag`;
* `fidt_psiSize_tan`: `PsiSize` of `tanIter es (Φ + I)` from the bounds of `tanIter es Φ` (`Px5Bnds`
  of `ψ^loc`) and a `C^{2+|es|}` kernel `I`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx.PXFIDT

variable {d : ℕ} {s : ℝ}

theorem contDiff_tanL (es : List (Euc d)) (j : ℕ) {G : Euc d × Euc d → ℝ}
    (h : ContDiff ℝ ((es.length + j : ℕ) : WithTop ℕ∞) G) :
    ContDiff ℝ (j : WithTop ℕ∞) (tanL es G) := by
  rw [← contDiffOn_univ] at h ⊢
  exact contDiffOn_tanL isOpen_univ es j h

theorem norm_iteratedFDeriv_tanL_le :
    ∀ (es : List (Euc d)) (i : ℕ) {G : Euc d × Euc d → ℝ} (n : ℕ), ContDiff ℝ (n : WithTop ℕ∞) G →
      i + es.length ≤ n → ∀ p,
      ‖iteratedFDeriv ℝ i (tanL es G) p‖ ≤
        (es.map fun e => ‖e‖).prod * ‖iteratedFDeriv ℝ (i + es.length) G p‖
  | [], i, G, n, hG, hi, p => by simp [tanL]
  | e :: es, i, G, n, hG, hi, p => by
    have hi' : i + 1 + es.length ≤ n := by simp at hi; omega
    have hA : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (tanL es G) :=
      contDiff_tanL es (i + 1) (hG.of_le (by exact_mod_cast (by omega : es.length + (i + 1) ≤ n)))
    have h1 := norm_iteratedFDeriv_dirD_le (hA.contDiffAt (x := p)) (e, e)
    rw [norm_prod_self] at h1
    have h2 := norm_iteratedFDeriv_tanL_le es (i + 1) n hG hi' p
    have e1 : i + (e :: es).length = i + 1 + es.length := by simp; omega
    rw [e1]
    show ‖iteratedFDeriv ℝ i (dirD (e, e) (tanL es G)) p‖ ≤ _
    have hp : 0 ≤ (es.map fun e => ‖e‖).prod :=
      List.prod_nonneg (by intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
    calc ‖iteratedFDeriv ℝ i (dirD (e, e) (tanL es G)) p‖
        ≤ ‖iteratedFDeriv ℝ (i + 1) (tanL es G) p‖ * ‖e‖ := h1
      _ ≤ ((es.map fun e => ‖e‖).prod * ‖iteratedFDeriv ℝ (i + 1 + es.length) G p‖) * ‖e‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := by simp only [List.map_cons, List.prod_cons]; ring

theorem isCk2_tanIter (es : List (Euc d)) {j : ℕ} {I : Torus d → Torus d → ℝ}
    (hI : PDE.IsCk2 (j + es.length) I) : PDE.IsCk2 j (tanIter es I) := by
  unfold PDE.IsCk2 at hI ⊢
  have : PDE.lift2 (tanIter es I) = lift2 (tanIter es I) := rfl
  rw [this, lift2_tanIter]
  exact contDiff_tanL es j (by
    have e : es.length + j = j + es.length := by omega
    rw [e]; exact hI)

theorem cbNorm2_tanIter_le (es : List (Euc d)) {I : Torus d → Torus d → ℝ}
    (hI : PDE.IsCk2 (2 + es.length) I) :
    PDE.cbNorm2 2 (tanIter es I) ≤
      3 * (es.map fun e => ‖e‖).prod * PDE.cbNorm2 (2 + es.length) I := by
  have hp : 0 ≤ (es.map fun e => ‖e‖).prod :=
    List.prod_nonneg (by intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
  have hcb : 0 ≤ PDE.cbNorm2 (2 + es.length) I := PDE.MFPair.cbNorm2_nonneg _ _
  have hterm : ∀ i : ℕ, i ≤ 2 →
      (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (PDE.lift2 (tanIter es I)) p‖) ≤
      (es.map fun e => ‖e‖).prod * PDE.cbNorm2 (2 + es.length) I := by
    intro i hi
    refine ciSup_le fun p => ?_
    show ‖iteratedFDeriv ℝ i (lift2 (tanIter es I)) p‖ ≤ _
    rw [lift2_tanIter]
    have hG : ContDiff ℝ ((2 + es.length : ℕ) : WithTop ℕ∞) (lift2 I) := hI
    refine (norm_iteratedFDeriv_tanL_le es i (2 + es.length) hG (by omega) p).trans ?_
    exact mul_le_mul_of_nonneg_left
      (PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hI (i := i + es.length) (by omega) p) hp
  have h3 : PDE.cbNorm2 2 (tanIter es I) =
      (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ 0 (PDE.lift2 (tanIter es I)) p‖) +
      (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ 1 (PDE.lift2 (tanIter es I)) p‖) +
      ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ 2 (PDE.lift2 (tanIter es I)) p‖ := by
    unfold PDE.cbNorm2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [h3]
  have b0 := hterm 0 (by norm_num)
  have b1 := hterm 1 (by norm_num)
  have b2 := hterm 2 le_rfl
  nlinarith [b0, b1, b2]

theorem PsiSize.congr_offDiag {K : ℝ} {ψ ψ' : Torus d → Torus d → ℝ}
    (hψ : ∀ x y, x ≠ y → ψ x y = ψ' x y) (h : PsiSize s K ψ') : PsiSize s K ψ := by
  have hE : Set.EqOn (lift2 ψ) (lift2 ψ') (offDiag d) := fun p hp => hψ _ _ hp
  have hN : ∀ p ∈ offDiag d, lift2 ψ =ᶠ[𝓝 p] lift2 ψ' := fun p hp =>
    Filter.eventuallyEq_of_mem (isOpen_offDiag.mem_nhds hp) hE
  refine ⟨h.smooth.congr hE, fun x y hxy => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hψ x y hxy]; exact h.size x y hxy
  · rw [(hN p hp).fderiv_eq]; exact h.grad p hp
  · rw [((hN p hp).iteratedFDeriv ℝ 2).eq_of_nhds]; exact h.hess p hp

/-- The tangential `PsiSize` of a sum `Φ + I`: `tanIter es Φ` has `PsiSize` with constant `K₁`,
`I` is `C^{2+|es|}` with `3 ∏‖e‖ ‖I‖_{C^{2+|es|}} ≤ M`, and `Φ + I` is `C^∞` off the diagonal. -/
theorem fidt_psiSize_tan (es : List (Euc d)) {K₁ M : ℝ} {Φ I : Torus d → Torus d → ℝ}
    (hΦ : PsiSize s K₁ (tanIter es Φ))
    (hΦsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 Φ) (offDiag d))
    (hI : PDE.IsCk2 (2 + es.length) I)
    (hM : 3 * (es.map fun e => ‖e‖).prod * PDE.cbNorm2 (2 + es.length) I ≤ M)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 (fun x y => Φ x y + I x y)) (offDiag d)) :
    PsiSize s (K₁ + M) (tanIter es (fun x y => Φ x y + I x y)) := by
  have hI' : ContDiff ℝ ((2 + es.length : ℕ) : WithTop ℕ∞) (lift2 I) := hI
  have hIsm : ContDiffOn ℝ (es.length : WithTop ℕ∞) (lift2 I) (offDiag d) :=
    (hI'.contDiffOn).of_le (by exact_mod_cast (by omega : es.length ≤ 2 + es.length))
  have hΦsm' : ContDiffOn ℝ (es.length : WithTop ℕ∞) (lift2 Φ) (offDiag d) :=
    hΦsm.of_le (by exact_mod_cast le_top)
  have hEq : Set.EqOn (lift2 (tanIter es (fun x y => Φ x y + I x y)))
      (lift2 (fun x y => tanIter es Φ x y + tanIter es I x y)) (offDiag d) := by
    intro p hp
    have h := tanL_add_eqOn isOpen_offDiag es hΦsm' hIsm hp
    show lift2 (tanIter es (fun x y => Φ x y + I x y)) p =
      lift2 (tanIter es Φ) p + lift2 (tanIter es I) p
    rw [lift2_tanIter, lift2_tanIter, lift2_tanIter]
    exact h
  have hsm2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (lift2 (fun x y => tanIter es Φ x y + tanIter es I x y)) (offDiag d) := by
    have : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 (tanIter es (fun x y => Φ x y + I x y)))
        (offDiag d) := by
      rw [lift2_tanIter]; exact contDiffOn_top_tanL isOpen_offDiag es hsm
    exact this.congr (fun p hp => (hEq hp).symm)
  have hIck : PDE.IsCk2 2 (tanIter es I) := isCk2_tanIter es (by simpa [add_comm] using hI)
  have hMt : PDE.cbNorm2 2 (tanIter es I) ≤ M := (cbNorm2_tanIter_le es hI).trans hM
  have h1 := PsiSize.add_ck2 hΦ hIck hMt hsm2
  exact PsiSize.congr_offDiag (fun x y hxy => by
    have := tanIter_add_offDiag es hΦsm' hIsm x y hxy
    exact this) h1

end HRS.Parx.PXFIDT

end
