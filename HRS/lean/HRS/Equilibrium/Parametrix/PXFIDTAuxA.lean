import HRS.Equilibrium.PairPoissonFull
import HRS.Equilibrium.Parametrix.PX1AuxPartial

/-!
# Packet PX-FID-T, file A: tangential derivatives of conormal kernels

`tanDeriv e F = d/dt F(x + te, y + te)` is, in the chart `(X, z)`, the derivative `∂_X · e`; hence it
costs one conormal derivative and no singular order:

* `lift2_tanDeriv`: `lift2 (tanDeriv e ψ) = dirD (e, e) (lift2 ψ)` (periodicity of `lift2 ψ`),
* `toChart_tanDeriv`: `toChart (tanDeriv e F) = dirD (e, 0) (toChart F)` on the chart domain,
* `conormal_tanDeriv`: `ConormalL σ b (m+1) B F → ConormalL σ b m (B ‖e‖) (tanDeriv e F)`,
* `conormal_tanIter`: the iterated version, with the product of the norms.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx.PXFIDT

variable {d : ℕ}

theorem lift2_tanDeriv (e : Euc d) (ψ : Torus d → Torus d → ℝ) (p : Euc d × Euc d) :
    lift2 (tanDeriv e ψ) p = fderiv ℝ (lift2 ψ) p (e, e) := by
  obtain ⟨n1, hn1⟩ := Torus.rep_mk p.1
  obtain ⟨n2, hn2⟩ := Torus.rep_mk p.2
  have hper : ∀ q : Euc d × Euc d,
      lift2 ψ (q + (Lattice.toEuc n1, Lattice.toEuc n2)) = lift2 ψ q := by
    intro q
    simp only [lift2, Prod.fst_add, Prod.snd_add]
    rw [mk_add', mk_toEuc', add_zero, mk_add', mk_toEuc', add_zero]
  have h1 : fderiv ℝ (lift2 ψ) (p + (Lattice.toEuc n1, Lattice.toEuc n2)) = fderiv ℝ (lift2 ψ) p := by
    have e' : (fun q => lift2 ψ (q + (Lattice.toEuc n1, Lattice.toEuc n2))) = lift2 ψ := funext hper
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := lift2 ψ) (x := p) (Lattice.toEuc n1, Lattice.toEuc n2)
    rw [e'] at this
    exact this.symm
  show tanDeriv e ψ (Torus.mk p.1) (Torus.mk p.2) = _
  unfold tanDeriv
  rw [hn1, hn2]
  have : ((p.1 + Lattice.toEuc n1, p.2 + Lattice.toEuc n2) : Euc d × Euc d) =
      p + (Lattice.toEuc n1, Lattice.toEuc n2) := rfl
  rw [this, h1]

theorem lift2_tanDeriv_eq (e : Euc d) (ψ : Torus d → Torus d → ℝ) :
    lift2 (tanDeriv e ψ) = dirD (e, e) (lift2 ψ) :=
  funext (lift2_tanDeriv e ψ)

theorem toChart_tanDeriv {F : Torus d → Torus d → ℝ} {m : ℕ}
    (hF : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d)) (hm : 1 ≤ m) (e : Euc d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (tanDeriv e F) q = fderiv ℝ (toChart F) q (e, 0) := by
  have hTq : chartT d q ∈ offDiag d := hq
  have hd : DifferentiableAt ℝ (lift2 F) (chartT d q) :=
    (hF.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))).differentiableAt
      (isOpen_offDiag.mem_nhds hTq)
  have h1 : toChart (tanDeriv e F) q = lift2 (tanDeriv e F) (chartT d q) := by
    rw [toChart_eq]; rfl
  rw [h1, lift2_tanDeriv]
  have h2 : HasFDerivAt (toChart F) ((fderiv ℝ (lift2 F) (chartT d q)).comp (chartT d)) q := by
    rw [toChart_eq]
    exact hd.hasFDerivAt.comp q (chartT d).hasFDerivAt
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  rw [chartT_apply]
  refine Prod.ext ?_ ?_ <;> simp

theorem tb_tan {G : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W : ℝ}
    (hG : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q) (e : Euc d)
    (h1 : TB G q (a + 1) c W) : TB (dirD (e, (0 : Euc d)) G) q a c (W * ‖e‖) := by
  intro u v
  rw [iteratedFDeriv_dirD hG, ← iteratedFDeriv_cons_eq_snoc hG]
  have := h1 (Fin.cons e u) v
  rw [pat_cons_left, iteratedFDeriv_cast, prod_norm_cons] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem norm_prod_self (e : Euc d) : ‖((e, e) : Euc d × Euc d)‖ = ‖e‖ := by
  rw [Prod.norm_def, max_self]

theorem conormal_tanDeriv {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b (m + 1) B F) (e : Euc d) :
    ConormalL σ b m (B * ‖e‖) (tanDeriv e F) where
  smooth := by
    rw [lift2_tanDeriv_eq]
    exact contDiffOn_dirD isOpen_offDiag hF.smooth (e, e)
  near := by
    intro a c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    set r := ‖z‖ with hr
    set L := 1 + |Real.log r| with hL
    have hr0 : 0 < r := norm_pos_iff.mpr hz
    have hr1 : r ≤ 1 := by unfold r0 at hzr; linarith
    have hL1 : 1 ≤ L := by linarith [abs_nonneg (Real.log r)]
    have hB : 0 ≤ B := by
      have h00 := hF.near 0 0 (Nat.zero_le _) X z hz hzr
      have h0 : 0 ≤ ‖mixedDeriv 0 0 (toChart F) X z‖ := ContinuousMultilinearMap.opNorm_nonneg _
      have hw : 0 < 1 + r ^ (-(σ + ((0 : ℕ) : ℝ))) * L ^ (b 0) := by positivity
      by_contra hneg
      rw [not_le] at hneg
      have := mul_neg_of_neg_of_pos hneg hw
      linarith
    have hs : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 (tanDeriv e F)) (offDiag d) := by
      rw [lift2_tanDeriv_eq]
      exact contDiffOn_dirD isOpen_offDiag hF.smooth (e, e)
    have hG'd : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart (tanDeriv e F)) (Uc d) :=
      (toChart_contDiffOn hs).of_le (by exact_mod_cast hac)
    have hGd : ∀ k ≤ m + 1, ContDiffOn ℝ (k : WithTop ℕ∞) (toChart F) (Uc d) := fun k hk =>
      (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hk)
    have hGat : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) (toChart F) (X, z) :=
      (hGd (a + c + 1) (by omega)).contDiffAt (isOpen_Uc.mem_nhds hq)
    have hev : toChart (tanDeriv e F) =ᶠ[𝓝 (X, z)] dirD (e, (0 : Euc d)) (toChart F) := by
      filter_upwards [isOpen_Uc.mem_nhds hq] with q' hq'
      exact toChart_tanDeriv hF.smooth (by omega) e hq'
    set W₁ : ℝ := B * (1 + r ^ (-(σ + (c : ℝ))) * L ^ (b c)) with hW₁
    have hW₁0 : 0 ≤ W₁ := by simp only [hW₁]; positivity
    have T1 : TB (toChart F) (X, z) (a + 1) c W₁ :=
      tb_of_norm_le isOpen_Uc (hGd (a + 1 + c) (by omega)) hq
        (hF.near (a + 1) c (by omega) X z hz hzr)
    have T := tb_congr hev (tb_tan hGat e T1)
    have hnorm := norm_le_of_tb isOpen_Uc hG'd hq (by positivity) T
    refine hnorm.trans (le_of_eq ?_)
    simp only [hW₁]
    ring
  far := by
    intro k hk p hp hr
    have hB : 0 ≤ B := (norm_nonneg _).trans (hF.far 0 (Nat.zero_le _) p hp hr)
    have hat : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (lift2 F) p :=
      (hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le
        (by exact_mod_cast (by omega : k + 1 ≤ m + 1))
    have hev : lift2 (tanDeriv e F) = dirD (e, e) (lift2 F) := lift2_tanDeriv_eq e F
    rw [hev]
    refine (norm_iteratedFDeriv_dirD_le hat _).trans ?_
    rw [norm_prod_self]
    have := hF.far (k + 1) (by omega) p hp hr
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem conormal_tanIter {σ : ℝ} {b : ℕ → ℕ} :
    ∀ (es : List (Euc d)) {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ},
      ConormalL σ b (m + es.length) B F →
      ConormalL σ b m (B * (es.map fun e => ‖e‖).prod) (tanIter es F)
  | [], m, B, F, h => by simpa [tanIter] using h
  | e :: es, m, B, F, h => by
    have h1 : ConormalL σ b (m + 1) (B * (es.map fun e => ‖e‖).prod) (tanIter es F) :=
      conormal_tanIter es (m := m + 1) (by
        have : m + 1 + es.length = m + (e :: es).length := by simp; omega
        rw [this]; exact h)
    have h2 := conormal_tanDeriv h1 e
    have e3 : B * (es.map fun e => ‖e‖).prod * ‖e‖ = B * ((e :: es).map fun e => ‖e‖).prod := by
      simp [mul_comm, mul_assoc]
    rw [e3] at h2
    exact h2

end HRS.Parx.PXFIDT

end
