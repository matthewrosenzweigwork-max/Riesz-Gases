import HRS.MS.UniqC2b

/-!
# Packet C2, part 3: joint continuity of the mean-field drift `b^σ = meanFieldDriftW D (ρ (t-σ))`

Main results:

* `c2_drift_cont`: under the hypotheses `H` of `HRS.MS.UniqC1.c1_isAdvectingDrift`
  (`d ≥ 1`, `0 ≤ s < d`, `D.s = s`, `MatBound`, `VHypRd (m+3)`, `CoeffHypRd s m Λ T ρ`, `t ∈ [0,T]`),
  `(σ,x) ↦ meanFieldDriftW D (ρ (t-σ)) x` is continuous on `[0,t] × ℝ^d`.
* `c2_isAdvectingDrift`: the full `IsAdvectingDrift` (no continuity hypothesis).

Route: `CoeffHypRd.regular` gives, uniformly in `r ∈ [0,T]`, `|ρ^r(y)| ≤ A (1+|y|)^{-(d+1)}` and
`‖Dρ^r‖ ≤ A`; `CoeffHypRd.cont` is weak continuity.  Testing against an approximate identity gives
pointwise continuity of `r ↦ ρ^r(y)` (`c2_pointwise`), the Lipschitz bound upgrades this to joint
continuity (`c2_joint`), and dominated convergence gives continuity of the convolution (`c2_rgT_cont`).
The term `-∇V` is continuous; `m ≥ 0` is enough (only `C^1` bounds of `ρ^r` are used).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC2
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen HRS.MS.UniqC1

variable {d : ℕ}

/-- Continuity of a map into `ℝ^d` from the continuity of its coordinates. -/
lemma c2_vec_contOn {X : Type*} [TopologicalSpace X] {f : X → Euc d} {S : Set X}
    (h : ∀ i, ContinuousOn (fun p => f p i) S) : ContinuousOn f S := by
  have : f = fun p => WithLp.toLp 2 (fun i => f p i) := by funext p; simp
  rw [this]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp_continuousOn (continuousOn_pi.2 h)

/-- **Joint continuity of the convolution** `(r,x) ↦ (∇g * ρ^r)(x)` on `[0,T] × ℝ^d`. -/
theorem c2_force_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ : ℝ)
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hcoef : CoeffHypRd s m Λ T ρ) :
    ContinuousOn (fun p : ℝ × Euc d => convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  set A : ℝ := c1A d m Λ with hAdef
  have hA : 0 ≤ A := by unfold c1A at hAdef; rw [hAdef]; positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) T, RgDecay (m + 3) (fun _ => A) (ρ r) := by
    intro r hr
    have hcb := hcoef.regular.1 r hr
    have hcb0 : 0 ≤ HRS.cbNorm (m + 3) (ρ r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    exact rg_rho_decay hd (r := m + 3) (Λ := max Λ 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ 0])
  have hparts := fun r hr => rg_decay_parts (n := m + 3) (by omega) (a := fun _ => A) (fun _ => hA)
    (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (ρ r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖ρ r y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) :=
    fun r hr => (hparts r hr).2.1
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  have hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T) := fun ψ hψ hk =>
    hcoef.cont ψ hψ (by
      obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hk
      exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x⟩)
  have hjoint := c2_joint hA hweak hdiff h1'
  apply c2_vec_contOn
  intro i
  have hcomp := c2_rgT_cont hd hs0 hsd (rgKerComp_ok (d := d) hs0 i) hA hA hdiff h0 h1' hjoint
  refine hcomp.congr fun p hp => ?_
  exact rg_force_comp hd hs0 hsd (hdiff p.1 hp.1) hA hA (h0 p.1 hp.1) (h1' p.1 hp.1) p.2 i

/-- **Joint continuity of the drift** `(σ,x) ↦ meanFieldDriftW D (ρ (t-σ)) x` on `[0,t] × ℝ^d`. -/
theorem c2_drift_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContinuousOn (fun p : ℝ × Euc d => meanFieldDriftW D (ρ (t - p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
  have hF := c2_force_cont hd hs0 hsd m Λ hcoef
  have hc : ContinuousOn (fun p : ℝ × Euc d => (t - p.1, p.2)) (Set.Icc 0 t ×ˢ Set.univ) :=
    (continuousOn_const.sub continuousOn_fst).prodMk continuousOn_snd
  have hmaps : Set.MapsTo (fun p : ℝ × Euc d => (t - p.1, p.2)) (Set.Icc 0 t ×ˢ Set.univ)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := fun p hp =>
    ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1, ht.2]⟩, Set.mem_univ _⟩
  have h1 := hF.comp hc hmaps
  have hmat : Continuous (Torus.matVec D.M) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)
  have hgrad : Continuous (fun x : Euc d => gradient D.V x) := by
    have : Continuous (fderiv ℝ D.V) := hV.1.continuous_fderiv (by simp)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp this
  unfold meanFieldDriftW
  rw [hDs]
  exact (hmat.comp_continuousOn h1).sub (hgrad.comp_continuousOn continuousOn_snd)

/-- **`IsAdvectingDrift` for the mean-field drift** with no continuity hypothesis: the joint continuity
is supplied by `c2_drift_cont`. -/
theorem c2_isAdvectingDrift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsAdvectingDrift m (c1Cb d s m MB Λ ΛV G₀) t (fun σ => meanFieldDriftW D (ρ (t - σ))) :=
  c1_isAdvectingDrift hd hs0 hsd m MB Λ ΛV G₀ hDs hMB hV hcoef ht
    (c2_drift_cont hd hs0 hsd m MB Λ ΛV G₀ hDs hMB hV hcoef ht)

end HRS.MS.UniqC2
