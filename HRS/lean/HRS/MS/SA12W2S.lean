import HRS.MS.SA12W2R

/-!
# S.A.12 C5 (SA12W2 worker), part S: closure of `C^m`-norm continuity of torus families

`sa12w2_CC t w` (part R) is closed under sums, products, constants, directional derivatives and the coordinates of the
cancellation convolution `convGradConv (periodicRieszGrad d s)`.  This is the algebra needed to show that the
nonlocal term `-𝒢_L[F]` of the rescaled solution is jointly smooth.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

theorem sa12w2_ck_of_smooth {f : Torus d → ℝ} (h : ContDiff ℝ ∞ (Torus.lift f)) (m : ℕ) :
    Torus.IsCk (m : WithTop ℕ∞) f :=
  h.of_le (by exact_mod_cast le_top)

theorem sa12w2_isCk_sub {f g : Torus d → ℝ} {k : WithTop ℕ∞} (hf : Torus.IsCk k f) (hg : Torus.IsCk k g) :
    Torus.IsCk k (fun x => f x - g x) := by
  unfold Torus.IsCk at *
  exact hf.sub hg

theorem sa12w2_cbNorm_zero (m : ℕ) : Torus.cbNorm m (fun _ : Torus d => (0 : ℝ)) = 0 := by
  unfold Torus.cbNorm
  refine Finset.sum_eq_zero fun j _ => ?_
  have : Torus.lift (fun _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
  rw [this]
  simp [iteratedFDeriv_zero_fun]

theorem sa12w2_CC_of_bound {t : ℝ} {w : ℝ → Torus d → ℝ}
    (hs : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Torus.lift (w τ)))
    (hb : ∀ τ₀ ∈ Icc (0 : ℝ) t, ∀ m : ℕ, ∃ n : ℝ → ℝ, Tendsto n (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0) ∧
      ∀ τ ∈ Icc (0 : ℝ) t, Torus.cbNorm m (fun x => w τ x - w τ₀ x) ≤ n τ) : sa12w2_CC t w := by
  refine ⟨hs, fun τ₀ hτ₀ m => ?_⟩
  obtain ⟨n, hn, hle⟩ := hb τ₀ hτ₀ m
  exact squeeze_zero' (eventually_nhdsWithin_of_forall fun τ _ => HRS.KernelGrad.cbNorm_nonneg' _ m)
    (eventually_nhdsWithin_of_forall hle) hn

theorem sa12w2_CC_const (t c : ℝ) : sa12w2_CC t (fun (_ : ℝ) (_ : Torus d) => c) := by
  refine ⟨fun τ _ => contDiff_const, fun τ₀ _ m => ?_⟩
  simp only [sub_self, sa12w2_cbNorm_zero]
  exact tendsto_const_nhds

theorem sa12w2_CC_add {t : ℝ} {a b : ℝ → Torus d → ℝ} (ha : sa12w2_CC t a) (hb : sa12w2_CC t b) :
    sa12w2_CC t (fun τ x => a τ x + b τ x) := by
  refine sa12w2_CC_of_bound (fun τ hτ => (ha.1 τ hτ).add (hb.1 τ hτ)) fun τ₀ hτ₀ m => ?_
  refine ⟨fun τ => Torus.cbNorm m (fun x => a τ x - a τ₀ x) + Torus.cbNorm m (fun x => b τ x - b τ₀ x),
    ?_, ?_⟩
  · simpa using (ha.2 τ₀ hτ₀ m).add (hb.2 τ₀ hτ₀ m)
  · intro τ hτ
    have h1 : Torus.IsCk (m : WithTop ℕ∞) (fun x => a τ x - a τ₀ x) :=
      sa12w2_isCk_sub (sa12w2_ck_of_smooth (ha.1 τ hτ) m) (sa12w2_ck_of_smooth (ha.1 τ₀ hτ₀) m)
    have h2 : Torus.IsCk (m : WithTop ℕ∞) (fun x => b τ x - b τ₀ x) :=
      sa12w2_isCk_sub (sa12w2_ck_of_smooth (hb.1 τ hτ) m) (sa12w2_ck_of_smooth (hb.1 τ₀ hτ₀) m)
    have e : (fun x => (a τ x + b τ x) - (a τ₀ x + b τ₀ x)) =
        (fun x => a τ x - a τ₀ x) + (fun x => b τ x - b τ₀ x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [e]
    exact Torus.cbNorm_add_le m _ _ h1 h2

theorem sa12w2_CC_mul {t : ℝ} {a b : ℝ → Torus d → ℝ} (ha : sa12w2_CC t a) (hb : sa12w2_CC t b) :
    sa12w2_CC t (fun τ x => a τ x * b τ x) := by
  refine sa12w2_CC_of_bound (fun τ hτ => (ha.1 τ hτ).mul (hb.1 τ hτ)) fun τ₀ hτ₀ m => ?_
  obtain ⟨C, hC0, hC⟩ := HRS.PDE.MFVelocity.exists_cbNorm_mul_le (d := d) m
  set na : ℝ → ℝ := fun τ => Torus.cbNorm m (fun x => a τ x - a τ₀ x) with hna
  set nb : ℝ → ℝ := fun τ => Torus.cbNorm m (fun x => b τ x - b τ₀ x) with hnb
  set cb : ℝ := Torus.cbNorm m (b τ₀) with hcb
  set ca : ℝ := Torus.cbNorm m (a τ₀) with hca
  refine ⟨fun τ => C * na τ * (cb + nb τ) + C * ca * nb τ, ?_, ?_⟩
  · have h1 := ha.2 τ₀ hτ₀ m
    have h2 := hb.2 τ₀ hτ₀ m
    have h := (((tendsto_const_nhds (x := C)).mul h1).mul ((tendsto_const_nhds (x := cb)).add h2)).add
      ((tendsto_const_nhds (x := C * ca)).mul h2)
    simpa [mul_assoc] using h
  · intro τ hτ
    have hAτ := sa12w2_ck_of_smooth (ha.1 τ hτ) m
    have hAτ₀ := sa12w2_ck_of_smooth (ha.1 τ₀ hτ₀) m
    have hBτ := sa12w2_ck_of_smooth (hb.1 τ hτ) m
    have hBτ₀ := sa12w2_ck_of_smooth (hb.1 τ₀ hτ₀) m
    have hdA := sa12w2_isCk_sub hAτ hAτ₀
    have hdB := sa12w2_isCk_sub hBτ hBτ₀
    obtain ⟨p1, q1⟩ := hC _ _ hdA hBτ
    obtain ⟨p2, q2⟩ := hC _ _ hAτ₀ hdB
    have e : (fun x => a τ x * b τ x - a τ₀ x * b τ₀ x) =
        (fun x => (a τ x - a τ₀ x) * b τ x) + (fun x => a τ₀ x * (b τ x - b τ₀ x)) := by
      funext x; simp only [Pi.add_apply]; ring
    have eb : (fun x => b τ x) = (fun x => b τ₀ x) + (fun x => b τ x - b τ₀ x) := by
      funext x; simp only [Pi.add_apply]; ring
    have hbb : Torus.cbNorm m (b τ) ≤ cb + nb τ := by
      have := Torus.cbNorm_add_le m _ _ hBτ₀ hdB
      rw [← eb] at this
      exact this
    have hna0 : 0 ≤ na τ := HRS.KernelGrad.cbNorm_nonneg' _ m
    rw [e]
    refine (Torus.cbNorm_add_le m _ _ p1 p2).trans ?_
    have h3 : C * Torus.cbNorm m (fun x => a τ x - a τ₀ x) * Torus.cbNorm m (b τ) ≤
        C * na τ * (cb + nb τ) := by
      have := mul_le_mul_of_nonneg_left hbb (mul_nonneg hC0 hna0)
      simpa [hna] using this
    have h4 : C * Torus.cbNorm m (a τ₀) * Torus.cbNorm m (fun x => b τ x - b τ₀ x) ≤ C * ca * nb τ := le_rfl
    exact add_le_add (q1.trans h3) q2

theorem sa12w2_CC_const_mul {t : ℝ} (c : ℝ) {a : ℝ → Torus d → ℝ} (ha : sa12w2_CC t a) :
    sa12w2_CC t (fun τ x => c * a τ x) :=
  sa12w2_CC_mul (sa12w2_CC_const t c) ha

theorem sa12w2_CC_sum {ι : Type*} {t : ℝ} (s : Finset ι) (a : ι → ℝ → Torus d → ℝ)
    (h : ∀ i ∈ s, sa12w2_CC t (a i)) : sa12w2_CC t (fun τ x => ∑ i ∈ s, a i τ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sa12w2_CC_const t (0 : ℝ)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact sa12w2_CC_add (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### directional derivative -/

theorem sa12w2_dirTor_sub {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (v : Euc d) :
    HRS.KernelGrad.dirTor (fun x => f x - g x) v =
      fun x => HRS.KernelGrad.dirTor f v x - HRS.KernelGrad.dirTor g v x := by
  apply sa12w2_eq_of_lift
  rw [HRS.KernelGrad.lift_dirTor]
  funext y
  have e1 := congrFun (HRS.KernelGrad.lift_dirTor f v) y
  have e2 := congrFun (HRS.KernelGrad.lift_dirTor g v) y
  have hf' : DifferentiableAt ℝ (Torus.lift f) y := (hf.differentiable (by simp)) y
  have hg' : DifferentiableAt ℝ (Torus.lift g) y := (hg.differentiable (by simp)) y
  show fderiv ℝ (fun y => Torus.lift f y - Torus.lift g y) y v =
    Torus.lift (HRS.KernelGrad.dirTor f v) y - Torus.lift (HRS.KernelGrad.dirTor g v) y
  rw [e1, e2, fderiv_fun_sub hf' hg']
  rfl

theorem sa12w2_CC_dir {t : ℝ} {w : ℝ → Torus d → ℝ} (hw : sa12w2_CC t w) (v : Euc d) (hv : ‖v‖ ≤ 1) :
    sa12w2_CC t (fun τ => HRS.KernelGrad.dirTor (w τ) v) := by
  refine sa12w2_CC_of_bound (fun τ hτ => ?_) fun τ₀ hτ₀ m => ?_
  · refine contDiff_infty.2 fun k => ?_
    have := HRS.KernelGrad.isCk_dirTor (h := w τ) (k := k) (by
      have := sa12w2_ck_of_smooth (hw.1 τ hτ) (k + 1)
      simpa using this) v
    exact this
  · refine ⟨fun τ => Torus.cbNorm (m + 1) (fun x => w τ x - w τ₀ x), ?_, ?_⟩
    · exact hw.2 τ₀ hτ₀ (m + 1)
    · intro τ hτ
      have h1 : Torus.IsCk (1 : WithTop ℕ∞) (w τ) := sa12w2_ck_of_smooth (hw.1 τ hτ) 1
      have h2 : Torus.IsCk (1 : WithTop ℕ∞) (w τ₀) := sa12w2_ck_of_smooth (hw.1 τ₀ hτ₀) 1
      have e := sa12w2_dirTor_sub (f := w τ) (g := w τ₀) (by simpa using h1) (by simpa using h2) v
      have hd' : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => w τ x - w τ₀ x) :=
        sa12w2_isCk_sub (sa12w2_ck_of_smooth (hw.1 τ hτ) (m + 1)) (sa12w2_ck_of_smooth (hw.1 τ₀ hτ₀) (m + 1))
      have := HRS.KernelGrad.cbNorm_dirTor_le (h := fun x => w τ x - w τ₀ x) (k := m) hd' hv
      rw [e] at this
      exact this

/-! ### coordinates and the cancellation convolution -/

theorem sa12w2_proj_cbNorm {m : ℕ} {f : Torus d → Euc d} (hf : Torus.IsCk (m : WithTop ℕ∞) f) (j : Fin d) :
    Torus.IsCk (m : WithTop ℕ∞) (fun x => f x j) ∧
      Torus.cbNorm m (fun x => f x j) ≤ Torus.cbNorm m f := by
  set P : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j with hP
  have hl : Torus.lift (fun x => f x j) = P ∘ Torus.lift f := rfl
  have hCk : Torus.IsCk (m : WithTop ℕ∞) (fun x => f x j) := by
    unfold Torus.IsCk at *
    rw [hl]
    exact P.contDiff.comp hf
  refine ⟨hCk, ?_⟩
  unfold Torus.cbNorm
  refine Finset.sum_le_sum fun n hn => ?_
  have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hbdd := HRS.KernelGrad.bddAbove_iteratedFDeriv hf hnm
  refine ciSup_le fun x => ?_
  have hfn : ContDiffAt ℝ (n : WithTop ℕ∞) (Torus.lift f) x :=
    ((hf : ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift f)).of_le (by exact_mod_cast hnm)).contDiffAt
  have h1 := P.norm_iteratedFDeriv_comp_left hfn (n := n) (by exact_mod_cast le_rfl)
  have h2 : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa [hP] using PiLp.norm_apply_le y j
  rw [hl]
  calc ‖iteratedFDeriv ℝ n (P ∘ Torus.lift f) x‖
      ≤ ‖P‖ * ‖iteratedFDeriv ℝ n (Torus.lift f) x‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (Torus.lift f) x‖ := by gcongr
    _ ≤ _ := by
        rw [one_mul]
        exact le_ciSup hbdd x

theorem sa12w2_coeffOf_sub {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) (k : Lattice d) :
    coeffOf (fun x => f x - g x) k = coeffOf f k - coeffOf g k := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int, funFourierCoeff_eq_int]
  push_cast
  simp_rw [mul_sub]
  exact integral_sub (MFAux.integrable_mode_mul_real' (-k) (MFThermal.integrable_of_continuous hf))
    (MFAux.integrable_mode_mul_real' (-k) (MFThermal.integrable_of_continuous hg))

theorem sa12w2_cgc_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f g : Torus d → ℝ}
    (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (j : Fin d) :
    (fun x => (convGradConv (periodicRieszGrad d s) (fun y => f y - g y) x) j) =
      fun x => (convGradConv (periodicRieszGrad d s) f x) j - (convGradConv (periodicRieszGrad d s) g x) j := by
  have hfg : Torus.IsCk 1 (fun y => f y - g y) := sa12w2_isCk_sub hf hg
  have cf := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
    (convGradConv_continuous_of_one_le hd hs0 hsd f hf)
  have cg := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
    (convGradConv_continuous_of_one_le hd hs0 hsd g hg)
  have cfg := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
    (convGradConv_continuous_of_one_le hd hs0 hsd _ hfg)
  refine MFAux.eq_of_funFourierCoeff_eq cfg (cf.sub cg) fun k => ?_
  show coeffOf (fun x => (convGradConv (periodicRieszGrad d s) (fun y => f y - g y) x) j) k =
    coeffOf (fun x => (convGradConv (periodicRieszGrad d s) f x) j -
      (convGradConv (periodicRieszGrad d s) g x) j) k
  have hfc := MFAux.continuous_of_isCk hf
  have hgc := MFAux.continuous_of_isCk hg
  have e5 : coeffOf (fun x => (convGradConv (periodicRieszGrad d s) f x) j -
      (convGradConv (periodicRieszGrad d s) g x) j) k =
      coeffOf (fun x => (convGradConv (periodicRieszGrad d s) f x) j) k -
        coeffOf (fun x => (convGradConv (periodicRieszGrad d s) g x) j) k :=
    sa12w2_coeffOf_sub (f := fun x => (convGradConv (periodicRieszGrad d s) f x) j)
      (g := fun x => (convGradConv (periodicRieszGrad d s) g x) j) cf cg k
  rw [e5]
  have e1 := congrFun (convGradConv_coeff_of_one_le hd hs0 hsd _ hfg j) k
  have e2 := congrFun (convGradConv_coeff_of_one_le hd hs0 hsd f hf j) k
  have e3 := congrFun (convGradConv_coeff_of_one_le hd hs0 hsd g hg j) k
  have e4 := sa12w2_coeffOf_sub hfc hgc
  rw [e1, e2, e3]
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  rw [e4 k]
  ring

theorem sa12w2_CC_cgc (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {t : ℝ} {w : ℝ → Torus d → ℝ}
    (hw : sa12w2_CC t w) (j : Fin d) :
    sa12w2_CC t (fun τ x => (convGradConv (periodicRieszGrad d s) (w τ) x) j) := by
  have hCk : ∀ τ ∈ Icc (0 : ℝ) t, ∀ m : ℕ, Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (w τ) := fun τ hτ m =>
    sa12w2_ck_of_smooth (hw.1 τ hτ) (m + 1)
  refine sa12w2_CC_of_bound (fun τ hτ => ?_) fun τ₀ hτ₀ m => ?_
  · refine contDiff_infty.2 fun m => ?_
    obtain ⟨C, hC⟩ := convGradConv_cbNorm_of_one_le hd hs0 hsd m
    exact (sa12w2_proj_cbNorm (hC _ (by exact_mod_cast hCk τ hτ m)).1 j).1
  · obtain ⟨C, hC⟩ := convGradConv_cbNorm_of_one_le hd hs0 hsd m
    refine ⟨fun τ => C * Torus.cbNorm (m + 1) (fun x => w τ x - w τ₀ x), ?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := C)).mul (hw.2 τ₀ hτ₀ (m + 1))
    · intro τ hτ
      have h1 : Torus.IsCk (1 : WithTop ℕ∞) (w τ) := sa12w2_ck_of_smooth (hw.1 τ hτ) 1
      have h2 : Torus.IsCk (1 : WithTop ℕ∞) (w τ₀) := sa12w2_ck_of_smooth (hw.1 τ₀ hτ₀) 1
      have e := sa12w2_cgc_sub hd hs0 hsd (f := w τ) (g := w τ₀) (by simpa using h1) (by simpa using h2) j
      have hd' : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => w τ x - w τ₀ x) :=
        sa12w2_isCk_sub (hCk τ hτ m) (hCk τ₀ hτ₀ m)
      obtain ⟨p, q⟩ := hC _ (by exact_mod_cast hd')
      have := (sa12w2_proj_cbNorm p j).2
      have e' : (fun x => (convGradConv (periodicRieszGrad d s) (fun y => w τ y - w τ₀ y) x) j) =
          fun x => (convGradConv (periodicRieszGrad d s) (w τ) x) j -
            (convGradConv (periodicRieszGrad d s) (w τ₀) x) j := e
      rw [← e']
      exact this.trans q

end HRS.PDE.SA12W2
