import HRS.Kernel.D1
import HRS.MC.CepK1Aux1

/-!
# Packet K1: circular decomposition of the periodic logarithmic force
-/

noncomputable section

open Real

namespace HRS.MC.CepK1

open HRS

/-- The embedding `ℝ → Euc 1`. -/
def cepk1_ι (u : ℝ) : Euc 1 := WithLp.toLp 2 (fun _ => u)

/-- The force along the line, `u ↦ (∇g)_0 (mk u)`. -/
def cepk1_F (u : ℝ) : ℝ := (periodicRieszGrad 1 0 (Torus.mk (cepk1_ι u))) 0

/-- The remainder `ρ = ∇g + π cot (π u)` (junk values at the integers are `0`). -/
def cepk1_ρ (u : ℝ) : ℝ := cepk1_F u + π * (Real.cos (π * u) / Real.sin (π * u))

lemma cepk1_mk_eq (y : Euc 1) : Torus.mk y = Torus.mk (cepk1_ι (y 0)) := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [Torus.mk, cepk1_ι]

lemma cepk1_mk_add_one (u : ℝ) : Torus.mk (cepk1_ι (u + 1)) = Torus.mk (cepk1_ι u) := by
  funext i
  simp only [Torus.mk, cepk1_ι]
  rw [AddCircle.coe_add]
  simp

lemma cepk1_mk_neg (u : ℝ) : Torus.mk (cepk1_ι (-u)) = -Torus.mk (cepk1_ι u) := by
  funext i
  simp [Torus.mk, cepk1_ι]

lemma cepk1_F_add_one (u : ℝ) : cepk1_F (u + 1) = cepk1_F u := by
  unfold cepk1_F; rw [cepk1_mk_add_one]

lemma cepk1_F_neg (u : ℝ) : cepk1_F (-u) = -cepk1_F u := by
  unfold cepk1_F
  rw [cepk1_mk_neg, PDE.periodicRieszGrad_neg (d := 1) (s := 0) (by norm_num)]
  simp

lemma cepk1_F_zero : cepk1_F 0 = 0 := by
  have := cepk1_F_neg 0
  simp at this
  linarith

lemma cepk1_ρ_add_one (u : ℝ) : cepk1_ρ (u + 1) = cepk1_ρ u := by
  unfold cepk1_ρ
  rw [cepk1_F_add_one, mul_add, mul_one, Real.cos_add_pi, Real.sin_add_pi]
  rw [neg_div_neg_eq]

lemma cepk1_ρ_neg (u : ℝ) : cepk1_ρ (-u) = -cepk1_ρ u := by
  unfold cepk1_ρ
  rw [cepk1_F_neg, mul_neg, Real.cos_neg, Real.sin_neg, div_neg]
  ring

lemma cepk1_ρ_periodic : Function.Periodic cepk1_ρ 1 := cepk1_ρ_add_one

lemma cepk1_ρ_eq_off {y : Euc 1} (_hy : ∀ n : ℤ, y 0 ≠ n) :
    (periodicRieszGrad 1 0 (Torus.mk y)) 0 =
      -(π * (Real.cos (π * y 0) / Real.sin (π * y 0))) + cepk1_ρ (y 0) := by
  rw [cepk1_mk_eq y]
  unfold cepk1_ρ cepk1_F
  ring

lemma cepk1_norm_ι (u : ℝ) : ‖cepk1_ι u‖ = |u| := by
  simp [cepk1_ι, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

lemma cepk1_contDiff_ι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_ι := by
  rw [contDiff_euclidean]
  intro i
  simp only [cepk1_ι]
  exact contDiff_id

lemma cepk1_continuous_mk : Continuous (Torus.mk : Euc 1 → Torus 1) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' 1).comp (EuclideanSpace.proj i).continuous

lemma cepk1_isOpen_offZero : IsOpen {x : Euc 1 | Torus.mk x ≠ 0} :=
  isOpen_compl_singleton.preimage cepk1_continuous_mk

lemma cepk1_mk_ne_zero {u : ℝ} (hu : ∀ n : ℤ, u ≠ n) : Torus.mk (cepk1_ι u) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [Torus.mk, cepk1_ι, Pi.zero_apply] at h0
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  exact hu n (by simpa using hn.symm)

lemma cepk1_sin_ne_zero {u : ℝ} (hu : ∀ n : ℤ, u ≠ n) : Real.sin (π * u) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hu n
  have hpi : π ≠ 0 := Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  linarith

lemma cepk1_F_contDiffAt {u : ℝ} (hu : ∀ n : ℤ, u ≠ n) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_F u := by
  have hS := periodicRieszGrad_smoothOffZero_d1 (s := 0) le_rfl (by norm_num)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (periodicRieszGrad 1 0)) (cepk1_ι u) :=
    hS.contDiffAt (cepk1_isOpen_offZero.mem_nhds (cepk1_mk_ne_zero hu))
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Euc 1 => (Torus.lift (periodicRieszGrad 1 0) x) 0) (cepk1_ι u) :=
    (contDiffAt_euclidean.1 h1) 0
  exact h2.comp u cepk1_contDiff_ι.contDiffAt

lemma cepk1_ρ_contDiffAt_off {u : ℝ} (hu : ∀ n : ℤ, u ≠ n) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_ρ u := by
  unfold cepk1_ρ
  refine (cepk1_F_contDiffAt hu).add ?_
  refine contDiffAt_const.mul ?_
  refine ContDiffAt.div ?_ ?_ (cepk1_sin_ne_zero hu)
  · exact (Real.contDiff_cos.contDiffAt).comp u (contDiffAt_const.mul contDiffAt_id)
  · exact (Real.contDiff_sin.contDiffAt).comp u (contDiffAt_const.mul contDiffAt_id)

lemma cepk1_ρ_contDiffAt_zero : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_ρ 0 := by
  obtain ⟨r, δ, hδ, hr, hr0, hloc⟩ :=
    periodicRieszGrad_local_singularity_d1 (s := 0) le_rfl (by norm_num)
  set rt : ℝ → ℝ := fun u => (r (Torus.mk (cepk1_ι u))) 0 with hrt
  have hrt_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rt := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Euc 1 => (Torus.lift r x) 0) :=
      (contDiff_euclidean.1 (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr)) 0
    exact h1.comp cepk1_contDiff_ι
  have hH : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_H 0 := cepk1_H_analyticAt.contDiffAt
  have hsum := hH.add hrt_sm.contDiffAt
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with u hu
  by_cases hu0 : u = 0
  · subst hu0
    have hz : Torus.mk (cepk1_ι 0) = 0 := by
      funext i; simp [Torus.mk, cepk1_ι]
    simp [cepk1_ρ, cepk1_F_zero, cepk1_H_zero, rt, hz, hr0]
  · have hn : ‖cepk1_ι u‖ < δ := by
      rw [cepk1_norm_ι]; simpa [Real.dist_eq] using hu
    have hne : cepk1_ι u ≠ 0 := by
      intro h
      apply hu0
      have := congrArg (fun v : Euc 1 => v 0) h
      simpa [cepk1_ι] using this
    have h := hloc (cepk1_ι u) hn hne
    have hF : cepk1_F u = -(1 / u) + rt u := by
      unfold cepk1_F
      rw [h]
      simp [KernelD1.eucRieszGrad, KernelD1.rieszRadial, cepk1_ι, rt]
      have h2 : ‖(WithLp.toLp 2 fun _ : Fin 1 => u : Euc 1)‖ = |u| := cepk1_norm_ι u
      rw [h2, sq_abs]
      field_simp
    simp only [cepk1_ρ, hF, cepk1_H_eq hu0]
    ring

lemma cepk1_ρ_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cepk1_ρ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ∀ n : ℤ, x ≠ n
  · exact cepk1_ρ_contDiffAt_off hx
  · push_neg at hx
    obtain ⟨n, rfl⟩ := hx
    have hper : ∀ u, cepk1_ρ u = cepk1_ρ (u - n) := by
      intro u
      have : cepk1_ρ (u - n * 1) = cepk1_ρ u := cepk1_ρ_periodic.sub_int_mul_eq n
      simpa using this.symm
    have h0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => cepk1_ρ (u - n)) (n : ℝ) := by
      have := cepk1_ρ_contDiffAt_zero
      refine ContDiffAt.comp (n : ℝ) (g := cepk1_ρ) (f := fun u : ℝ => u - n) ?_ ?_
      · simpa using this
      · exact (contDiff_id.sub contDiff_const).contDiffAt
    exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall hper)

/-- **K1 (circular decomposition of the periodic logarithmic force)**. -/
theorem cep_K1_force_decomp_proof :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ u, ρ (u + 1) = ρ u) ∧ (∀ u, ρ (-u) = -ρ u) ∧
      ∀ y : Euc 1, (∀ n : ℤ, y 0 ≠ n) →
        (periodicRieszGrad 1 0 (Torus.mk y)) 0 =
          -(Real.pi * (Real.cos (Real.pi * y 0) / Real.sin (Real.pi * y 0))) + ρ (y 0) :=
  ⟨cepk1_ρ, cepk1_ρ_contDiff, cepk1_ρ_add_one, cepk1_ρ_neg, fun _ hy => cepk1_ρ_eq_off hy⟩

end HRS.MC.CepK1
