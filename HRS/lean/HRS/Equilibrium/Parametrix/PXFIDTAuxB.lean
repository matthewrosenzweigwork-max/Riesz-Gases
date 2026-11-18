import HRS.Equilibrium.Parametrix.PXFIDTAuxA
import HRS.Equilibrium.Parametrix.Assembly

/-!
# Packet PX-FID-T, file B: size bounds of the tangential derivatives of `ψ^loc`

* `tanL es G`: the iterated tangential derivative on the cover, `lift2 (tanIter es ψ) = tanL es (lift2 ψ)`;
* `tanL` is compatible with sums off the diagonal and with `ContDiffOn`;
* `fidt_psi_bnds`: `Px5Bnds` for `tanIter es (parxPsi f n)` with constant `C |f|_{m+2} ∏‖e_i‖`
  whenever `2n + |es| ≤ m` (the tangential derivatives only use up conormal derivatives).
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx.PXFIDT

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- Iterated tangential derivative on the covering space. -/
def tanL : List (Euc d) → (Euc d × Euc d → ℝ) → Euc d × Euc d → ℝ
  | [], G => G
  | e :: es, G => dirD (e, e) (tanL es G)

theorem lift2_tanIter (es : List (Euc d)) (ψ : Torus d → Torus d → ℝ) :
    lift2 (tanIter es ψ) = tanL es (lift2 ψ) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    show lift2 (tanDeriv e (tanIter es ψ)) = dirD (e, e) (tanL es (lift2 ψ))
    rw [lift2_tanDeriv_eq, ih]

theorem contDiffOn_tanL {U : Set (Euc d × Euc d)} (hU : IsOpen U) :
    ∀ (es : List (Euc d)) (j : ℕ) {G : Euc d × Euc d → ℝ},
      ContDiffOn ℝ ((es.length + j : ℕ) : WithTop ℕ∞) G U →
        ContDiffOn ℝ (j : WithTop ℕ∞) (tanL es G) U
  | [], j, G, h => by simpa [tanL] using h
  | e :: es, j, G, h => by
    have h1 : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (tanL es G) U :=
      contDiffOn_tanL hU es (j + 1) (by
        have : (e :: es).length + j = es.length + (j + 1) := by simp; omega
        rw [this] at h; exact h)
    show ContDiffOn ℝ (j : WithTop ℕ∞) (dirD (e, e) (tanL es G)) U
    exact contDiffOn_dirD hU h1 (e, e)

theorem contDiffOn_top_tanL {U : Set (Euc d × Euc d)} (hU : IsOpen U) (es : List (Euc d))
    {G : Euc d × Euc d → ℝ} (h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tanL es G) U := by
  rw [contDiffOn_infty] at h ⊢
  intro n
  exact contDiffOn_tanL hU es n (h (es.length + n))

theorem tanL_add_eqOn {U : Set (Euc d × Euc d)} (hU : IsOpen U) :
    ∀ (es : List (Euc d)) {G₁ G₂ : Euc d × Euc d → ℝ},
      ContDiffOn ℝ (es.length : WithTop ℕ∞) G₁ U → ContDiffOn ℝ (es.length : WithTop ℕ∞) G₂ U →
      Set.EqOn (tanL es (fun p => G₁ p + G₂ p)) (fun p => tanL es G₁ p + tanL es G₂ p) U
  | [], G₁, G₂, _, _ => fun p _ => rfl
  | e :: es, G₁, G₂, h1, h2 => by
    intro p hp
    have h1' : ContDiffOn ℝ (es.length : WithTop ℕ∞) G₁ U :=
      h1.of_le (by exact_mod_cast (by simp : es.length ≤ (e :: es).length))
    have h2' : ContDiffOn ℝ (es.length : WithTop ℕ∞) G₂ U :=
      h2.of_le (by exact_mod_cast (by simp : es.length ≤ (e :: es).length))
    have ih := tanL_add_eqOn hU es h1' h2'
    have hev : tanL es (fun p => G₁ p + G₂ p) =ᶠ[𝓝 p] fun p => tanL es G₁ p + tanL es G₂ p :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hp) ih
    have c1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (tanL es G₁) U :=
      contDiffOn_tanL hU es 1 h1
    have c2 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (tanL es G₂) U :=
      contDiffOn_tanL hU es 1 h2
    have d1 : DifferentiableAt ℝ (tanL es G₁) p :=
      (c1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
    have d2 : DifferentiableAt ℝ (tanL es G₂) p :=
      (c2.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
    show fderiv ℝ (tanL es (fun p => G₁ p + G₂ p)) p (e, e) =
      fderiv ℝ (tanL es G₁) p (e, e) + fderiv ℝ (tanL es G₂) p (e, e)
    rw [hev.fderiv_eq, fderiv_fun_add d1 d2]
    rfl

theorem tanIter_add_offDiag (es : List (Euc d)) {ψ₁ ψ₂ : Torus d → Torus d → ℝ}
    (h1 : ContDiffOn ℝ (es.length : WithTop ℕ∞) (lift2 ψ₁) (offDiag d))
    (h2 : ContDiffOn ℝ (es.length : WithTop ℕ∞) (lift2 ψ₂) (offDiag d)) (x y : Torus d)
    (hxy : x ≠ y) :
    tanIter es (fun x y => ψ₁ x y + ψ₂ x y) x y = tanIter es ψ₁ x y + tanIter es ψ₂ x y := by
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have e1 : ∀ ψ : Torus d → Torus d → ℝ, tanIter es ψ x y =
      lift2 (tanIter es ψ) (Torus.rep x, Torus.rep y) := by
    intro ψ; simp [lift2, Torus.mk_rep]
  rw [e1, e1 ψ₁, e1 ψ₂, lift2_tanIter, lift2_tanIter, lift2_tanIter]
  exact tanL_add_eqOn isOpen_offDiag es h1 h2 hp

theorem tanIter_zero (es : List (Euc d)) :
    tanIter es (fun _ _ : Torus d => (0 : ℝ)) = fun _ _ => 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    show tanDeriv e (tanIter es (fun _ _ : Torus d => (0 : ℝ))) = fun _ _ => 0
    rw [ih]
    funext x y
    have h0 : lift2 (fun _ _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
    simp [tanDeriv, h0]

theorem Px5Bnds.congr_offDiag {K : ℝ} {ψ ψ' : Torus d → Torus d → ℝ}
    (hψ : ∀ x y, x ≠ y → ψ x y = ψ' x y) (h : Px5Bnds s K ψ') : Px5Bnds s K ψ := by
  have hE : Set.EqOn (lift2 ψ) (lift2 ψ') (offDiag d) := fun p hp => hψ _ _ hp
  have hN : ∀ p ∈ offDiag d, lift2 ψ =ᶠ[𝓝 p] lift2 ψ' := fun p hp =>
    Filter.eventuallyEq_of_mem (isOpen_offDiag.mem_nhds hp) hE
  refine ⟨h.smooth2.congr hE, fun x y hxy => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hψ x y hxy]; exact h.size x y hxy
  · rw [(hN p hp).fderiv_eq]; exact h.grad p hp
  · rw [((hN p hp).iteratedFDeriv ℝ 2).eq_of_nhds]; exact h.hess p hp

/-- `ψ^loc_n` and its tangential derivatives satisfy the bounds with constant
`C |f|_{m+2} ∏ ‖e_i‖`, `C` independent of `es` (`2 n + |es| ≤ m`). -/
theorem fidt_psi_bnds (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∀ n : ℕ, 2 * n ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ es : List (Euc d), 2 * n + es.length ≤ m →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Px5Bnds s (C * posSeminorm (m + 2) f * (es.map fun e => ‖e‖).prod)
        (tanIter es (parxPsi d s V β ρ f n)) := by
  have hs0 : 0 < s := px5_s_pos H
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, le_rfl, fun es _ f hf => ?_⟩
    have e : tanIter es (parxPsi d s V β ρ f 0) = fun _ _ => 0 := by
      have : parxPsi d s V β ρ f 0 = fun _ _ => 0 := by
        funext x y; simp [parxPsi]
      rw [this, tanIter_zero]
    rw [e, zero_mul, zero_mul]
    exact Px5Bnds.zero s
  | succ n ih =>
    intro hn
    obtain ⟨C1, hC1, h1⟩ := ih (by omega)
    obtain ⟨C2, hC2, h2⟩ := parxN_conormal H m n (by omega)
    obtain ⟨Cw, hCw0, hCw, hmn⟩ : ∃ Cw : ℝ, 0 ≤ Cw ∧
        Px5W s (s - (n : ℝ) / 2 - 2)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) Cw ∧ True := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact ⟨1, zero_le_one, px5W_sharp hs0, trivial⟩
      · obtain ⟨Cw, hCw0, hCw⟩ := px5W_coarse (s := s) (τ := s - (n : ℝ) / 2 - 2)
          (by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
            linarith)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
          (fun c => by split_ifs <;> simp)
        exact ⟨Cw, hCw0, hCw, trivial⟩
    refine ⟨C1 + 16 * (C2 * (1 + Cw)), by positivity, fun es hes f hf => ?_⟩
    have hcl := h2 f hf
    have hidx : m - 2 * n = (m - 2 * n - es.length) + es.length := by omega
    rw [hidx] at hcl
    have hT := conormal_tanIter es hcl
    have hP0 : 0 ≤ (es.map fun e => ‖e‖).prod :=
      List.prod_nonneg (by intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
    have hB0 : 0 ≤ C2 * posSeminorm (m + 2) f * (es.map fun e => ‖e‖).prod :=
      mul_nonneg (mul_nonneg hC2 (posSeminorm_nonneg' _ _)) hP0
    have hN := Px5Bnds.of_conormal hT (by omega) hB0 hCw0 hCw
    have hsum := (h1 es (by omega) f hf).add hN
    have hsm1 : ContDiffOn ℝ (es.length : WithTop ℕ∞) (lift2 (parxPsi d s V β ρ f n)) (offDiag d) :=
      (parxPsi_smooth_offDiag H f hf n).of_le (by exact_mod_cast le_top)
    have hsm2 : ContDiffOn ℝ (es.length : WithTop ℕ∞)
        (lift2 (newtonOp d β ρ (parxR d s V β ρ f n))) (offDiag d) := by
      refine hcl.smooth.of_le ?_
      exact_mod_cast (by omega : es.length ≤ m - 2 * n - es.length + es.length)
    have e : parxPsi d s V β ρ f (n + 1) = fun x y => parxPsi d s V β ρ f n x y +
        newtonOp d β ρ (parxR d s V β ρ f n) x y := by
      funext x y; simp [parxPsi, Finset.sum_range_succ]
    have e2 : C1 * posSeminorm (m + 2) f * (es.map fun e => ‖e‖).prod +
        16 * (C2 * posSeminorm (m + 2) f * (es.map fun e => ‖e‖).prod * (1 + Cw)) =
        (C1 + 16 * (C2 * (1 + Cw))) * posSeminorm (m + 2) f * (es.map fun e => ‖e‖).prod := by
      ring
    rw [← e2]
    refine Px5Bnds.congr_offDiag (fun x y hxy => ?_) hsum
    rw [e]
    exact tanIter_add_offDiag es hsm1 hsm2 x y hxy

end HRS.Parx.PXFIDT

end
