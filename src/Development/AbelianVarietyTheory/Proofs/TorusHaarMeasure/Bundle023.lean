module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteZeroOrbits

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cpt_origin {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  have : nmat X 0 = ExtFPf.oneF X := by
    funext τ a b
    simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
    split_ifs with h1 h2 h3
    · exact absurd h2 (ne_of_gt h1)
    · rfl
    · rfl
    · rfl
  rw [cpt, this, ExtFPf.rmul_oneF]

theorem eventually_split {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r,
      y = rmul (cpt X x z) b := by
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (hx τ).1
  have hM : ∀ τ, LUPf.Mx X x x τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hu τ)
  have hΔ : LUPf.DeltaF X x x ≠ 0 := by
    have : LUPf.DeltaF X x x = 1 := by
      unfold LUPf.DeltaF
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
      rw [hM]
      exact LUPf.lminor_one k
    rw [this]; exact one_ne_zero
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine (LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero)
      (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm
    rw [Matrix.one_mul]; exact Matrix.one_apply_ne (ne_of_gt h)
  have hz0 : LUPf.zF X x x = 0 := by
    ext k
    set p := (Fintype.equivFin (Ent X)).symm k with hp
    show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0
    rw [hM, hL, inv_one]
    exact Matrix.one_apply_ne (ne_of_gt p.2.2)
  have hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)
  have hn := hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)
  have hc : ContinuousAt (LUPf.zF X x) x :=
    (LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn
  have hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ :=
    hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)
  filter_upwards [hn, hb] with y hy hyb
  refine ⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩
  funext τ
  show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ *
    (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)
  rw [LUPf.nmat_zF]
  show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) :
    Matrix (Fin r) (Fin r) ℂ)
  have hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  rfl

theorem isolated_of_det {n : ℕ} {f : V n → V n} (hdet : (fderiv ℂ f 0).det ≠ 0) (h0 : f 0 = 0) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  by_cases hd : DifferentiableAt ℂ f 0
  · exact HE.iso_zero hd.hasFDerivAt hdet h0
  · refine ⟨1, one_pos, fun y _ _ => ?_⟩
    have hk := HE.ker_bot_of_det hdet
    rw [fderiv_zero_of_not_differentiableAt hd] at hk
    have : y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) := by simp
    rw [hk] at this
    exact (Submodule.mem_bot ℂ).1 this

def orbitSetoid {r : ℕ} (X : Data E r) : Setoid (Frame X.Ψ r) where
  r x y := ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
  iseqv := by
    refine ⟨fun x => ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]
    · rintro x y ⟨γ, hγ, b, hb, rfl⟩
      refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
      rw [← FundSetPf.lact_rmul, FundSetPf.lact_inv, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    · rintro x y z ⟨γ, hγ, b, hb, rfl⟩ ⟨γ', hγ', b', hb', rfl⟩
      refine ⟨γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc]

theorem finite_orbits : ∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ),
    X.IsSec L w0 → (∀ k, X.IsSec L (s k)) →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ k, s k x = 0) ↔ ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j' := by
  classical
  intro r X L w0 s _ hs hsimp C hC hCd hmeet
  set S := orbitSetoid X with hS

  have hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0) := by
    rintro x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩
    have hxb := OntoS.dom_rmul X hx hb
    refine ⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩
    rw [(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]

  have hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y := by
    intro x hx h0
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_det (hsimp x hx h0).2 (by
      ext k
      simp [cpt_origin, h0 k])
    filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0
    have hR : S.r (cpt X x z) y := ⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩
    have h1 := (hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2
    have hz0 : z = 0 := hiso z hz (by
      ext k
      simp [h1 k])
    rwa [hz0, cpt_origin] at hR
  have hK : IsCompact (C ∩ {x | ∀ k, s k x = 0}) := by
    have hcont : ContinuousOn (fun x k => s k x) C :=
      continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd
    have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))
    have he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0} := by
      ext x; simp [funext_iff]
    rw [he]
    exact hC.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y})
    (fun x hx => hloc x (hCd hx.1) hx.2)
  set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT
  have hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1,
    fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨γ, hγ, b, hb, hc⟩ := hmeet x hx h0
    have hR : S.r x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    have h1 := (hstab _ _ hR ⟨hx, h0⟩).2
    obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)
    refine ⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))
  · rintro ⟨j, hj⟩
    exact (hstab _ x hj (hout _ (T.equivFin.symm j).2)).2
  · intro j j' γ hγ b hb h
    have hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out := ⟨γ, hγ, b, hb, h⟩
    have := Quotient.sound (s := S) hR
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact T.equivFin.symm.injective (Subtype.ext this)

end GlobalTheory.FiniteZeroOrbits
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem isOpen_cell {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (ho : IsOrth X x1)
    {N : Set (V (nd X))} (hN : IsOpen N) (hNO : N ⊆ OmF X x1) :
    IsOpen {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x1 ho
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} =
      {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N := by
    ext x
    constructor
    · rintro ⟨y, hy, b, hb, rfl⟩
      obtain ⟨h1, h2, -⟩ := huniq y (hNO hy) b hb
      refine ⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩
      rw [Set.mem_preimage, h2]
      exact hy
    · rintro ⟨⟨hx, hd⟩, hzN⟩
      obtain ⟨-, h2, h3⟩ := hsplit x hx hd
      exact ⟨zOf x, hzN, bOf x, h2, h3⟩
  rw [heq]
  exact hz.continuousOn.isOpen_inter_preimage hU hN

theorem isOpen_saturation : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 →
    ∀ N : Set (V (nd X)), IsOpen N → N ⊆ OmF X x1 →
    IsOpen {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} := by
  intro r X x1 ho N hN hNO
  have heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} =
      ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
    · rintro ⟨γ, hγ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ, hγ, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  rw [heq]
  exact isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)

end GlobalTheory.SatOpen
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.OrthFrameMahler

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c

theorem norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by
  have h1 : rmul z t τ a c = z τ a c * t τ c c := by
    show ∑ k, z τ a k * t τ k c = _
    refine Finset.sum_eq_single c (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ c) h)
    rw [(hdiag τ k).2 c (Ne.symm hk), mul_zero]
  calc ‖z τ a c‖ = ‖rmul z t τ a c‖ := by
        rw [h1, norm_mul, (hdiag τ c).1, mul_one]
    _ ≤ ‖rmul z t τ a‖ := norm_le_pi_norm _ c
    _ ≤ ‖rmul z t τ‖ := norm_le_pi_norm _ a
    _ ≤ ‖rmul z t‖ := norm_le_pi_norm _ τ

theorem exists_bound_orthonormal_frame :
    (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x →
      ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  intro r X ε hε
  obtain ⟨K, hKc, hKd, hK⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨β, hβc, hβ⟩ := GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt (E := E) r X
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (continuousOn_rmul_self (hβc.mono hKd))
  refine ⟨R, fun x hx hla => ?_⟩
  obtain ⟨γ, hγ, b, hb, hy⟩ := hK x (IW.orth_mem_dom X x hx) hla
  refine ⟨γ, X.Γ_stab γ hγ, fun τ a c => ?_⟩
  obtain ⟨hβb, hβo⟩ := hβ _ (hKd hy)
  have hRy : ‖rmul (lact γ (rmul x b)) (β (lact γ (rmul x b)))‖ ≤ R := hR _ hy
  generalize β (lact γ (rmul x b)) = s at hβb hβo hRy
  rw [FundSetPf.lact_rmul, ExtFPf.rmul_assoc] at hβo hRy
  have hγo : IsOrth X (lact γ x) := fun σ => by rw [OntoS.gram_lact X hγ]; exact hx σ
  have hdiag := (GlobalTheory.isOrth_rmul_iff_unitary_diagonal r X _ _ hγo (ExtFPf.mul_mem X hb hβb)).1 hβo
  exact (norm_apply_le_of_diagonal _ _ hdiag τ a c).trans hRy

end GlobalTheory.OrthFrameMahler
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def satFrames (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ z ∈ A, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b}

theorem measurableSet_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ : X.Ψ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a : Fin r, ⋂ c : Fin r, ⋂ (_ : c < a), {b : Frame X.Ψ r | b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
    exact (isOpen_ne_fun hM.matrix_det continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem continuous_rmul (X : Data E r) :
    Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact (hM.comp continuous_fst).matrix_mul (hM.comp continuous_snd)

theorem continuous_lact (X : Data E r) (γ : GL (Fin r) E) :
    Continuous fun x : Frame X.Ψ r => lact γ x := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem rmul_right_cancel (X : Data E r) {y b b' : Frame X.Ψ r} (hy : y ∈ X.dom)
    (h : rmul y b = rmul y b') : b = b' := by
  funext τ
  have h1 : mat y τ * mat b τ = mat y τ * mat b' τ := congrFun h τ
  have hu : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (hy τ).1
  have := congrArg (fun M => (mat y τ)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

theorem measurableSet_satFrames (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (satFrames X x0 A) := by
  have h : satFrames X x0 A =
      (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (A ×ˢ Bor X.Ψ r) := by
    ext x
    constructor
    · rintro ⟨z, hz, b, hb, rfl⟩; exact ⟨(z, b), ⟨hz, hb⟩, rfl⟩
    · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩; exact ⟨z, hz, b, hb, rfl⟩
  rw [h]
  have : PolishSpace (Fin r → ℂ) := inferInstance
  have : PolishSpace (Fin r → Fin r → ℂ) := inferInstance
  have : PolishSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X)) := inferInstance
  refine MeasurableSet.image_of_continuousOn_injOn (hA.prod (measurableSet_Bor X)) ?_ ?_
  · exact ((continuous_rmul X).comp (((FundSetPf.cont_cpt X x0).comp continuous_fst).prodMk
      continuous_snd)).continuousOn
  · rintro ⟨z, b⟩ ⟨hz, hb⟩ ⟨z', b'⟩ ⟨-, hb'⟩ hh
    obtain rfl : z = z' := FundSetPf.cpt_uniq X ho hb hb' hh
    exact Prod.ext rfl (rmul_right_cancel X (hAO hz) hh)

theorem rmul_mem_satFrames_iff (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X)))
    (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ satFrames X x0 A ↔ x ∈ satFrames X x0 A := by
  constructor
  · rintro ⟨z, hz, b', hb', h⟩
    refine ⟨z, hz, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨z, hz, b', hb', rfl⟩
    exact ⟨z, hz, rmul b' b, ExtFPf.mul_mem X hb' hb, by rw [ExtFPf.rmul_assoc]⟩

theorem cpt_mem_satFrames_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (A : Set (V (nd X))) (z : V (nd X)) : cpt X x0 z ∈ satFrames X x0 A ↔ z ∈ A := by
  constructor
  · rintro ⟨z', hz', b, hb, h⟩
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rw [FundSetPf.cpt_uniq X ho (ExtFPf.oneF_mem X) hb h]; exact hz'
  · intro hz
    exact ⟨z, hz, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X _).symm⟩

theorem cpt_lact (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := (FundSetPf.lact_rmul γ _ _).symm

theorem isOrth_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : IsOrth X (lact γ x0) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

theorem muF_lact (X : Data E r) (x0 : Frame X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    muF X (lact γ x0) = muF X x0 := by
  have h1 : OmF X (lact γ x0) = OmF X x0 := by
    ext z
    show cpt X (lact γ x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
    rw [cpt_lact]
    refine ⟨fun h => ?_, OntoS.dom_lact X hγ⟩
    have := OntoS.dom_lact X (X.Γ.inv_mem hγ) h
    rwa [FundSetPf.lact_inv] at this
  have h2 : densF X (lact γ x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_lact, OntoS.gram_lact X hγ]
  simp only [muF, h1, h2]

theorem unique_translate (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by
  obtain ⟨z, hz, b, hb, h⟩ := h
  obtain ⟨z', hz', b', hb', h'⟩ := h'
  have hδ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ
  have e1 : lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) b) = rmul (cpt X x0 z') b' := by
    rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hbb := ExtFPf.mul_mem X hb (ExtFPf.invF_mem X hb')
  have e2 : cpt X x0 z' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) (rmul b (ExtFPf.invF X b'))) := by
    rw [← ExtFPf.rmul_assoc, FundSetPf.lact_rmul, e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb',
      ExtFPf.rmul_oneF]
  obtain rfl : z = z' := hF.2.2.1 z hz z' hz' _ hδ _ hbb e2
  have e3 : lact (γ'⁻¹ * γ) (cpt X x0 z) = rmul (cpt X x0 z) (rmul b' (ExtFPf.invF X b)) := by
    rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
      ExtFPf.rmul_oneF]
  have := X.Γ_free _ hδ _ (hF.2.1 hz) _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e3
  exact (inv_mul_eq_one.mp this).symm

theorem lintegral_unfold (hM : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (ho : IsOrth X x0) (FF : Set (V (nd X))) (hF : IsFundSet X x0 FF) (ψ : Frame X.Ψ r → ℝ≥0∞)
    (hψ : Measurable ψ) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := measurableSet_satFrames X ho hF.1 hF.2.1
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let φ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun x => lact (γ.1)⁻¹ x) ⁻¹' satFrames X x0 FF).indicator ψ
  have hφm : ∀ γ, Measurable (φ γ) := fun γ =>
    hψ.indicator ((continuous_lact X _).measurable hS)
  have hφB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ γ (rmul x b) = φ γ x := by
    intro γ x hx b hb
    simp only [φ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      rmul_mem_satFrames_iff X x0 FF _ hb, hB x hx b hb]
  have h1 : ∀ᵐ z ∂muF X x0, ψ (cpt X x0 z) = ∑' γ : X.Γ, φ γ (cpt X x0 z) := by
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    have hm : lact γ⁻¹ (cpt X x0 z) ∈ satFrames X x0 FF :=
      ⟨z', hz', b, hb, by rw [h, FundSetPf.lact_inv]⟩
    rw [tsum_eq_single (⟨γ, hγ⟩ : X.Γ)]
    · exact (Set.indicator_of_mem (s := (fun x => lact γ⁻¹ x) ⁻¹' satFrames X x0 FF) hm ψ).symm
    · intro γ' hne
      refine Set.indicator_of_notMem (fun hm' => hne ?_) ψ
      exact Subtype.ext (unique_translate X hF γ'.2 hγ hm' hm)
  rw [lintegral_congr_ae h1,
    lintegral_tsum (f := fun γ z => φ γ (cpt X x0 z)) fun γ => ((hφm γ).comp hc).aemeasurable,
    lintegral_tsum (f := fun (γ : X.Γ) z => ψ (lact γ.1 (cpt X x0 z))) fun γ : X.Γ =>
      ((hψ.comp (continuous_lact X γ.1).measurable).comp hc).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [hM r X x0 (lact γ.1 x0) ho (isOrth_lact X ho γ.2) (φ γ) (hφm γ) (hφB γ), muF_lact X x0 γ.2,
    ← lintegral_indicator hF.1]
  refine lintegral_congr fun z => ?_
  simp only [φ, Set.indicator, Set.mem_preimage, cpt_lact, FundSetPf.lact_inv,
    cpt_mem_satFrames_iff X ho]

end GlobalTheory.Unfold
end
