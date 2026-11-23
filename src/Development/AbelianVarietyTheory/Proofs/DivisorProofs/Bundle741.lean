module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapTmulOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle702
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin.Holo

open Matrix
open scoped ComplexOrder

noncomputable section

theorem differentiable_det {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : Type*} [Fintype n]
    [DecidableEq n] (f : F → Matrix n n ℂ) (hf : ∀ i j, Differentiable ℂ fun x => f x i j) :
    Differentiable ℂ fun x => (f x).det := by
  simp only [Matrix.det_apply']
  fun_prop

theorem det_block_ne {r p : ℕ} (hp : p ≤ r) (m : Matrix (Fin r) (Fin r) ℂ)
    (hpos : ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp)).PosDef) :
    (m.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro hdet
  set A := m.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hdc : (A.map (starRingEnd ℂ)).det = 0 := by
    rw [show A.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix A from rfl, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdc
  have h := hpos.dotProduct_mulVec_pos hv
  set u : Fin r → ℂ := fun k => ∑ b, starRingEnd ℂ (m k (Fin.castLE hp b)) * v b with hu_def
  have hu : ∀ i : Fin p, u (Fin.castLE hp i) = 0 := fun i => by
    have := congrFun hAv i
    simpa [hA, Matrix.mulVec, dotProduct, u] using this
  have hq : star v ⬝ᵥ ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp) *ᵥ v) =
      ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) := by

    simp only [dotProduct, mulVec, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, hu_def, map_sum, map_mul, Complex.conj_conj,
    Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]
    ring
  have hq' : ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) =
      ((∑ k : Fin r, sgn p (k : ℕ) * Complex.normSq (u k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hq, hq', Complex.zero_lt_real] at h
  refine absurd h (not_lt.2 (Finset.sum_nonpos fun k _ => ?_))
  by_cases hk : (k : ℕ) < p
  · have h0 : u k = 0 := by
      have := hu ⟨k, hk⟩
      rwa [show Fin.castLE hp ⟨k, hk⟩ = k from Fin.ext rfl] at this
    simp [h0]
  · simp only [sgn, if_neg hk]
    nlinarith [Complex.normSq_nonneg (u k)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_Mx₂₂_ne (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) : (KU.Mx X x0 x τ).toBlocks₂₂.det ≠ 0 := by
  have h0 := ExF.det_ne_of_orth X ho τ
  set m := (mat x0 τ)⁻¹ * mat x τ with hm
  have hxm : mat x τ = mat x0 τ * m := by
    rw [hm, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 h0)]
  have hg : gram τ.1 X.Gm (mat x τ) = mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ) := by
    rw [hxm, FrameDegreeData.gram_mul, ho τ]
  have hpos := X.gramPos_posDef hx τ
  rw [Data.gramPos, hg] at hpos
  have hb : (KU.Mx X x0 x τ).toBlocks₂₂ = m.submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
    ext i j
    simp [KU.Mx, KU.tl, Matrix.toBlocks₂₂, KU.eT_inr, m]
  rw [hb]
  exact det_block_ne X.p0_le m hpos

theorem differentiable_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i j) :
    Differentiable ℂ fun x : Frame X.Ψ r => KU.Mx X x0 x τ i j := by
  simp only [KU.Mx, KU.tl, Matrix.submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

theorem qS_differentiableOn (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (k : ℕ) :
    DifferentiableOn ℂ (qS X x0 k) X.dom := by
  have hd1 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).det := fun τ =>
    differentiable_det _ (differentiable_Mx X x0 τ)
  have hd2 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det := fun τ =>
    differentiable_det (fun x => (KU.Mx X x0 x τ).toBlocks₂₂) fun i j =>
      differentiable_Mx X x0 τ (Sum.inr i) (Sum.inr j)
  have hq : qS X x0 k = ∏ τ, fun x : Frame X.Ψ r =>
      ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k := by
    funext x
    simp [qS, Finset.prod_apply]
  rw [hq]
  refine Finset.prod_induction _ (fun g : Frame X.Ψ r → ℂ => DifferentiableOn ℂ g X.dom)
    (fun a b ha hb => ha.mul hb) (differentiableOn_const 1) fun τ _ => ?_
  have hne : ∀ x ∈ X.dom, (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (det_Mx₂₂_ne X ho hx τ)
  have h1 := (hd1 τ).differentiableOn (s := X.dom)
  have h2 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
    ((hd2 τ).differentiableOn).pow 2
  have h3 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom := by
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv hne)
  exact h3.pow k

theorem qS_holomorphicOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r),
    IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom :=
  fun _ _ _ _ _ X x0 ho k => qS_differentiableOn X x0 ho k

end

end GlobalTheory.ScalarPoin.Holo
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDeg

theorem etale_morphismRestrict_of_goodCover {k : Type} [CommRing k] {X Y : Scheme.{0}}
    (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (U : X.Opens) (hG : GoodCover p π D δ U) :
    Etale (π ∣_ U) := by
  obtain ⟨hU, hπU, -, hét, -⟩ := hG
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_map_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (O : X.Opens) (hO : O = X.basicOpen g) (hle : O ≤ W) :
    (X.presheaf.map (homOfLE hle).op).hom.Etale := by
  subst hO
  have := hW.isLocalization_basicOpen g
  exact Algebra.Etale.of_isLocalizationAway g

theorem algX_comp {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X)
    (W : X.Opens) (V : Y.Opens) (h : V ≤ π ⁻¹ᵁ W) :
    ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) V =
      (π.appLE W V h).hom.comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) := by
  have e : (π ≫ p).appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) =
      p.appLE ⊤ W (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ π.appLE W V h := by
    first
      | rw [Scheme.Hom.appLE_comp_appLE]
      | (rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE])
      | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc, Scheme.Hom.naturality_assoc]; rfl)
  ext r
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, RingHom.comp_apply]
  rw [e, CommRingCat.comp_apply]

theorem etale_pullback_coords : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  intro k _ X Y p q π hπ D δ U hG W x hW hx z hzU hzW
  subst hπ
  have hE := etale_morphismRestrict_of_goodCover p π D δ U hG
  obtain ⟨hU, hπU, -⟩ := hG
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

end GlobalTheory.CoverDeg
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

open Matrix

noncomputable section

theorem normSq_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    Complex.normSq g.det = 1 := by
  have hJ : (Jf p q).det * (Jf p q).det = 1 := by
    rw [← det_mul, sumBdJf_mul_Jf, det_one]
  have hJ0 : (Jf p q).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h1 := congrArg det (show gᴴ * Jf p q * g = Jf p q from h)
  rw [det_mul, det_mul, det_conjTranspose] at h1
  have h2 : ((Complex.normSq g.det : ℂ) - 1) * (Jf p q).det = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : star g.det = (starRingEnd ℂ) g.det := rfl
    rw [this] at h1
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ0
  exact_mod_cast sub_eq_zero.1 h3

theorem norm_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    ‖g.det‖ = 1 := by
  have h1 := normSq_det_of_isUpq h
  rw [Complex.normSq_eq_norm_sq] at h1
  have h0 := norm_nonneg g.det
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Mx_self (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    KU.Mx X x0 x0 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl, Matrix.submatrix_one_equiv]

theorem norm_fac_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    ‖(KU.Mx X x0 (lact γ x0) τ).det / (KU.Mx X x0 (lact γ x0) τ).toBlocks₂₂.det ^ 2‖ =
      (Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det)⁻¹ := by
  rw [KU.Mx_lact X ho, Mx_self X ho, Matrix.mul_one, norm_div, norm_pow,
    norm_det_of_isUpq (KU.gm_upq X ho hγ τ), Complex.normSq_eq_norm_sq, one_div]

theorem one_add_fsq_le (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det :=
  sumBd_detD_ge (KU.gm_upq X ho hγ τ)

theorem norm_qS_lact_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧
      (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  intro E _ _ _ r X x0 ho γ hγ
  classical
  set N : X.Ψ → ℝ := fun τ => Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det with hNdef
  have hF : ∀ τ, 1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ N τ := fun τ => one_add_fsq_le X ho hγ τ
  have hN1 : ∀ τ, 1 ≤ N τ := fun τ => by
    have := sumBdFsq_nonneg (KU.gm X x0 γ τ).toBlocks₁₂; linarith [hF τ]
  have hq : ‖qS X x0 1 (lact γ x0)‖ = ∏ τ, (N τ)⁻¹ := by
    simp only [qS, pow_one]
    rw [norm_prod]
    exact Finset.prod_congr rfl fun τ _ => norm_fac_lact X ho hγ τ
  have ha0 : ∀ τ, 0 ≤ (N τ)⁻¹ := fun τ => inv_nonneg.2 (by linarith [hN1 τ])
  have ha1 : ∀ τ, (N τ)⁻¹ ≤ 1 := fun τ => inv_le_one_of_one_le₀ (hN1 τ)
  refine ⟨?_, fun h1 σ => ?_⟩
  · rw [hq]; exact Finset.prod_le_one₀ (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
  · rw [hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ)] at h1
    have hP0 : 0 ≤ ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := Finset.prod_nonneg fun τ _ => ha0 τ
    have hP1 : ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ ≤ 1 := Finset.prod_le_one₀ (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
    have hs : 1 ≤ (N σ)⁻¹ := by
      calc (1 : ℝ) = (N σ)⁻¹ * ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := h1.symm
        _ ≤ (N σ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hP1 (ha0 σ)
        _ = (N σ)⁻¹ := mul_one _
    have hNs : N σ ≤ 1 := by
      have hpos : 0 < N σ := by linarith [hN1 σ]
      rw [le_inv_comm₀ one_pos hpos, inv_one] at hs
      exact hs
    have hF0 : sumBdFsq (KU.gm X x0 γ σ).toBlocks₁₂ ≤ 0 := by linarith [hF σ]
    ext i j
    have he := sumBd_entry_le_fsq (KU.gm X x0 γ σ).toBlocks₁₂ i j
    have : Complex.normSq ((KU.gm X x0 γ σ).toBlocks₁₂ i j) = 0 :=
      le_antisymm (by linarith) (Complex.normSq_nonneg _)
    simpa using this

end

end GlobalTheory.ScalarPoin
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem etale_closure_of_field : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  intro H A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hAR₁ f hf φ hφ β hβ DA _ _ q act hq hqA htor P₁ _ hS₁ hS π hπ y hy
  haveI := hS₁
  haveI := hS
  letI algSS₁ : Algebra (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) :=
    (Localization.localRingHom (P₁.comap φ) P₁ φ rfl).toAlgebra
  have hloc : ∀ r : R, algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
      (algebraMap R (Localization.AtPrime (P₁.comap φ)) r) = algebraMap R₁ (Localization.AtPrime P₁) (φ r) :=
    Localization.localRingHom_to_map _ _ _ rfl
  have hR₁S₁ : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hRS : Function.Injective (algebraMap R (Localization.AtPrime (P₁.comap φ))) :=
    IsLocalization.injective _ (P₁.comap φ).primeCompl_le_nonZeroDivisors
  have hπS : algebraMap A (Localization.AtPrime (P₁.comap φ)) π =
      algebraMap R (Localization.AtPrime (P₁.comap φ)) (algebraMap A R π) :=
    IsScalarTower.algebraMap_apply A R _ π
  have hφw : φ (algebraMap A R π) = algebraMap A₁ R₁ (f π) := by
    rw [← RingHom.comp_apply, hφ]; rfl
  have hπ0 : f π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    have h0 : π = 0 := (injective_iff_map_eq_zero f).1 hf π h
    rw [h0, map_zero]
  have hx0 : algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π)) ≠ 0 := by
    rw [hφw]
    intro h
    exact hπ0 ((injective_iff_map_eq_zero _).1 hAR₁ _ ((injective_iff_map_eq_zero _).1 hR₁S₁ _ h))
  have hxu : ¬ IsUnit (algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π))) := by
    intro hu
    rw [← hloc] at hu
    haveI := Localization.isLocalHom_localRingHom (P₁.comap φ) P₁ φ rfl
    apply hπ.not_isUnit
    rw [hπS]
    exact isUnit_of_map_unit (Localization.localRingHom (P₁.comap φ) P₁ φ rfl) _ hu
  have hSS₁ : Function.Injective
      (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0'
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0' hπ
    have h2 := hn.map (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁))
    rw [hx, map_pow, hπS, hloc] at h2
    exact pow_ne_zero n hx0 (h2.eq_zero_iff.1 rfl)
  have hqS : IsUnit ((q : Localization.AtPrime (P₁.comap φ))) := by
    have := hqA.map (algebraMap A (Localization.AtPrime (P₁.comap φ)))
    rwa [map_natCast] at this
  have hy' : (algebraMap R₁ (Localization.AtPrime P₁) y) ^ q =
      algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
        (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) := by
    rw [← map_pow, hy, hπS, hloc]
  have hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ (algebraMap A R π))) := by
    rw [hφw]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (f π), f π, mem_nonZeroDivisors_of_ne_zero hπ0, rfl⟩ :
        Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  exact etale_closure_core H A R hAR A₁ R₁ hAR₁ φ β hβ DA q act hq htor
    (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) hRS hR₁S₁ hloc hSS₁ hqS
    (algebraMap A _ π) hπ (algebraMap R₁ _ y) hy' (φ (algebraMap A R π)) hx0 hxu hxB

end GlobalTheory.KeyOriginTransport
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.localization_at_prime_etale_compat : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  first | (exact @GlobalTheory.KeyOriginBC.pointAtZero_bc) | (exact GlobalTheory.KeyOriginBC.pointAtZero_bc) | (intros; apply GlobalTheory.KeyOriginBC.pointAtZero_bc  <;> assumption)
end
