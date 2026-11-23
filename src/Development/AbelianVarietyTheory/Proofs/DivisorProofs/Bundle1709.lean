module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveProd

theorem product_formula_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  intro k _ Y _ _ q hq f hf
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int k Y q hq
  have := hAff
  have := hFin
  have : Module.Finite ℤ k := hq.finite
  have hgen : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : CharZero Γ(Y, ⊤) := (flat_int_iff_charZero (q ≫ spMap (Int.castRingHom k))).1 hq.flat
  have : IsFractionRing Γ(Y, ⊤) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)

  have finHom : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], Finite (B →+* ℂ) := by
    intro B _ _
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
    have hint : ∀ x : B, IsIntegral ℤ x := fun x => Algebra.IsIntegral.isIntegral x
    choose p hpm hp using hint
    let T : Set (s → ℂ) :=
      Set.pi Set.univ fun x => {z : ℂ | ((p x).map (Int.castRingHom ℂ)).IsRoot z}
    have hT : T.Finite :=
      Set.Finite.pi fun x => Polynomial.finite_setOfPred_isRoot ((hpm x).map _).ne_zero
    have hmem : ∀ φ : B →+* ℂ, (fun x : s => φ x) ∈ T := by
      intro φ x _
      show Polynomial.eval (φ (x : B)) ((p x).map (Int.castRingHom ℂ)) = 0
      rw [Polynomial.eval_map]
      rw [← show φ.comp (algebraMap ℤ B) = Int.castRingHom ℂ from RingHom.ext_int _ _,
        ← Polynomial.hom_eval₂, hp x, map_zero]
    let F : (B →+* ℂ) → T := fun φ => ⟨fun x => φ x, hmem φ⟩
    have hF : Function.Injective F := by
      intro φ ψ h
      have h' : Set.EqOn φ.toAddMonoidHom.toIntLinearMap ψ.toAddMonoidHom.toIntLinearMap (s : Set B) := by
        intro x hx
        have := congrArg (fun t : T => t.1 ⟨x, hx⟩) h
        simpa [F] using this
      have hl := LinearMap.ext_on hs h'
      ext x
      exact LinearMap.congr_fun hl x
    have : Finite T := hT.to_subtype
    exact Finite.of_injective F hF

  have finZero : ∀ c : Γ(Y, ⊤), Finite (Γ(Y, ⊤) ⧸ Ideal.span {c}) →
      {z : Y | z ∉ Y.basicOpen c}.Finite := by
    intro c _
    have hS : (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {c})))).Finite :=
      Set.finite_range _
    refine (hS.preimage fun _ _ _ _ h => Y.toSpecΓ.isOpenEmbedding.injective h).subset ?_
    intro z hz
    have h1 : Y.toSpecΓ z ∉ PrimeSpectrum.basicOpen c := by
      intro h
      apply hz
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact h
    show Y.toSpecΓ z ∈ Set.range _
    apply (Set.ext_iff.1 (range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective) _).2
    have h2 : c ∈ (Y.toSpecΓ z).asIdeal := by
      by_contra h
      exact h1 h
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff.2 h2

  have hgb : ∀ c : Γ(Y, ⊤), c ≠ 0 → genericPoint Y ∈ Y.basicOpen c := by
    intro c hc
    by_contra h
    apply hc
    rw [← basicOpen_eq_bot_iff (X := Y) (U := ⊤) c, ← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
    rintro ⟨x, hx⟩
    exact h (gen_mem hx)

  have hsupp : ∀ c : Γ(Y, ⊤), c ≠ 0 → (Function.support fun z =>
      (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
        Real.log (Nat.card (Y.residueField z))).Finite := by
    intro c hc
    refine (finZero c (GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc).1).subset ?_
    intro z hz hzc
    apply hz
    have hu : UnitAt z (algebraMap Γ(Y, ⊤) Y.functionField c) :=
      (unitAt_fnOf_iff (U := ⊤) trivial hgen c).2 hzc
    simp only
    rw [hu.ord_eq_zero]
    simp

  have key : ∀ c : Γ(Y, ⊤), c ≠ 0 →
      ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) =
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField c) y‖ := by
    intro c hc
    obtain ⟨hfq, hlog⟩ := GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc
    have := hfq
    rw [GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths k Y q hq c hc, ← GlobalTheory.T.log_card_eq_finsum_length_localized_maximal Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ Ideal.span {c}), hlog,
      GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms k Y q hq c]

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, ⊤) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hinj := IsFractionRing.injective Γ(Y, ⊤) Y.functionField
  have ha'0 : algebraMap Γ(Y, ⊤) Y.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb'0 : algebraMap Γ(Y, ⊤) Y.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ z, Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z =
        Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z -
          Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z := by
    intro z
    have h := Scheme.ord_mul (x := z) (div_ne_zero ha'0 hb'0) hb'0
    rw [div_mul_cancel₀ _ hb'0] at h
    omega

  have hpt : ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖ -
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    intro σ y
    have hg : under y = genericPoint Y := GlobalTheory.TwistTop.under_eq_genericPoint hq y
    have hua : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen a).2 (hgb a ha0)
    have hub : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen b).2 (hgb b hb0)
    have huq : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [div_eq_mul_inv]
      exact hua.mul hub.inv
    have hm : ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y =
        ratVal (algebraMap Γ(Y, ⊤) Y.functionField a / algebraMap Γ(Y, ⊤) Y.functionField b) y *
          ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y := by
      rw [← ratVal_mul huq.regAt hub.regAt, div_mul_cancel₀ _ hb'0]
    rw [hm, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero huq))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hub))]
    ring
  have hL : ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) =
      (∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z : ℝ) *
          Real.log (Nat.card (Y.residueField z))) -
        ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) := by
    rw [← finsum_sub_distrib (hsupp a ha0) (hsupp b hb0)]
    refine finsum_congr fun z => ?_
    rw [hord z]
    push_cast
    ring
  have hR : ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
      (∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖) -
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    have : Finite (k →+* ℂ) := finHom k
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun σ => ?_
    have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun y => hpt σ y
  rw [hL, hR, key a ha0, key b hb0]

end GlobalTheory.CurveProd
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HeckeP

theorem mem_range_map_subtype {B : Type} [CommRing B] (R : Subring B) {n : ℕ} (g : GL (Fin n) B) :
    g ∈ (GeneralLinearGroup.map R.subtype).range ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) B) i j ∈ R) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) R) i j).2
    · rw [← map_inv]; exact ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) R => X.map R.subtype) :=
      fun X Y e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
    have hM : M.map R.subtype = (g : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have hM' : M'.map R.subtype = ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have e1 : M * M' = 1 := hinj (by
      show (M * M').map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have e2 : M' * M = 1 := hinj (by
      show (M' * M).map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

variable (p : ℕ) [Fact p.Prime]

theorem inclK_mem_intKQ_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) :
    inclK p K r a ∈ intKQ p K r ↔ a ∈ GlobalTheory.LKLoc.intK p K := by
  constructor
  · intro h
    have h1 := GlobalTheory.LKRes.Model.mulMap_intKQ p K r _ h
    have h2 : GlobalTheory.LKRes.Model.mulMap p K r (inclK p K r a) = (a : PadicAlgCl p) := by
      show (a : PadicAlgCl p) * 1 = _
      rw [mul_one]
    rw [h2] at h1
    exact (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 h1
  · intro h
    exact Subring.subset_closure (Or.inl ⟨⟨a, h⟩, rfl⟩)

theorem map_inclK_mem_Kres_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ Kres p K n r ↔ g ∈ GlobalTheory.LKLoc.KintK p K n := by
  unfold Kres GlobalTheory.LKLoc.KintK
  rw [mem_range_map_subtype, mem_range_map_subtype, ← map_inv]
  simp only [GeneralLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, RingHom.mapMatrix_apply]
  simp [Matrix.map_apply, inclK_mem_intKQ_iff]

theorem scalar_mem_Kint_iff (r : ℕ) (s : ℚ_[p]ˣ) :
    (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom s) ∈
        GlobalTheory.LKLoc.Kint p (Q0 p) 1 r ↔ ‖(s : ℚ_[p])‖ ≤ 1 ∧ ‖((s⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
  unfold GlobalTheory.LKLoc.Kint
  rw [mem_range_map_subtype, ← map_inv, ← map_inv]
  have key : ∀ t : ℚ_[p], algebraMap ℚ_[p] (Qr p r) t ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖ ≤ 1 := by
    intro t
    rw [GlobalTheory.LKLoc.intR, Subring.mem_comap, ValuationSubring.mem_toSubring, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
      ← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]
  have key' : ∀ t : ℚ_[p], (algebraMap ℚ_[p] (Qr p r) t)⁻¹ ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖⁻¹ ≤ 1 := by
    intro t; rw [← map_inv₀, key, norm_inv]
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, key, key']

theorem inclG_mem_KHT_iff (G : HTGroup p) (r : ℕ) (x : Gp G) :
    inclG G r x ∈ KHT p G.m G.n r G.Fw ↔
      (‖(x.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((x.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ∧
        ∀ w, x.2 w ∈ GlobalTheory.LKLoc.KintK p (G.Fw w) G.n := by
  unfold KHT
  rw [Subgroup.mem_prod, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  have h1 : (inclG G r x).1 =
      (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom x.1) := rfl
  have h2 : ∀ w, (inclG G r x).2 w = GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (x.2 w) :=
    fun w => rfl
  rw [h1, scalar_mem_Kint_iff]
  simp only [h2, map_inclK_mem_Kres_iff]

theorem gl_one_map_conj {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) (g : GL (Fin 1) R) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hc : ∀ a b : GL (Fin 1) R, a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have : (MulAut.conj g).toMonoidHom = MonoidHom.id _ := MonoidHom.ext fun x => by
    show g * x * g⁻¹ = x
    rw [hc g x, mul_inv_cancel_right]
  rw [this, Subgroup.map_id]

theorem Kres_commensurable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    Subgroup.Commensurable ((Kres p K n r).map (MulAut.conj g).toMonoidHom) (Kres p K n r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  have mono : ∀ (x : KQ p K r) (k l : ℕ), k ≤ l → (p : KQ p K r) ^ k * x ∈ intKQ p K r →
      (p : KQ p K r) ^ l * x ∈ intKQ p K r := by
    intro x k l hkl h
    rw [← Nat.add_sub_cancel' hkl, pow_add, mul_comm ((p : KQ p K r) ^ k), mul_assoc]
    exact mul_mem (pow_mem (natCast_mem _ p) _) h
  choose f hf using GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers p K r
  let k : ℕ := (Finset.univ.sup fun ij : Fin n × Fin n => f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) ⊔
    Finset.univ.sup fun ij : Fin n × Fin n => f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)
  have hk1 : ∀ i j, (p : KQ p K r) ^ k * (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_left.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  have hk2 : ∀ i j, (p : KQ p K r) ^ k *
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_right.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  let c : intKQ p K r := (p : intKQ p K r) ^ k
  have hc : (c : KQ p K r) = (p : KQ p K r) ^ k := by simp [c]
  have hfin : Finite (intKQ p K r ⧸ Ideal.span {c * c}) := by
    have h := GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow p K r (2 * k) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p K (2 * k)) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p (Qr p r) (2 * k))
    have e : c * c = (p : intKQ p K r) ^ (2 * k) := by simp only [c]; ring
    rw [e]; exact h
  exact GlobalTheory.T.commensurable_conj_range_gl_map_subtype (intKQ p K r) n c hfin g (fun i j => by rw [hc]; exact hk1 i j)
    (fun i j => by rw [hc]; exact hk2 i j)

end GlobalTheory.HeckeP


open GlobalTheory.HeckeP in
theorem GlobalTheory.heckeOperator_integral :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
      (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom)
        (KHT p G.m G.n r G.Fw)) ∧
      (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧
      (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  intro p _ G r hr
  refine ⟨fun g => ?_, ?_, ?_⟩
  · unfold KHT
    exact GlobalTheory.T.commensurable_map_conj_prod_pi' _ _ g (by rw [gl_one_map_conj])
      (fun i => Kres_commensurable p (G.Fw i) G.n r hr (g.2 i))
  · ext x
    rw [Subgroup.mem_comap, Kp0, Subgroup.mem_comap, inclG_mem_KHT_iff, inclG_mem_KHT_iff]
  · rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.LKRes.Model.sigHT_KHT p _ _ _ _ x hx
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.FinClsLoc.BaseChangeCent in
theorem GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg :
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ) (L : Type) [Ring L] [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι →
    (∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c) →
    ∀ (K : Type) [Field K] [Algebra ℚ K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) ∧
      ∀ x : K ⊗[ℚ] G.C, x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        Commute x (inC G K (Y : G.C)) ∧
          inC G K (β : G.C) * (starT G.star K x).unop * inC G K ((β⁻¹ : G.Cˣ) : G.C) = x := by
  intro p _ G β Y L _ _ ι hinj hrange K _ _
  have hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro c
    change _ ↔ c ∈ Set.range ι
    rw [phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    rfl
  have hex' := Module.Flat.lTensor_exact K hex
  refine ⟨?_, ?_⟩
  · have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj
    intro a b hab
    apply this
    rw [← hmap, ← hmap, hab]
  · intro x
    have e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        x ∈ Set.range (ι.toLinearMap.lTensor K) := by
      constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩
    rw [e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi,
      Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    exact and_congr Iff.rfl Iff.rfl
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.FinClsLoc.support_subset_compact) | (exact GlobalTheory.FinClsLoc.support_subset_compact) | (intros; apply GlobalTheory.FinClsLoc.support_subset_compact  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  first | (exact @GlobalTheory.FinClsLoc.localTransfer) | (exact GlobalTheory.FinClsLoc.localTransfer) | (intros; apply GlobalTheory.FinClsLoc.localTransfer  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  first | (exact @GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (exact GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (intros; apply GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  first | exact @GlobalTheory.ChernCalc.curv_lowerTriangular | exact GlobalTheory.ChernCalc.curv_lowerTriangular | (intros; apply GlobalTheory.ChernCalc.curv_lowerTriangular <;> assumption)
end
