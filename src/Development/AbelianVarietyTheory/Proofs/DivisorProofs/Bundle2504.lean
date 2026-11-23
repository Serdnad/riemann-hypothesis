module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle083
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.factorDepth_bounds_inert_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  first | exact @GlobalTheory.RefSum.facBetween_inert | exact GlobalTheory.RefSum.facBetween_inert | (intros; apply GlobalTheory.RefSum.facBetween_inert <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffInt

theorem coeff_valuation_le_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  refine ⟨S₁ ∪ hfin.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg hL
    hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G
    (fun y' Y hY hch => hG y' Y 1 hY (by rw [Units.val_one]; exact hch)) μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hw]
  exact Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)

end GlobalTheory.CoeffInt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pO1_comp {R : Type} [CommRing R] {Z Y A : Over (Sp R)} (i : Z ⟶ Y) (f : Y ⟶ A) (x : HO1 A.hom) :
    pO1 i (pO1 f x) = pO1 (i ≫ f) x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 _ _ _ _ _ _ _ _ (ovw f) _ _ _ _ _ (ovw i) _ _ (ovw (i ≫ f)) (Over.comp_left _ _ _ _ _)
    (fun _ ↦ rfl)).1 x

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (x : HO1 A.hom) : pO1 (𝟙 A) x = x :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 x

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (x : HO1 (𝟙_ (Over (Sp R))).hom) : x = 0 := by
  have : IsAffine (𝟙_ (Over (Sp R))).left := by
    change IsAffine (Sp R); infer_instance
  exact (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).2 _ _ x

theorem pO1_toUnit_comp {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (x : HO1 A.hom) :
    pO1 (toUnit Y ≫ f) x = 0 := by
  rw [← pO1_comp, pO1_unit_eq_zero (pO1 f x), map_zero]

theorem primO1_of_axesO1 {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : AxesVanishingStructureSheafDegOne A) : StructureSheafH1Primitive A := by
  intro x
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  apply h
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_right, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_left, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : CatCoh.H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [GlobalTheory.CatCoh.cup_mk, GlobalTheory.CatCoh.cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [GlobalTheory.CatCoh.d1_apply, Submodule.coe_add, Pi.add_apply, GlobalTheory.CatCoh.cupZ_apply, GlobalTheory.CatCoh.Z1.comp a,
    GlobalTheory.CatCoh.Z1.comp b, map_mul, map_neg]
  ring

theorem cup_self_eq_zero_of_prim {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hP : StructureSheafH1Primitive A)
    (hN : NoPrimitiveStructureSheafH2 A) (x : HO1 A.hom) : cup _ x x = 0 := by
  have key : ∀ f : A ⊗ A ⟶ A, structureSheafH2Pullback f (cup _ x x) = cup _ (pO1 f x) (pO1 f x) := fun f ↦
    ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 _ _ _ _ _ _ _ _ (ovw f)).1 x x
  apply hN
  rw [key, key, key, hP x]
  simp only [map_add (f := _), LinearMap.add_apply]
  have := cup_add_cup_swap (OAff (A ⊗ A).hom) (pO1 (fst A A) x) (pO1 (snd A A) x)
  linear_combination (norm := module) this

theorem cup_self_eq_zero_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R))
    [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  intro R _ _ A _ g hA hg x
  exact cup_self_eq_zero_of_prim A (primO1_of_axesO1 A (GlobalTheory.T.axes_vanishing_noetherian_abelian R A g hA hg)) (GlobalTheory.T.abelian_scheme_no_primitive_O2 R A g hA hg) x

end GlobalTheory.AbCoh
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu


open GlobalTheory.AV.KerPart in
theorem isIsog_hasLogDeg_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  intro p _ k _ A B G H t t' f hf
  have hp : p.Prime := Fact.out
  obtain ⟨N, g, hN, -, hfg, hgf⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have kill : ∀ {T : Over (Sp k)} (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ (p ^ a * m) = 1 :=
    fun x hx => pow_eq_one_of_comp hfg x hx
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (m : ℤ_[p]) := by
      by_contra h
      have h1 : (m : ℤ_[p]) ∈ nonunits ℤ_[p] := h
      rw [PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg PadicInt.toZMod hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff] at h2
      exact hm h2
    obtain ⟨u, hu⟩ := hu
    have hs : (↑u⁻¹ : ℤ_[p]) * ((p ^ a * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ a := by
      push_cast
      rw [← hu, mul_left_comm, Units.inv_mul, mul_one]
    have eA : ((p ^ a * m) • 𝟙 A : A ⟶ A).hom = 𝟙 A.X ^ (p ^ a * m) := by simp
    have eB : ((p ^ a * m) • 𝟙 B : B ⟶ B).hom = 𝟙 B.X ^ (p ^ a * m) := by simp
    haveI : IsMonHom (𝟙 A.X ^ (p ^ a * m)) := eA ▸ inferInstance
    haveI : IsMonHom (𝟙 B.X ^ (p ^ a * m)) := eB ▸ inferInstance
    have h1 : t.map t' f.hom ≫ t'.map t g.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 G := by
      rw [← TorsionTower.map_comp, ← t.map_pow_id]
      exact t.map_congr t (by rw [← comp_hom, hfg, eA])
    have h2 : t'.map t g.hom ≫ t.map t' f.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 H := by
      rw [← TorsionTower.map_comp, ← t'.map_pow_id]
      exact t'.map_congr t' (by rw [← comp_hom, hgf, eB])
    refine ⟨a, (↑u⁻¹ : ℤ_[p]) • t'.map t g.hom, ?_, ?_⟩
    · rw [Linear.comp_smul, h1, smul_smul, hs]
    · rw [Linear.smul_comp, h2, smul_smul, hs]
  · obtain ⟨H₀, _, _, i₀, hK₀, hdeg⟩ := GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree k A B f hf
    obtain ⟨Hm, _, _, im, hKm, hpm⟩ := GlobalTheory.T.exists_kernelPart_order_prime_to_p p k A B f m hm0 hm
    have hcop : (p ^ a).Coprime m := (Nat.Coprime.pow_left a ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).symm))
    obtain ⟨H₁, _, _, i₁, hK₁, hrank⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f (p ^ a) m hcop _ _ _ _ (kerPow_kerPt t t' f a) hKm
    have h01 : Module.finrank k H₁ = deg f := (finrank_eq_of_kerPow hK₁ hK₀ fun R _ _ x hx =>
      iff_of_true (kill x hx) (pow_zero x)).trans hdeg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (finrank_quot_kerIdeal_dvd (t.map t' f.hom) a)
    have hv : padicValNat p (deg f) = j := by
      rw [← h01, hrank, hj, Nat.padicValNat_def,
        Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero)
          (fun h0 => hpm (by rw [h0]; exact dvd_zero p)),
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨a, fun n hn => ?_⟩
    rw [hv, ← hj]
    refine finrank_eq_of_kerPow (kerPow_kerPt t t' f n) (kerPow_kerPt t t' f a) fun R _ _ x hx => ?_
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := pow_gcd_eq_one.2 ⟨h, kill x hx⟩
      have h3 : (p ^ n).gcd (p ^ a * m) = p ^ a := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, Nat.gcd_mul_left, (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)), mul_one]
      rwa [h3] at h2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_mul, h, one_pow]

end GlobalTheory.Dieu
end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem coinv_stab_snd (P Q R S : ℕ) (x : ℂ) : Stab (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro Z y hy
  have hcomm := (GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S).2.2.2.2
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Z f, ?_⟩
    rw [map_sub, map_smul, hcomm]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem degW_le_of_abs_le {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) (B : ℚ) (hμ : ∀ a, |μ a| ≤ B) :
    degW c μ ≤ ((p + q : ℕ) : ℚ) * (B + |c|) := by
  unfold degW
  have h : ∀ a, |shiftNu c μ a| ≤ B + |c| := by
    intro a
    rcases a with i | j
    · simp only [shiftNu]; exact (abs_sub _ _).trans (add_le_add (hμ _) le_rfl)
    · simp only [shiftNu]; exact (abs_add_le _ _).trans (add_le_add (hμ _) le_rfl)
  calc ∑ a, |shiftNu c μ a| ≤ ∑ _a : Ix p q, (B + |c|) := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Finset.card_univ, Fintype.card_sum]; ring

theorem fockCoinvariantKernel_highestWeight_admissible (P Q R S : ℕ) (x : ℂ) : AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro B
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ ⌊((R + S : ℕ) : ℚ) * (B + |cPair P Q|)⌋₊, inferInstance, ?_⟩
  intro μ hμ v hv
  obtain ⟨-, hL2, -, hw2, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  have hgood : Good (fockAct2 P Q R S) := ⟨hL2, hw2, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩
  obtain ⟨hspan, -, hK2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inl rfl))
  have hKc : KStable (fockAct2 P Q R S) (coinv P Q R S x) := fun X _ w hw => coinv_stab_snd P Q R S x X w hw
  have hv' : v ∈ (Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x) ⊓ hwSub (fockAct2 P Q R S) μ :=
    ⟨by rw [GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top]; exact Submodule.mem_top, hv⟩
  have hsplit := GlobalTheory.T.howeHighestWeight_sup_stable_le R S _ (fockAct2 P Q R S) hgood _ _ hK2 hKc μ hv'
  obtain ⟨h, hh, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  refine Submodule.add_mem_sup ?_ hc.1
  rw [mem_restrictTotalDegree]
  have hh2 : h ∈ harm2 P Q R S := by rw [← hspan]; exact hh.1
  exact (GlobalTheory.DegKeep.deg_le_of_harm hh2 hh.2).trans (Nat.floor_mono (degW_le_of_abs_le _ μ B hμ))

theorem coinv_stab_adm : ∀ (P Q R S : ℕ) (x : ℂ),
    Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) :=
  fun P Q R S x => ⟨coinv_stab_snd P Q R S x, fockCoinvariantKernel_highestWeight_admissible P Q R S x⟩

end GlobalTheory.HoweR

end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.Places

section One

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_hwSub_iff (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub a μ ↔ (∀ c, a (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → a (Eab c d) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem hw_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ := by
  rw [mem_hwSub_iff] at hv ⊢
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · rw [← h, hv.1 c, map_smul]
  · rw [← h, hv.2 c d hcd, map_zero]

end One

section Quad

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem qop_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) (α β : ℂ)
    (a b : ι) {v : M} (hv : v ∈ H) : qop F α β a b v ∈ H := by
  unfold qop
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
  refine H.sub_mem (H.sub_mem (H.sum_mem fun c _ => hF _ _ _ (hF _ _ _ hv)) (H.smul_mem _ (hF _ _ _ hv))) ?_
  by_cases hab : a = b
  · simpa [hab] using H.smul_mem β hv
  · simp [hab]

theorem negT_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) :
    ∀ a b, ∀ u ∈ H, negT F a b u ∈ H := fun a b u hu => by
  simp only [negT, LinearMap.neg_apply]
  exact H.neg_mem (hF b a u hu)

end Quad

theorem multi_place_step : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (α β α' β' : T → ℂ), ∃ B : ℚ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ N N' : Submodule ℂ V, N < N' →
    (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') → (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) N N') →
    ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) ∧ ∃ v ∈ N', (∀ w, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
  intro T _ _ R S α β α' β'
  have hk := fun w => GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient (R w) (S w) (α w) (β w) (α' w) (β' w)
  choose Bw hBw using hk
  refine ⟨∑ w, |Bw w|, ?_⟩
  intro V _ _ a hG hc N N' hNN' hsN hsN' hQ
  have hB : ∀ w, |Bw w| ≤ ∑ w, |Bw w| := fun w =>
    Finset.single_le_sum (f := fun w => |Bw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have h0 : (0 : ℚ) ≤ ∑ w, |Bw w| := Finset.sum_nonneg fun w _ => abs_nonneg (Bw w)
  have key : ∀ s : Finset T, ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ ∑ w, |Bw w|) ∧
      ∃ v ∈ N', (∀ w ∈ s, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨v, hv, hvN⟩ := SetLike.exists_of_lt hNN'
      exact ⟨fun _ _ => 0, fun _ _ => by simpa using h0, v, hv, by simp, hvN⟩
    | insert w s hws ih =>
      obtain ⟨μ, hμB, v, hvN', hvs, hvN⟩ := ih
      let H : Submodule ℂ V := ⨅ w' ∈ s, hwSub (a w') (μ w')
      have memH : ∀ u, u ∈ H ↔ ∀ w' ∈ s, u ∈ hwSub (a w') (μ w') := fun u => by
        simp only [H, Submodule.mem_iInf]
      have sH : ∀ Z, ∀ u ∈ H, a w Z u ∈ H := fun Z u hu => by
        rw [memH] at hu ⊢
        intro w' hw'
        exact hw_comm (fun Z' x => hc w w' (fun e => hws (e ▸ hw')) Z Z' x) (hu w' hw')
      have sU : ∀ c d, ∀ u ∈ H, units (a w) c d u ∈ H := fun c d u hu => sH _ u hu
      have hlt : N ⊓ H < N' ⊓ H := by
        refine lt_of_le_of_ne (inf_le_inf_right _ hNN'.le) fun e => hvN ?_
        have : v ∈ N' ⊓ H := ⟨hvN', (memH v).2 hvs⟩
        rw [← e] at this
        exact this.1
      have hS1 : Stab (a w) (N ⊓ H) := fun Z u hu => ⟨hsN w Z u hu.1, sH Z u hu.2⟩
      have hS2 : Stab (a w) (N' ⊓ H) := fun Z u hu => ⟨hsN' w Z u hu.1, sH Z u hu.2⟩
      have hQ' : QuadMod (a w) (α w) (β w) (α' w) (β' w) (N ⊓ H) (N' ⊓ H) := fun c d u hu =>
        ⟨⟨(hQ w c d u hu.1).1, qop_mem _ H sU _ _ c d hu.2⟩,
          ⟨(hQ w c d u hu.1).2, qop_mem _ H (negT_mem _ H sU) _ _ c d hu.2⟩⟩
      obtain ⟨ν, hνB, u, huN', huhw, huN⟩ := hBw w V (a w) (hG w) _ _ hlt hS1 hS2 hQ'
      refine ⟨Function.update μ w ν, fun w' c => ?_, u, huN'.1, fun w' hw' => ?_, fun h => huN ⟨h, huN'.2⟩⟩
      · rcases eq_or_ne w' w with rfl | e
        · simp only [Function.update_self]
          exact (hνB c).trans ((le_abs_self _).trans (hB w'))
        · rw [Function.update_of_ne e]
          exact hμB w' c
      · rcases Finset.mem_insert.1 hw' with rfl | hw''
        · simpa using huhw
        · have hne : w' ≠ w := fun e => hws (e ▸ hw'')
          rw [Function.update_of_ne hne]
          exact (memH u).1 huN'.2 w' hw''
  obtain ⟨μ, hμ, v, hv, hvs, hvN⟩ := key Finset.univ
  exact ⟨μ, hμ, v, hv, fun w => hvs w (Finset.mem_univ w), hvN⟩

end GlobalTheory.HoweR.Places

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.latticeLink_of_surviving_simple_subquotient : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | exact GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | (intros; apply GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving <;> assumption)
end
