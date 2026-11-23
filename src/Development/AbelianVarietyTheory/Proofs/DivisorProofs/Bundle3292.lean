module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

theorem eImage_equiv_conj : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F A' G' _ _ U' oA oG hSA hOL σ p₀ p p' hy hg hext
  have hB := D'.tau_bimult
  obtain ⟨b, hb⟩ := GlobalTheory.T.idempotent_image_base_point_rational_fractionField T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F p₀ p hy hg
  have hc := GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hg ⟨b, hb⟩
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) =
      algebraMap _ _ := σ.toAlgHom.comp_algebraMap
  have hpp : QkExt σ.toAlgHom.toRingHom p p := by
    refine ⟨rfl, ?_, hc⟩
    rw [hb, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact (RingHom.congr_fun hσ x).symm
  have hg' : p.g = p'.g :=
    GlobalTheory.TorusExt.gt_ext_val (Over.OverMorphism.ext (hpp.2.1.trans hext.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (hpp.2.2 χ) _).trans (val_corr hJ (hext.2.2 χ) _).symm
  have hy' : p.y = p'.y := hpp.1.trans hext.1.symm
  have hp : p = p' := by
    obtain ⟨y, g, e⟩ := p
    obtain ⟨y', g', e'⟩ := p'
    obtain rfl : y = y' := hy'
    obtain rfl : g = g' := hg'
    rfl
  rw [← hp]
  exact qk_equiv_refl hB p

end GlobalTheory.Mum.GalFixQ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.Periods

theorem inv_eq_unit_mul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (g : D.X → (FractionRing R)ˣ) {y : D.X} {r : R} (hr : Formalism.L2.Pj.PsiCoord D y r)
    (hU : PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y Set.univ) :
    ∃ u : Rˣ, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ u * algebraMap R _ r := by
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D g) y v := by
    let D' := GlobalTheory.TauTwist.rescale D g
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D' y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D' y j hj
    obtain ⟨s, hs, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  obtain ⟨x', hx', e'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D g) y _).1 hv
  have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord (GlobalTheory.TauTwist.rescale D g) y (g y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j h) := by
    refine ⟨j, h, hj, ?_⟩
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (g y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (g y : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  obtain ⟨u, hu⟩ := h₁.unique hx'
  have k := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, e, e'] at k
  have k' : (g y : FractionRing R) * algebraMap R _ r = algebraMap R _ ((u * v : Rˣ) : R) := by
    rw [k, Units.val_mul, map_mul]; rfl
  refine ⟨(u * v)⁻¹, ?_⟩
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [mul_left_comm, k', ← map_mul, Units.inv_mul, map_one]

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C D' L θ₀ e β hβ hact hL hc N ε hε
  letI := H.starRing
  obtain ⟨-, hbm, hgen, o₀, ho₀, hw₀⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  letI : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨g, hD, q, hxe, hpr, hU, qs, qa, qb, hg⟩ := GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau (H := H) θ₀ (mulDeg L.D l.M') o₀ C.P.D.toPre C.P.oD e β
    hbm hgen hw₀ C.P.D.tau_bimult C.P.w0 hβ (fun a => by rw [ho₀]; exact hact a) hL hc
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := (Nat.cast_ne_zero.2 (level_pos l).ne').isUnit
    simpa using h1.map C.b
  obtain ⟨s, hs₁, hs₂, hs⟩ := GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots H L.D.X V hV.1.2.2.2 hk l.M' hM C.m N ε C.s C.s_ne_zero
    (fun a b => q (e.symm a) (e.symm b)) (fun a b => qs _ _) (fun a a' b => by simp only [map_add (f := _), qa])
    (fun x a b => by simp only [map_smul, qb]) (fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨u, n, hn, hco⟩ := C.mono y
      obtain ⟨v, hv⟩ := inv_eq_unit_mul _ g hco (hU y)
      refine ⟨v * u, ?_⟩
      rw [map_smul, e.symm_apply_apply, ← hg, hv, Units.val_mul, map_mul, map_mul, map_prod, _root_.mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, ← zpow_natCast]
      congr 1
      have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H L.D.X).le (ε (.inl i)).2) (e y)
      have h2 := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hε, pull_apply, LinearEquiv.coe_coe, h1, smul_eq_mul] at h2
      linarith)
  refine ⟨s, hs₁, hs₂, g, hD, fun y => ?_, hxe, fun x => ?_⟩
  · rw [hg, ← hs, map_smul, e.symm_apply_apply]
  · have := hact x
    rw [← hpr] at this
    exact this.trans (Category.assoc _ _ _)

end GlobalTheory.UCanon.Periods
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivTorsRat

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_char_descend {X K F : Type} [Group X] [Field K] [Field F] (f : K →+* F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (t : X →* Fˣ) (ht : t ^ k = 1) :
    ∃ t₀ : X →* Kˣ, (Units.map f.toMonoidHom).comp t₀ = t := by
  have hinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : NeZero k := ⟨hk⟩
  have hr : ∀ x, t x ∈ (Units.map f.toMonoidHom).range := fun x => by
    have h1 : ((t x : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ht]; rfl
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective f.injective).eq_pow_of_pow_eq_one h1
    exact ⟨(hζ.isUnit hk).unit ^ i, Units.ext (by simpa using hi)⟩
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (t.codRestrict _ hr), MonoidHom.ext fun x => ?_⟩
  exact MonoidHom.apply_ofInjective_symm hinj _

theorem exists_qkExt_of_b {V : Type} [CommRing V] [IsDomain V] {Q : DegPre V} (hB : Q.TauBimult) {K F : Type} [Field K]
    [Field F] [Algebra (FractionRing V) K] [Algebra (FractionRing V) F] (f : K →+* F)
    (hf : f.comp (algebraMap (FractionRing V) K) = algebraMap (FractionRing V) F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (p : QkPt Q F k) (hp : p.y = 0) (q : QkPt Q K k) (hq : q.y = 0)
    (hb : p.g.b.left = spMap f ≫ q.g.b.left) : ∃ p₀ : QkPt Q K k, QkExt f p₀ p := by
  have hb' : p.g.b = (gtExt Q f hf q.g).b := (Over.OverMorphism.ext hb).trans (gtExt_b f hf _).symm
  have np : k • p.g = 0 := by rw [qk_nsmul hB, hp, map_zero]
  have nq : k • q.g = 0 := by rw [qk_nsmul hB, hq, map_zero]
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := p.g + -(gtExt Q f hf q.g)) (by rw [add_b, neg_b, hb', mul_inv_cancel])
  have tk : t ^ k = 1 := by
    have : torusPt Q F (Additive.ofMul (t ^ k)) = torusPt Q F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← ht, nsmul_add, smul_neg, ← map_nsmul, np, nq, ofMul_one, map_zero, map_zero, neg_zero,
        add_zero]
    exact torusPt_injective this
  obtain ⟨t₀, rfl⟩ := exists_char_descend f hk hζ t tk
  have t0 : t₀ ^ k = 1 := MonoidHom.ext fun x => Units.map_injective (f := f.toMonoidHom) f.injective (by
    have := DFunLike.congr_fun tk x
    rw [MonoidHom.pow_apply, map_pow, MonoidHom.one_apply, map_one]
    exact this)
  refine ⟨qkMk hB 0 (q.g + torusPt Q K (Additive.ofMul t₀)) ?_, (qkExt_iff hB f hf _ _).2 (qk_ext hp ?_)⟩
  · simp only [nsmul_add, nq, ← map_nsmul, ← ofMul_pow, t0, ofMul_one, map_zero, zero_add]
  · show p.g = gtExt Q f hf (q.g + torusPt Q K (Additive.ofMul t₀))
    rw [map_add (f := _), GlobalTheory.QkNumberField.gtExt_torusPt, ← ht]
    abel

theorem exists_ptEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) (T : Over S') (b : T.left ⟶ S) (hb : b = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  refine ⟨MulEquiv.ofBijective (pushHom gp T) ⟨fun x y e => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (gp.1.lift y.left T.hom (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

theorem exists_etaA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B W : Type} [CommRing B] [CommRing W] {b : Geo.Tor.Base l B} {σ : B →+* W} (o : Obj D l b (spMap σ)) {F : Type} [Field F]
    [IsAlgClosed F] (j : W →+* F) (x : Over.mk (spMap j) ⟶ o.t.G) (hx : x ^ l.A = 1) :
    ∃ a, x.left = spMap j ≫ (o.etaA a).left := by
  obtain ⟨-, I, -, h, -⟩ := o.geom F (spMap j) (j.comp σ) (by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos x).1 hx
  refine ⟨a, ?_⟩
  rw [← ha, ← h]
  simp

theorem exists_qkExt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  intro E _ _ _ H D' l c L R _ _ _ _ t P iw I _ s ε e hε hs ⟨g, hD, hdiv⟩ p hp
  have hB := P.D.tau_bimult
  have hM : 0 < l.M' := (LowDat.lowLevel l).A_pos
  let K := FractionRing R
  let F := AlgebraicClosure K
  let j : L.W →+* F := (algebraMap K F).comp ((algebraMap R K).comp iw)
  have hj : spMap j = (TF (R := R) F).hom ≫ spMap iw := by
    show _ = (jFK (R := R) F ≫ jK R) ≫ spMap iw
    simp only [j, jFK, jK, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have gp : IsGrpPullback P.D.toPre.P.A L.D.P.A (spMap iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    pull_grp hD
  obtain ⟨ρ₁, h₁⟩ := exists_ptEquiv gp (TF (R := R) F) (spMap j) hj
  obtain ⟨ρ₂, h₂⟩ := exists_ptEquiv L.ab.1 (Over.mk (spMap j)) (spMap j) (Category.comp_id _).symm
  have hbk : p.g.b ^ l.M' = 1 := by rw [← nsmul_b, qk_nsmul hB, hp, map_zero, zero_b]
  obtain ⟨a, ha⟩ := exists_etaA L.o j (ρ₂.symm (ρ₁ p.g.b)) (by
    show _ ^ l.M' = 1
    rw [← map_pow, ← map_pow, hbk, map_one, map_one])
  obtain ⟨q, hq, hqb⟩ := GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate L P.D.toPre P.oD iw s ε e g hD hε hs hdiv a
  have hζ : IsPrimitiveRoot (⟨zeta l.M', c.zeta_mem⟩ : c.F) l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' hM.ne')
      Subtype.val_injective
  refine exists_qkExt_of_b hB (algebraMap K F) (RingHom.comp_id _) hM.ne'
    (hζ.map_of_injective ((algebraMap R K).comp (iw.comp L.b)).injective) p hp q hq ?_
  have e₂ := h₂ (ρ₂.symm (ρ₁ p.g.b))
  rw [ρ₂.apply_symm_apply, ha, h₁] at e₂
  refine gp.1.hom_ext (e₂.trans (Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (spMap (algebraMap K F) ≫ ·) hqb).trans ?_)))) ?_
  · rw [hj]
    show _ = (((spMap (algebraMap K F) ≫ jK R) ≫ _) ≫ _) ≫ _
    simp only [Category.assoc]
  · exact (Over.w p.g.b).trans ((Over.w (extMap (R := R) (algebraMap K F) (RingHom.comp_id _) ≫ q.g.b)).symm)

end GlobalTheory.DivTorsRat
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem ratHom_mem_of_isAlgClosed : ∀ (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → ∀ (g : F →+* K) (x : F), g x ∈ k₀ := by
  intro K _ k₀ hk₀ F hF g x
  haveI : CharZero K := (RingHom.charZero_iff g.injective).mp inferInstance
  haveI : CharZero k₀ := (RingHom.charZero_iff k₀.subtype.injective).mpr inferInstance
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℚ (g x) := by
    have := h1.algHom g.toRatAlgHom
    simpa using this
  have h3 : IsIntegral k₀ (g x) := (h2.extendScalars (algebraMap ℚ k₀).injective).isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h3)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (g x) hdeg
  rw [← hy]
  exact y.2

theorem pulledObj_descends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (π : o'.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) π ∧ LBIso o'.t.PP.L (M₀.pull π) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ _ ev k₀ hk₀ o' m₁ hB
  obtain ⟨B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', hab, hM, h1, h0, hw, hc⟩ := hB
  obtain ⟨θ, hθ, hLθ, hrel⟩ := GlobalTheory.T.pulledLowerObject_group_identification L Q oQ iw s ε e hDiv K ev o' m₁ B' π₁ h1
  obtain ⟨hpb, hL, hpts⟩ := GlobalTheory.T.pulledLowerObject_descends_with_points_subfield L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ B₀ M₀ c₀ B' π₁ π₀ w c' θ hab hM h1 h0 hw hc hθ hLθ hrel
  exact ⟨B₀, inferInstance, inferInstance, M₀, θ ≫ π₀, hab, hM, hpb, hL, fun y => by
    obtain ⟨x, hx1, hx2, x₀, hx₀⟩ := hpts y
    exact ⟨x, hx1, hx2, x₀, by rw [← Category.assoc] at hx₀ ⊢; simpa using hx₀⟩⟩

end GlobalTheory.UCanon.BaseDescent

theorem GlobalTheory.UCanon.base_value_mem_of_descended_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → ∀ a, ev (iw a) ∈ k₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ _ ev k₀ hk₀ hB a
  let f : L.W →+* K := ev.comp iw
  have hF : ∀ x : c.F, (f.comp L.b) x ∈ k₀ := GlobalTheory.UCanon.BaseDescent.ratHom_mem_of_isAlgClosed K k₀ hk₀ c.F c.fin (f.comp L.b)
  haveI : CharZero K := (RingHom.charZero_iff (f.comp L.b).injective).mp inferInstance
  obtain ⟨o', ⟨m₁⟩⟩ := (GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).1 (lowMap c L.b) L.o (spMap f)
    (lowMap c (f.comp L.b)) (by simp only [lowMap, spMap, ← Spec.map_comp]; rfl)
  obtain ⟨B₀, _, _, M₀, π, hab, hM, hpb, hL, hpts⟩ := GlobalTheory.UCanon.BaseDescent.pulledObj_descends L Q oQ iw s ε e hDiv K ev k₀ hk₀ o' m₁ hB
  choose x hx1 hx2 hx3 using hpts
  apply GlobalTheory.T.mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed' K k₀ hk₀
  intro σ hσ
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_objMap_fixing_descended_points_subfield K k₀ hk₀ o' B₀ M₀ π hab hM hpb hL σ hσ
  have hcomp : ∀ g' : Sp K ⟶ Sp L.W, g' = spMap (σ : K →+* K) ≫ spMap f →
      ∃ k : ObjMap o' L.o g', k.toSABMap.φ = n.toSABMap.φ ≫ m₁.toSABMap.φ := by
    rintro g' rfl
    exact ((GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := GlobalTheory.LowDat.lowLevel l)).2 _ _ _ L.o o' o' (spMap f) (spMap (σ : K →+* K)) m₁).1 n
  obtain ⟨m₂, hm₂⟩ := hcomp (spMap ((σ : K →+* K).comp f)) (by simp only [spMap, ← Spec.map_comp]; rfl)
  have key := L.fineRed K f ((σ : K →+* K).comp f)
    (by ext y; simp only [RingHom.comp_apply]; exact (hσ _ (hF y)).symm) o' m₁ m₂ x hx2
    (fun y => by
      rw [hm₂, Category.assoc, ← Category.assoc (x y), hn (x y) (hx1 y) (hx3 y), Category.assoc, hx2 y]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, f]) hx1
  have := congrArg (fun g : L.W →+* K => g a) key
  simpa [f] using this.symm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_finite_free_rank_le_of_prime (K : Type) [Field K] (l : ℕ) [Fact l.Prime]
    (hl : (l : K) ≠ 0) (A B : AbVar K) :
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  obtain ⟨hFA, hfA, hrA, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hFB, hfB, hrB, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  obtain ⟨Q, hpar, hpos, hdef⟩ := GlobalTheory.T.exists_posDef_quadraticForm_hom K A B
  have hrT : Module.finrank ℤ_[l] (Tl l A →ₗ[ℤ_[l]] Tl l B) = 4 * A.dim * B.dim := by
    rw [Module.finrank_linearMap, hrA, hrB]; ring
  refine GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank (A ⟶ B) Q hpar hpos hdef (4 * A.dim * B.dim) ?_
  intro n u hu
  rw [← hrT]
  refine GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form l (A ⟶ B) (Tl l A →ₗ[ℤ_[l]] Tl l B) Q hpar hpos hdef (tmap l A B) ?_ n u hu
  intro f φ hφ
  exact GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul K l hl A B f φ hφ

theorem hom_finite_free_rank_le : ∀ (K : Type) [Field K] (A B : AbVar K),
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  intro K _ A B
  by_cases h2 : ((2 : ℕ) : K) = 0
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ((3 : ℕ) : K) ≠ 0 := by
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add]; exact one_ne_zero
    exact hom_finite_free_rank_le_of_prime K 3 h3 A B
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hom_finite_free_rank_le_of_prime K 2 h2 A B

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem chernInt_eq_topSelf_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ n u hu
  have hL : L.IsLB := φ.isLB
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField ℂ Y.X Y.str L hL Y.dim (Var.topologicalKrullDim_eq Y).le n u hu
  have hπ : ProjSpace.toProj Y.str s hs ≫ PSpace.str ℂ Y.dim = Y.str := ProjSpace.toProj_str Y.str s hs
  have e := GlobalTheory.ProjSpace.lbIso_pull_O1_toProj_of_isLB ℂ Y.dim Y.X L hL Y.str s hs
  have h1 := GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso Y _ L (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull _ hπ) φ e
    (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)).pull _ hπ) hφ
  rw [← h1, GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf Y _ hπ,
    topSelf_congr ℂ (LB.isLB_pull (ProjSpace.O1_isLB ℂ Y.dim) (ProjSpace.toProj Y.str s hs)) hL e]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.kodaira_spencer_iso_flag_tangent : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  first | exact @GlobalTheory.FlagTan.ksIso_psiSet | exact GlobalTheory.FlagTan.ksIso_psiSet | (intros; apply GlobalTheory.FlagTan.ksIso_psiSet <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closedFibreLift_comm_translation_section_ratios : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  first | exact @GlobalTheory.HeatRatioW.dl_comm_transl_ratio | exact GlobalTheory.HeatRatioW.dl_comm_transl_ratio | (intros; apply GlobalTheory.HeatRatioW.dl_comm_transl_ratio <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_symbolZero_eq_connection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ (κ : ℕ → (DualNumber k)ˣ) (ℓ : ℕ → P.D.toPre.X →+ k), ∀ (e : ℕ), 1 ≤ e → ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) → ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val = gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom ((κ e).val * (1 + TrivSqZeroExt.inr (ℓ e α)))) * (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  first | exact @GlobalTheory.HeatUConn.uconn | exact GlobalTheory.HeatUConn.uconn | (intros; apply GlobalTheory.HeatUConn.uconn <;> assumption)
end
