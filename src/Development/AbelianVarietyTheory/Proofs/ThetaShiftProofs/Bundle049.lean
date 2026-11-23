module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFour
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle124
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LevelPointsOfArcEqPeriodDivLevel
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.IntLetterCoord

open Matrix GlobalTheory.BasisUniv

theorem mem_range_of_comb {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] {I : Type} {g m : ℕ} (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    (z : Fin g → A) (y : Fin m → K) (hz : (fun j => algebraMap A K (z j)) = ∑ k, y k • fun j => algebraMap A K (U k j))
    (k : Fin m) : y k ∈ Set.range (algebraMap A K) := by
  have hK : ∀ i, (fun j => algebraMap A K (z j)) ᵥ* (M i).map (algebraMap A K) =
      algebraMap A K (ρ i) • fun j => algebraMap A K (z j) := fun i => by
    have e : ∀ k, (fun j => algebraMap A K (U k j)) ᵥ* (M i).map (algebraMap A K) =
        algebraMap A K (ρ i) • fun j => algebraMap A K (U k j) := fun k => by
      funext j
      have := congrArg (algebraMap A K) (congrFun (hU k i) j)
      simpa [Matrix.vecMul, dotProduct] using this
    rw [hz, Matrix.sum_vecMul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_vecMul, e, smul_comm]
  have hA : ∀ i, z ᵥ* (M i).map (RingHom.id A) = RingHom.id A (ρ i) • z := fun i => by
    funext j
    apply IsFractionRing.injective A K
    have := congrFun (hK i) j
    simpa [Matrix.vecMul, dotProduct] using this
  have hfl : (algebraMap A K).Flat :=
    RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors A))
  obtain ⟨cf, hcf, -⟩ := eig_powerSeries M ρ U hU h (RingHom.id A) (RingHom.Flat.id A) z hA
  have := (eig_powerSeries M ρ U hU h (algebraMap A K) hfl _ hK).unique (y₂ := fun k => algebraMap A K (cf k)) hz (by
    funext j
    have := congrArg (algebraMap A K) (congrFun hcf j)
    simpa [Finset.sum_apply, Algebra.smul_def] using this)
  exact ⟨cf k, (congrFun this k).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem mem_range_of_letBC (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {b : O →+* A} {b' : O →+* K}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β K b'}
    {p : Out.IsPullDeg (algebraMap A K) a.D₀ a'.D₀} (hp : InBC (algebraMap A K) a a' p)
    {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (hB : ArcBasis W ρ e) (τ : E →+* ℂ) {e₁ : Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR K)}
    (he : ∀ k, LetBC p (e τ k) (e₁ k)) {ν : Out.GtPt a.D₀ (epsR A)} {ν₁ e₂ : Out.GtPt a'.D₀ (epsR K)}
    (hν : GtTanR ν) (hν₁ : LetBC p ν ν₁) {y : Fin (Dw.mult τ) → K} (h₂ : GtComb y e₁ e₂) {x : K}
    (hx : GtComb ![x] ![e₂] ν₁) (k : Fin (Dw.mult τ)) : x * y k ∈ Set.range (algebraMap A K) := by
  have hG := hL.globalFns
  have hf : Function.Injective (algebraMap A K) := IsFractionRing.injective _ _
  obtain ⟨hW, -⟩ := (GlobalTheory.ArcQBC.baseChanges hL hL₂ hU hL₅ E H Dw l Xo c O β Y A K b a _ hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.ArcBaseChange.main hL hL₂ E H Dw l Xo c O β Y A b a χ W K b' a' _ p W' hp hW'
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, s, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
  have ex := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have ex' := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y K b' a' _ W'
  have lin := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y A b a χ W
  have lin' := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y K b' a' _ W'
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  obtain ⟨n, j, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', j', hy'⟩ := exists_chart_of_pullback _ m.cart
  choose v' hv' using fun j => exists_lift _ m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange _ m.cart hv hv'
  have coord : ∀ ξ ξ' w, GtTanR ξ → LieImg W ξ w → LetBC p ξ ξ' → ∃ (z : Fin g → A) (w' : epsR (PowerSeries K) ⟶ W'.t.G),
      IsLieComb (fun j => PowerSeries.C (R := A) (z j)) v w ∧ LieImg W' ξ' w' ∧
      IsLieComb (fun j => PowerSeries.C (R := K) (algebraMap A K (z j))) v' w' := fun ξ ξ' w ht hw hξ => by
    obtain ⟨z, hz, -⟩ := hcomb _ ht
    have h1 := (lin g z s ξ v w (fun i => (hev i).2) hz).1 hw
    obtain ⟨w', hw'⟩ := exists_lift _ m.cart w
    refine ⟨z, w', h1, hm _ _ w w' hξ hw hw', ?_⟩
    simpa only [PowerSeries.map_C] using Chart.comb_baseChange _ m.cart h1 hv' hw'
  choose U u hU₀ hu hU' using fun k => coord _ _ _ (((ex (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1) (hv₀ τ k) (he k)
  obtain ⟨w, hw⟩ := (ex ν).1.exists
  obtain ⟨z, w', -, hw', hz'⟩ := coord _ _ _ hν hw hν₁
  obtain ⟨w₂, hw₂⟩ := (ex' e₂).1.exists
  have c₂ := (lin' _ y e₁ e₂ u w₂ hu h₂).1 hw₂
  have c₁ := (lin' _ ![x] ![e₂] ν₁ (fun _ => w₂) w' (fun i => by fin_cases i; exact hw₂) hx).1 hw'
  have d₂ : IsLieComb (∑ k, PowerSeries.C (R := K) (y k) • fun j => PowerSeries.C (R := K) (algebraMap A K (U k j)))
      v' w₂ := by
    have hc := (Chart.isLieComb_iff (∑ k, PowerSeries.C (R := K) (y k) •
      fun j => PowerSeries.C (R := K) (algebraMap A K (U k j))) v' _).2 rfl
    have := (comb_iff hy' hb' hU' hc _).2 rfl
    rwa [((Chart.isLieComb_iff _ _ _).1 this).trans ((Chart.isLieComb_iff _ _ _).1 c₂).symm] at hc
  have d₁ := (comb_iff hy' hb' (u := fun _ : Fin 1 => w₂) (fun _ => d₂) hz' _).1 c₁
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ k x, U k ᵥ* M x = ρ τ x • U k := fun k x => by
    have := (eig_iff hy hv _ (hMR x) (hU₀ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine mem_range_of_comb M (fun x => ρ τ x) U hUe (fun s hs => ?_) z (fun k => x * y k) ?_ k
  · have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU₀ hc] using this
  · funext i
    have := congrArg (PowerSeries.constantCoeff (R := K)) (congrFun d₁ i)
    simpa [Finset.sum_apply, Finset.mul_sum, _root_.mul_assoc] using this

theorem main : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (Yw : Model Xo c (c.V Wl).subtype), Yw.N4 → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (x : Tv.Fr), (∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![x] ![e₂] ν₁) → ∀ m, x * M.g τ k m ∈ Set.range (algebraMap Tv.V Tv.Fr) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl M Yw hN hB τ k x ⟨ν, ν₁, e₂, hν, hν₁, he₂, hx⟩ m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨e₁, e₂', l₁, l₂, -, hg⟩ := M.e_tie
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK := ⟨rfl, M.bcK.2⟩
  obtain ⟨-, x₂, -⟩ :=
    (GlobalTheory.ArcQBC.baseChanges hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _
      (d.a.restrict (c.V d.Wp).subtype) io io.injective _ hK'.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK hK'
  obtain rfl : e₂ = e₂' τ k := (x₂ (d.e τ k)).unique he₂ (l₂ τ k)
  exact mem_range_of_letBC hK.laws hK.laws2 hK.ubc hK.laws5 M.bcw W₀ (hB χ₀ W₀) τ (l₁ τ) hν hν₁ (hg τ k) hx m

end GlobalTheory.IntLetterCoord
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.hasSum_thetaGenerator_chart_ratio : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (φ : p.R →ₐ[c.F] ℂ⸨X⸩) (y₁ : FrPt Xo c ℂ⸨X⸩) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → OpenChart j y₀ → FrMap φ y₀ y₁ → FrChg G s y₁ y → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ yw : FrPt Xo c (CAt σ)) (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ), (∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (_root_.Formalism.L2.PjFree.toC (ψ f))) → FrMap ψ y₀ yw₁ → yw.x = Fu.u Ha.i (Ha.Pw w) → AnGen Fu Ha.i (Ha.Pw w) yw (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ → FrChg Gw sw yw₁ yw → HasSum (fun m : ℤ => (s).coeff m * eTwoPi w ^ m) (_root_.Formalism.L2.PjFree.toC sw) := by
  first | exact @GlobalTheory.ArcQ.hasSum_generator_ratio | exact GlobalTheory.ArcQ.hasSum_generator_ratio | (intros; apply GlobalTheory.ArcQ.hasSum_generator_ratio <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ GlobalTheory.ArcCM.RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  first | exact @GlobalTheory.ArcCM.Room.room_four | exact GlobalTheory.ArcCM.Room.room_four | (intros; apply GlobalTheory.ArcCM.Room.room_four <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_thetaOf_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  first | exact @GlobalTheory.existsUnique_thetaOf | exact GlobalTheory.existsUnique_thetaOf | (intros; apply GlobalTheory.existsUnique_thetaOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.tangentVectors_thetaSection_arcWitness_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A']
      (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A')
      (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)),
      InBC f a a' p → WitBC f p W W' →
        ∃ m : SABMap W'.t W.t (spMap (PowerSeries.map f)),
          W'.m.φ = m.φ ≫ W.m.φ ∧
          (∀ ν ν' v (v' : epsR (PowerSeries A') ⟶ W'.t.G),
            GlobalTheory.ArcQ.LetBC p ν ν' → LieImg W ν v →
              v'.left ≫ m.φ = spMap (Formalism.L2.Pj.dualMap (PowerSeries.map f)) ≫ v.left →
              LieImg W' ν' v') ∧
          ∀ (w : LB.Iso W'.t.PP.L (W.t.PP.L.pull m.φ)) th th' θ (θ' : LB.Sec W'.t.PP.L) θ₂,
            RigIso m w → ThBC p th th' → ThetaOf W th θ → PullSec m.φ θ θ₂ →
              IsoMaps w θ' θ₂ → ThetaOf W' th' θ' :=
  @GlobalTheory.ArcBaseChange.main
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  first | exact @GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres | exact GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres | (intros; apply GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem exists_cmObj_baseChange : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (K₂ : Type) [Field K₂] [NumberField K₂] (i : K →+* K₂) (σ₂ : K₂ →+* ℂ), σ₂.comp i = σ₁ → ∃ (ρ₂ : 𝓞 K₂) (X₂ : GlobalTheory.CM.CMObj H K₂ ρ₂ σ₂ p q) (_ : SABMap X₂.B.t X.B.t (spMap (RingOfIntegers.mapRingHom i))), (ρ₂ : K₂) = i (ρ : K) ∧ X₂.hh = X.hh := by
  intro _ E _ _ _ H K _ _ ρ σ₁ p q X K₂ _ _ i σ₂ h
  have extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ}
      (X : GlobalTheory.CM.CMObj H K ρ σ p q) (j : K →+* K₂) (σ' : K₂ →+* ℂ)
      (h : σ'.comp j = σ) :
      ∃ (X' : GlobalTheory.CM.CMObj H K₂ (RingOfIntegers.mapRingHom j ρ) σ' p q)
        (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
        (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
        X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := open GlobalTheory.CM GlobalTheory.CMExistsCompare in by
    set f := RingOfIntegers.mapRingHom j with hf
    have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
    choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
    obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
    have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
    choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
    have hpt := spMap_int j h
    refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K₂ j X.split |>.1
              ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
              A := A', B := B'
              typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
              typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
              typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
              hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
    · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
      have e := congrArg Over.Hom.left ((X.lin i).2 c)
      simp only [Over.comp_left] at e
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
        (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
    · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
      choose pA hA using fun b => exists_ptEquiv (a b) hpt
      obtain ⟨x, hx⟩ := X.onto (pB y)
      refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
      rw [hx, map_list_prod, List.map_ofFn]
      congr 2
      funext i
      apply Over.OverMorphism.ext
      simp only [Function.comp_apply]
      rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
      erw [hφ]
      rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
    · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
        (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
        ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
      rw [hpt]
      exact X.weil i
  obtain ⟨X₂, -, mb, hh, -⟩ := extend X i σ₂ h
  exact ⟨_, X₂, mb, rfl, hh⟩

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.PeriodObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)}

theorem mem_lat_iff (hP : IsPeriod D ty P) (ρ : ℂ) (a : D.La) :
    a ∈ PureType.lat hP ρ ↔ P (H.rt • a) = ρ • P a := by
  refine ⟨fun h => funext fun j => ?_, fun h j hj => ?_⟩
  · rw [hP.1, Pi.smul_apply, smul_eq_mul]
    by_cases hj : ty j (H.rt : E) = ρ
    · rw [hj]
    · rw [h j hj, mul_zero, mul_zero]
  · have := congrFun h j
    rw [hP.1, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hj

theorem exists_lat_move (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (gam : D.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {p q : ℕ} (Z : GlobalTheory.CM.CMLat hP p q) :
    ∃ Z' : GlobalTheory.CM.CMLat hP' p q, Z'.hh = Z.hh :=
  ⟨{ D₁ := Z.D₁
     sigP := Z.sigP
     sigM := Z.sigM
     f := fun j => gam.toLinearMap ∘ₗ Z.f j
     pure := fun j a => by
       refine (mem_lat_iff hP' _ _).2 ?_
       show P' (H.rt • gam (Z.f j a)) = _ • P' (gam (Z.f j a))
       rw [← map_smul, hh, hh, (mem_lat_iff hP _ _).1 (Z.pure j a), map_smul]
     hh := Z.hh
     form := fun j a b => (hE _ _).trans (Z.form j a b)
     span := by
       obtain ⟨n, hn, hs⟩ := Z.span
       refine ⟨n, hn, fun a => ?_⟩
       obtain ⟨x, hx⟩ := hs (gam.symm a)
       refine ⟨x, ?_⟩
       have := congrArg gam hx

       rw [map_nsmul, gam.apply_symm_apply, map_sum] at this
       exact this }, rfl⟩

theorem isExp_move {R : Type} [CommRing R] {T : GlobalTheory.CM.PAT H (Sp R)} {σ : R →+* ℂ} (hP : IsPeriod D ty P)
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)}
    (he : GlobalTheory.CM.IsExp T σ D' ty P' e) : GlobalTheory.CM.IsExp T σ D ty P fun z => e (h z) := by
  obtain ⟨hP', hol, add, onto, ker, lin, weil⟩ := he
  have hd : Differentiable ℂ h := h.toContinuousLinearEquiv.differentiable
  refine ⟨hP, fun U f => ⟨?_, ?_⟩, fun z w => ?_, onto.comp h.surjective, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · exact (hol U f).1.preimage hd.continuous
  · exact (hol U f).2.comp hd.differentiableOn fun z hz => hz
  · beta_reduce
    rw [map_add (f := _), add]
  · refine (ker _).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      exact ⟨gam.symm a, h.injective (by rw [← hh, gam.apply_symm_apply, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, hh a⟩
  · let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (a : E) * z k := fun _ => rfl
    have hc : h.toLinearMap.restrictScalars ℝ ∘ₗ m = m ∘ₗ h.toLinearMap.restrictScalars ℝ :=
      LinearMap.ext_on_range hP.2.2.2.1 fun x => by
        show h (m (P x)) = m (h (P x))
        rw [← hh, hm, hm, ← funext (hP.1 a x), ← funext (hP'.1 a (gam x)), ← hh, map_smul]
    have hz : h (m z) = m (h z) := LinearMap.congr_fun hc z
    show e (h (m z)) = _
    rw [hz, hm, lin]
  · beta_reduce
    rw [map_smul, map_smul, ← hh, ← hh]
    exact weil k _ _ c hk (by rw [hE]; exact hc)

end GlobalTheory.ArcCM.PeriodObj

namespace GlobalTheory.ArcCM

theorem exists_cmObj_of_period : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)) (hP : IsPeriod DB ty PB) (Z : GlobalTheory.CM.CMLat hP DB.p DB.q), 1 ≤ DB.p + DB.q → IsTypeFn H DB.p DB.q ty → l.A = 1 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (σ₁ : K →+* ℂ) (ρ : 𝓞 K) (X : GlobalTheory.CM.CMObj H K ρ σ₁ DB.p DB.q) (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)), σ₁.comp (algebraMap c.F K) = c.F.val.toRingHom ∧ σ₁ (ρ : K) = H.rt0 ∧ X.hh = Z.hh ∧ GlobalTheory.CM.IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) DB ty PB ex := by
  intro kn E _ _ _ H l c DB g ty PB hP Z hpq hty hA
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  obtain ⟨FU⟩ := kn.n1c E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, he⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq
    rfl hty DB LinearMap.id PB ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨i, P', hP', hy⟩ := FU.onto y he.1
  obtain ⟨gam, h, hE, -, -, hh⟩ := (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed kn.theta kn.laws E H DB l Xo
    (algebraMap (KA l) ℂ) g ty hpq rfl hty DB (FU.Di i) LinearMap.id (FU.t i) PB P' y (FU.u i P') e (FU.ex i P') he
    ⟨FU.over_σ i P' hP', hP', ⟨FU.ex_add i P' hP', FU.ex_onto i P' hP', ExpUniqFamily.isHolTo_ex FU i P' hP',
      (FU.ex_diff i P' hP').1, (FU.ex_diff i P' hP').2⟩, FU.ex_ker i P' hP', FU.ex_lin i P' hP', FU.ex_weil i P' hP',
      FU.ex_eta i P' hP', FU.ex_etaA i P' hP'⟩).1 hy.symm
  obtain ⟨Z', hZ'⟩ := PeriodObj.exists_lat_move hP hP' gam h hE hh Z
  obtain ⟨K, _, hk, ρ, X, y₀, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hX, -, hy₀, -⟩ :=
    kn.cm E H DB l Xo g ty FU i P' hP' Z' c.F c.fin
  obtain ⟨eB, heB, -⟩ := GlobalTheory.CM.ExCompare.exists_isExp_of_family FU i hP' (algebraMap (𝓞 K) K) (algebraMap K ℂ)
    X.B m m' hy₀
  exact ⟨K, inferInstance, inferInstance, (IntermediateField.inclusion hle).toRingHom.toAlgebra, algebraMap K ℂ, ρ, X,
    fun z => eB (h z), RingHom.ext fun _ => rfl, hρ, hX.trans hZ', PeriodObj.isExp_move hP gam h hE hh heB⟩

end GlobalTheory.ArcCM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.levelPoints_of_arc_eq_period_div_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c) (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (la : Λ.A.La) (p : Over.mk gen ⟶ W.t.G), Ξ.IsGen Φ → yF ≫ Y.j = gen ≫ χ → ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨ (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v)) → Λ.Rep k p₀ la → p.left ≫ W.m.φ = yF ≫ ξ.left ≫ Y.m.φ → Φ.LevelPt k p la := by
  first | exact @GlobalTheory.levelPt_of_rep | exact GlobalTheory.levelPt_of_rep | (intros; apply GlobalTheory.levelPt_of_rep <;> assumption)
end
