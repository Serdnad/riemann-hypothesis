module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPullByEndOfPullRel
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle508
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle524
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle514
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.RegSum

def secSum {X : Scheme.{0}} {N : LB X} {n : ℕ} (F : Fin n → LB.Sec N) : LB.Sec N :=
  ⟨fun j => ∑ i, (F i).f j, fun a b => by

    simp only [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (F i).compat a b⟩

theorem sval_sum {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {a : LB.Sec (LB.LinComb L φ ε)} {F : Fin n → LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, a.f j = ∑ i, (F i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval a r z J = ∑ i, sval (F i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem zCast_sum {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {a b : ℤ} (e : a = b) {n : ℕ}
    {t : LB.Sec (LPow A L a T)} {F : Fin n → LB.Sec (LPow A L a T)} (h : ∀ j, t.f j = ∑ i, (F i).f j) (j) :
    (PullbackSections.zCast A e t).f j = ∑ i, (PullbackSections.zCast A e (F i)).f j := by
  subst e
  exact h j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem reg_sum (I : IntData Xo c T io y.1) (M : ℕ) {n : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    {F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    (h : ∀ j, t.f j = ∑ i, (F i).f j) (hF : ∀ i, Reg I M (F i)) : Reg I M t := by
  choose σ σt h1 h2 using hF
  refine ⟨secSum σ, secSum σt, fun Z r zp e1 e2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · refine (sval_sum (zCast_sum _ _ h) zp z hJ).trans ?_
    rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h1 i Z r zp e1 e2 z J J' hJ hJ'
  · rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ',
      sval_sum (a := secSum σ) (F := σ) (fun _ => rfl) _ z hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h2 i Z r z J J' hJ hJ'

theorem reg_of_isTransl (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y))))
    (P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G) (hP : P.TorsionIso) (hM : IsUnit (M : T.V))
    (hF : letI := io.toAlgebra; IsTransl M y.1.s F) : Reg I M F := by
  let _ := io.toAlgebra
  obtain ⟨a, hVt⟩ := hF
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := PullbackSections.thetaTie _ _ _ _ _ _ T io y.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := PullbackSections.VtMove.vtMoveSt _ _ _ _ _ y.1.x I.t' I.m1 I.w1 I.rig1 M _ y.1.s _ F hVt
    (fun u hu => hu) θK hθ1
  obtain ⟨σ, hσ⟩ := PullbackSections.regUnif_of' PullbackSections.thetaNu GlobalTheory.EndPullNu.main.2 GlobalTheory.FiniteLiftNu.finNu _ _ T.V I.G P hP θ hθ M hM
    I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := PullbackSections.exists_restrict I.t' _ (PullbackSections.zCast I.t'.G (PullbackSections.natCast_sq M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ PullbackSections.gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp T.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, PullbackSections.gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ PullbackSections.gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ PullbackSections.gsec I.t'.G) (hg r) z J J' hJ hJ'

theorem reg_of_isTranslSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  intro E _ _ _ H Dw l Xo c T io y I M t ⟨P, hP⟩ hM ⟨n, F, hF, h⟩
  exact reg_sum I M h fun i => reg_of_isTransl I M (F i) P hP hM (hF i)

end GlobalTheory.HkIntegral.RegSum
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem spMap_epsMul_comp (a b : ℂ) {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) :
    spMap (epsMul a) ≫ spMap (epsMul b) ≫ v = spMap (epsMul (b * a)) ≫ v := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro x
  ext <;> simp [epsMul] <;> ring

theorem exists_lift_deriv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') {p : ℕ} (hp : p.Prime)
    {y y'' : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy'' : y'' = F.u j P') (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hI : IsHkIsog p y y'' C ψ ψp) :
    ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hy hy''
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  refine ⟨gam, h, h1, h2, h3, fun w v hvs hd => ?_⟩
  have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
    pullback.lift_fst _ _ _
  have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
    refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
      (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
    · convert ExpChain.isHolTo_ex F i P hP using 2 with z
      exact hfst z
    · convert hd using 2 with z
      exact hfst z
  have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
  have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left := fun z => by
    rw [← Category.assoc, hI.2.2.1, h4]
    exact pullback.lift_fst _ _ _
  simp only [e1] at d1
  exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1



theorem exists_similitude_tri_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU P p i k k' x x' C z t hA hK hH hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hP, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hP', per', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hH
  have hpp : p.Prime := hA.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ m, h.toLinearMap (Pi.single (e.symm ⟨τ, m⟩) 1) =
      (∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ m
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ m
    have d2 := hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ m)
      (z.u τ m)).1 (hPx' ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
      have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
        apply RingHom.ext
        intro a
        ext <;> simp [epsMul]
      rw [e0]
      first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, m⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ m hm v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨m, hm⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * Formalism.L2.PjFree.toC (cf τ i j)) hcol (Pm v) τ ⟨m, hm⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dite_eq_left ⟨hm, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeEx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTransLat

open Matrix

variable {D : D7}

theorem AA_le_Iid (a : D.host.E) (ha : a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    a ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  have ha' : a ∈ D.host.ccE * D.host.AA0 := by rw [← Host.AA]; exact ha
  refine FractionalIdeal.mul_induction_on ha' (fun x hx y hy => ?_) (fun x y hx hy => add_mem hx hy)
  rw [Host.ccE] at hx
  obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
  | zero => simp
  | add u w _ _ hu hw => rw [map_add (f := _), add_mul]; exact add_mem hu hw
  | smul o u _ hu =>
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact Submodule.smul_mem _ o hu

theorem coord_genMap {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (a : D.host.E) (s' : Fin S.rank → D.host.E) (t' : Fin T.rank → D.host.E) :
    (frT⁻¹).1 * GlobalTheory.LatVac.genMap S T a (frS.1 *ᵥ s') (frT.1 *ᵥ t') * frS.1 = a • Matrix.vecMulVec t' (star s') := by
  have hS' : frS.1ᴴ * S.gram * frS.1 = 1 := hS
  have e : ∀ (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E),
      GlobalTheory.LatVac.genMap S T a s t = a • Matrix.vecMulVec t (star s ᵥ* S.gram) := by
    intro s t
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.vecMul,
      dotProduct, smul_eq_mul, Pi.star_apply, mul_assoc]
  rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_mulVec,
    Units.inv_mul, Matrix.one_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hS',
    Matrix.vecMul_one]

theorem vecMulVec_mem_homL {N N' : ℕ} {Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D Ls) {s' : Fin N → D.host.E} (hs' : s' ∈ Ls)
    {t' : Fin N' → D.host.E} (ht' : t' ∈ Lt) : Matrix.vecMulVec t' (star s') ∈ homL D Ls Lt := by
  refine GlobalTheory.ThetaLatImage.mem_homL.2 fun x hx => ?_
  obtain ⟨o, ho⟩ := (((GlobalTheory.InertSign.sd_iff D Ls).1 hLs).2.2 x).1 hx s' hs'
  have e : Matrix.vecMulVec t' (star s') *ᵥ x = o • t' := by
    funext i
    rw [Pi.smul_apply, ← algebraMap_smul D.host.E o (t' i), ho, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, GlobalTheory.InertSign.hE, Pi.star_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [bridge_star_holds D.R D.host]; ring
  rw [e]
  exact Lt.smul_mem o ht'

theorem coord_mem_RL {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    {Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLs : SD D Ls) {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hw : w ∈ GlobalTheory.LatVac.latRat S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt)) :
    (frT⁻¹).1 * w * frS.1 ∈ GlobalTheory.InertSign.RL D D.host.ccK Ls Lt := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, ⟨s', hs', rfl⟩, t, ⟨t', ht', rfl⟩, rfl⟩ := hw
    rw [coord_genMap frS frT hS]
    exact Submodule.subset_span ⟨a, AA_le_Iid a ha, _, vecMulVec_mem_homL hLs hs' ht', rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

theorem mem_La_of_finRat : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), SD D Ls → SD D Lt → ∀ (δ : ℂ) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), GlobalTheory.VacUnique.finRat S T v ∈ latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) → δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D S T frS frT hS hT Ls Lt hLs hLt δ v hv
  obtain ⟨ΛS, hΛS, hSD⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTD⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice T frT hT Lt hLt
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  rw [← hΛS, ← hΛT] at hv
  have hrat := (GlobalTheory.AdForm.RatLat.finTens_mem_iff hψ hSD hTD v).1 hv
  rw [hΛS, hΛT] at hrat
  have hpt := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (coord_mem_RL frS frT hS hLs hrat) 1
  rw [one_smul] at hpt
  convert hpt using 1
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  have hi : (GlobalTheory.FockPos.frAt frT τ)⁻¹ = (frT⁻¹).1.map (tauE D τ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv' : Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) = v.map (tauE D τ) := rfl
  show δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b = _
  rw [hi, hv', GlobalTheory.FockPos.frAt, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end GlobalTheory.MovedTransLat
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowStart

theorem setIntegral_fd_eq {D : D7} (V : HSp D) (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA D V))
    (h1 : IsFundamentalDomain (GQ V) 𝓕 μ) (h2 : IsFundamentalDomain (GQ V) 𝓕' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : ∫ g in 𝓕, f g ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI := hμ
  exact h1.setIntegral_eq h2 fun γ g => by
    simp only [Subgroup.smul_def, smul_eq_mul]
    exact hf γ γ.2 g

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem IsCuspListed.left {θ : InfFam D} {X : Node} {F : Fn G X} (h : IsCuspListed θ X F) :
    ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g := h.1.toIsAutFun.left

theorem measEq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation

theorem kerA_right_rat (W : G.Weil) {i : ℕ} (hi : i < D.R.m) {f : Sch G (.right i 0)}
    (hf : IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) f) :
    ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g h, W.kerA (.right i 0) f (γ * g) h = W.kerA (.right i 0) f g h := by
  intro γ hγ g h
  have H := (GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ (W.om (.chi i 0))
    (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩) f hf).2 1 (Subgroup.one_mem _) γ hγ (negGA _ h) g
  rw [one_mul] at H
  exact H

theorem liftA_right_eq (W : G.Weil) (M M' : Vol G) {i : ℕ} {K : Subgroup (GL (Fin (G.V (.grid i 0)).rank) (Lev.EAf D))}
    (h : M.IsAt (.grid i 0) K) (h' : M'.IsAt (.grid i 0) K) (f : Sch G (.right i 0)) (F : Fn G (.grid i 0))
    (hinv : ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g x, W.kerA (.right i 0) f (γ * g) x * F (γ * g) = W.kerA (.right i 0) f g x * F g) :
    liftA W M (.right i 0) f F = liftA W M' (.right i 0) f F := by
  funext x
  have e := measEq M M' _ _ h h'
  rw [liftA_apply, liftA_apply]
  have h1 := h.haar_fund
  have h2 := h'.haar_fund
  simp only [Arrow.src] at h1 h2 e ⊢
  rw [e] at h1 ⊢
  exact setIntegral_fd_eq _ _ h2.1 _ _ h1.2 h2.2 _ fun γ hγ g => hinv γ hγ g x

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowCore (W : G.Weil) (M₀ M : Vol G) (ρm : RealMatch W) (t : T) (ρ : G.RealVec) (Φ : G.Datum)
    (hstep : CuspStep W M ρm t)
    (hloc : ∀ (i : Fin D.R.m) (κ : G.CosAt i), ∃ e, IsIdemSum e (locPl G t) ∧
      ∃ φ, IsLocVec W (.chi (i : ℕ) 0) e (W.vac i) φ (W.cosVec i κ))
    (hth : ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i))
    (h₀ : M₀.IsRow) (h₁ : M.IsRow) (u : Fn G (.grid 0 0)) (hu : IsCuspListed W.θ (.grid 0 0) u) :
    ∀ n (hn : n ≤ D.R.m), PathConv W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u ∧
      IsCuspListed W.θ (.grid n 0) (liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u) ∧
      liftP W M₀ (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u =
        liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨trivial, hu, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc, e⟩ := ih (by omega)
    set F := liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u with hF
    let k : Fin D.R.m := ⟨n, by omega⟩
    obtain ⟨e', he', φ, hφ⟩ := hloc k (Φ k)
    have hv : IsLocVec W (Arrow.right n 0 : Arrow T).pair e' (vacOf ρm (.right n 0)) φ (W.cosVec n (Φ k)) := by
      show IsLocVec W (.chi n 0) e' (ρm.vX n 0) φ (W.cosVec n (Φ k))
      rw [ρm.vX_row n]; exact hφ
    obtain ⟨hconv, hcusp⟩ := hstep (.right n 0) (Or.inl ⟨n, 0, by omega, Nat.zero_le _, rfl⟩) e' he' φ _ hv (ρ k) F hc
    refine ⟨⟨c, hconv⟩, hcusp, ?_⟩
    show liftA W M₀ (.right n 0) (W.datum ρ Φ k) (liftP W M₀ (rowPath T 0 n)
        (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u) = liftA W M (.right n 0) (W.datum ρ Φ k) F
    rw [e]
    refine liftA_right_eq W M₀ M (h₀.row n (by omega)) (h₁.row n (by omega)) _ F fun γ hγ g x => ?_
    rw [kerA_right_rat W (by omega) (hth k) γ hγ g x, IsCuspListed.left hc γ hγ g]

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

end GlobalTheory.RowStart
end
end
