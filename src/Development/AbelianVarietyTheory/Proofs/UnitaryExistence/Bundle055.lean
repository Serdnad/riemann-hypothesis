module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle051
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle053
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.nonempty_thetaData_flagDomainModels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, Nonempty (ThetaData e F M k) := by
  first | exact @GlobalTheory.FrameUnif.nonempty_thetaData | exact GlobalTheory.FrameUnif.nonempty_thetaData | (intros; apply GlobalTheory.FrameUnif.nonempty_thetaData <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.flagDomainModels_exponents_levelM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  first | exact @GlobalTheory.ExpoModels.expoMatch_models | exact GlobalTheory.ExpoModels.expoMatch_models | (intros; apply GlobalTheory.ExpoModels.expoMatch_models <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_splitLattice_datum_every_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  first | exact @GlobalTheory.CompRat.exists_splitLat_of_signature | exact GlobalTheory.CompRat.exists_splitLat_of_signature | (intros; apply GlobalTheory.CompRat.exists_splitLat_of_signature <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.SecSeparation

theorem exists_frBor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (t : Ix Dw → Sˣ) : ∃ y' : FrPt Xo c S, FrBor t y y' := by
  classical
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y
    (fun τ => Matrix.diagonal fun i => (t (some ⟨τ, i⟩) : S)) (t none) (fun τ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 fun i => Units.isUnit _)
  refine ⟨y', ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨_, ?_, ?_, hy'⟩⟩
  · intro τ i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne
  · intro τ i
    exact Matrix.diagonal_apply_eq _ _

end GlobalTheory.SecSeparation

namespace GlobalTheory

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frame_eq_of_baseChange_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  first | exact @GlobalTheory.Frames.frPt_eq_of_frMap_injective | exact GlobalTheory.Frames.frPt_eq_of_frMap_injective | (intros; apply GlobalTheory.Frames.frPt_eq_of_frMap_injective <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

variable [Fintype (Comp Xo c)]

section Concrete

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end Concrete

end GlobalTheory.TrivOrderTieCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.framedPointMove_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∃ ν : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X), ν.φ = 𝟙 _ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMove (𝟙 Xo.X) ν y y) ∧ (∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ'), ∃ μ : SABMap Xo.univ.t Xo.univ.t (ρ ≫ ρ'), μ.φ = ν.φ ≫ ν'.φ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrMove ρ ν y y' → FrMove ρ' ν' y' y'' → FrMove (ρ ≫ ρ') μ y y'') ∧ ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrMap φ y' z') ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S), FrBor t y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrBor t y' z' := by
  first | exact @GlobalTheory.MoveCalc.frMove_calculus | exact GlobalTheory.MoveCalc.frMove_calculus | (intros; apply GlobalTheory.MoveCalc.frMove_calculus <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnivFibre

theorem exists_fibre_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), σ (baseKA l).ρ = H.rt0 → g = Module.finrank ℚ E / 2 * (D.p + D.q) → IsPeriod (U.Di i) ty P → ∃ (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (m : SABMap t Xo.univ.t (U.u i P)), (∀ z, (e z).left ≫ m.φ = (U.ex i P z).left) ∧ (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond (U.Di i) t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : (U.Di i).La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((U.Di i).EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro E _ _ _ H D l Xo σ g ty U i P hσ hg hP
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp ℂ), Nonempty (SABMap t Xo.univ.t (U.u i P)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (U.u i P) Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨π, hπ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) (U.u i P) (Category.id_comp _).symm
  have he : ∀ z, (π.symm (U.ex i P z)).left ≫ m.φ = (U.ex i P z).left := fun z => by
    rw [← hπ, π.apply_symm_apply]
  obtain ⟨ha, hk⟩ := amplePt _ ℂ (U.u i P) Xo.univ.t.G t.G m.φ m.cart _ _ Xo.univ.t.PP.isLB t.PP.isLB hL
    Xo.univ.ample Xo.univ.ktriv
  have hdet := (Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)).1
  rw [hσ] at hdet
  refine ⟨t, fun z => π.symm (U.ex i P z), m, he,
    MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ?_, ha, hk, fun τ => ?_,
    fun z w => (congrArg π.symm (U.ex_add i P hP z w)).trans (map_mul π.symm _ _), π.symm.surjective.comp (U.ex_onto i P hP),
    fun z => by rw [← U.ex_ker i P hP z, map_eq_one_iff _ π.symm.injective], fun a z => ?_, ?_,
    fun k a b c hk hc => ?_⟩
  · rw [hg]
    have := smoothOfRelativeDimension_isStableUnderBaseChange (Module.finrank ℚ E / 2 * (D.p + D.q))
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) m.cart.1
      (ObjDim.smoothOfRelativeDimension Xo.univ)
  · rw [LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act,
      LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act, Category.id_comp,
      (U.sig i).1, (U.sig i).2]
    exact hdet τ
  · apply π.injective
    rw [π.apply_symm_apply, U.ex_lin i P hP]
    apply Over.OverMorphism.ext
    rw [hπ, Over.comp_left, Over.comp_left, Category.assoc, ← he z, Category.assoc]
    exact congrArg _ (m.act a).symm
  · refine HolTorsion.isHolTo_of_isPullback m.cart.1
      (HolTorsion.isHolTo_congr (HolHom.isHolTo_ex U i hP) fun z _ => he z)
      (HolTorsion.isHolTo_congr (c := fun _ => 𝟙 (Sp ℂ))
        (HolHom.isHolTo_of_holAt isOpen_univ fun z _ => HolHom.holAt_const _ _)
        fun z _ => Over.w (π.symm (U.ex i P z)))
  · have h := U.ex_weil i P hP k a b c hk hc
    have key : ∀ (y : Sp ℂ ⟶ Xo.X) (_ : y = (𝟙_ (Over (Sp ℂ))).hom ≫ U.u i P) (x₀ y₀ : Over.mk y ⟶ Xo.univ.t.G)
        (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ t.G), x.left ≫ m.φ = x₀.left → x'.left ≫ m.φ = y₀.left →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k x₀ y₀ (unitOn c) → Out.WeilIs t.G t.PP.L k x x' (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ Xo.univ.t.PP.isLB t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁.symm h₂.symm).2 h₃
    exact key _ (Category.id_comp _).symm _ _ _ _ (he _) (he _) h

end GlobalTheory.UnivFibre
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExpUniqFamily

theorem linear_eq_zero_of_discrete {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, f z ∈ Λ) (z : Fin g → ℂ) : f z = 0 := by
  have hc : Continuous (fun z => (⟨f z, hf z⟩ : Λ)) :=
    f.continuous_of_finiteDimensional.subtype_mk _
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using this

theorem eq_iff_sub {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  have h := he (z - w) w
  rw [sub_add_cancel] at h
  rw [h]
  exact mul_eq_right

theorem int_eq_of_exp (n n' : ℤ)
    (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n' : ℂ) / k)) : n = n' := by
  have hk : 0 < (n' - n).natAbs + 1 := Nat.succ_pos _
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  generalize hkk : (n' - n).natAbs + 1 = k at hk hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : ((n' - n : ℤ) : ℂ) = ((k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hm ⊢
    linear_combination hm
  have h4 : n' - n = k * m := Int.cast_injective h3
  have h5 : n' - n = 0 := Int.eq_zero_of_abs_lt_dvd (m := k) ⟨m, h4⟩ (by
    rw [← hkk, Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem algebraic {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  have h1 : ∀ z, f' (f z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P.range (f' ∘ₗ f - LinearMap.id) (fun z => (hk _).1 <|
      (eq_iff_sub e ha _ _).1 (by simp [hf, hf'])) z
  have h2 : ∀ z, f (f' z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ f' - LinearMap.id) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp [hf, hf'])) z
  let d : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => LinearMap.pi fun k => χ k a • LinearMap.proj k
  have hd : ∀ a z, d a z = fun k => χ k a * z k := fun a z => rfl
  have h3 : ∀ a z, f (d a z) = d a (f z) := fun a z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ d a - d a ∘ₗ f) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp only [LinearMap.comp_apply, hf, hd, hl, hl'])) z
  have m1 : ∀ a, ∃ b, P' b = f (P a) := fun a => (hk' _).1 (by rw [hf]; exact (hk _).2 ⟨a, rfl⟩)
  have m2 : ∀ b, ∃ a, P a = f' (P' b) := fun b => (hk _).1 (by rw [hf']; exact (hk' _).2 ⟨b, rfl⟩)
  choose ga hga using m1
  choose de hde using m2
  let gam : L ≃ₗ[O] L' :=
    { toFun := ga
      invFun := de
      map_add' := fun a b => iP' (by simp [hga])
      map_smul' := fun c a => iP' (by
        have e1 : P (c • a) = d c (P a) := funext fun i => hP c a i
        have e2 : P' (c • ga a) = d c (P' (ga a)) := funext fun i => hP' c _ i
        rw [RingHom.id_apply, hga, e1, e2, hga, h3])
      left_inv := fun a => iP (by rw [hde, hga, h1])
      right_inv := fun b => iP' (by rw [hga, hde, h2]) }
  refine ⟨LinearEquiv.ofLinear f f' (LinearMap.ext h2) (LinearMap.ext h1), gam, hf, hga, ?_⟩
  intro k a b hk0 hab
  have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  rw [← hf, map_smul, ← hga, eq_iff_sub e' ha', hk'] at hab
  obtain ⟨c, hc⟩ := hab
  refine ⟨c, iP' ?_⟩
  show P' (ga a) = _
  rw [map_add (f := _), map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hk1, one_smul]
  abel

theorem isHolTo_fibre {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} (y : V × W → (Sp ℂ ⟶ X)) (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hd : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have := h1.preimage hd.continuous
    convert this using 1
    ext z
    simp
  · exact h2.comp hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) :=
  isHolTo_fibre _ (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0

theorem fibrewise {X : Scheme.{0}} (t : SAB H X) (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (hy : y = y') (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : (∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
      ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
        ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e' (h z)).left = (e z).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') ∧
      ∀ (k : ℕ) (s : 𝟙_ (Over X) ⟶ t.G) a b, 0 < k → toUnit _ ≫ s = e ((k : ℂ)⁻¹ • P a) →
        toUnit _ ≫ s = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  subst hy
  have dk : DiscreteTopology {z // e z = 1} := by
    have h0 : (fun z => e z = 1) = fun z => z ∈ P.range := funext fun z => propext (hk z)
    show DiscreteTopology (Subtype fun z => e z = 1)
    rw [h0]
    exact hP.2.2.1
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e e' (𝟙 _) (MonoidHom.id _) t.semi.smooth ha ha' hh hh' hd' dk'
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨f', hf', -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e' e (𝟙 _) (MonoidHom.id _) t.semi.smooth ha' ha hh' hh hd dk
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨h, gam, h1, h2, h3⟩ := algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1 hP.2.1 hP'.2.1
    hP.2.2.1 hP'.2.2.1 e e' ha ha' hk hk' (fun a x => x ≫ t.act.act a) hl hl' f f' hf hf'
  refine ⟨h, gam, fun z => by rw [h1], h2, fun a a' => ?_, fun k s a b hk0 e1 e2 => h3 k a b hk0 (e1.symm.trans e2)⟩
  refine int_eq_of_exp _ _ fun k hk0 => ?_
  have w1 := hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t.G t.PP.L t.PP.isLB ℂ y k _ _ _ _ w2 w1)

end ExpUniqFamily

theorem familyUnif_exp_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i j P P' hP hP' hu
  obtain ⟨h, gam, h1, h2, h3, h4⟩ := ExpUniqFamily.fibrewise Xo.univ.t (U.Di i) (U.Di j) ty P P' hP hP' _ _ hu
    (U.ex i P) (U.ex j P') (U.ex_add i P hP) (U.ex_add j P' hP') (U.ex_ker i P hP) (U.ex_ker j P' hP')
    (U.ex_lin i P hP) (U.ex_lin j P' hP') (U.ex_weil i P hP) (U.ex_weil j P' hP')
    (ExpUniqFamily.isHolTo_ex U i P hP) (ExpUniqFamily.isHolTo_ex U j P' hP') (U.ex_diff i P hP) (U.ex_diff j P' hP')
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  exact ⟨h, gam, h1, h2, h3,
    fun a ha => h4 l.M _ _ _ hM (U.ex_eta i P hP a ha) (U.ex_eta j P' hP' a ha),
    fun a => h4 l.A _ _ _ l.A_pos (U.ex_etaA i P hP a) (U.ex_etaA j P' hP' a)⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.AbVarProj

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem mem_nonzeroLocus_iff_sval {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    y ∈ nonzeroLocus s ↔ IsUnit (sval s (𝟙 Y) y J) := by
  refine ⟨fun h => ?_, fun h => (mem_nonzeroLocus s y).2 ⟨_, hJ.mem φ (𝟙 Y), h⟩⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact isUnit_sval s (𝟙 Y) y hJ k hk

end General

section Group
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

end Group

end GlobalTheory.AbVarProj
end
end
