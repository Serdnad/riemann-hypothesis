module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemHermitianStandardLatticeIffPairingIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSlopeSqLocalMatricesEqDeterminants
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem sqLifting_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  intro P H R _ I h R₀ _ π hπ hI
  refine ⟨GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case P H R I h R₀ π hπ hI, ?_⟩
  intro g A₀ _ A _ i hA hAa hg g' B₀ _ B _ j hB hBa hg' f₀ _ hf
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.liftHom_exists_of_noetherian_alt P H R I h R₀ π hπ hI g A₀ A i hA hAa hg g' B₀ B j hB hBa hg' f₀ hf
  exact GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, by rw [hI]; exact h⟩ A₀ B₀ A B i j hA hB hAa hBa f₀ φ hφ

end GlobalTheory.SqLift
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  first | exact @GlobalTheory.TypeFrameCover.typeFrame_cover | exact GlobalTheory.TypeFrameCover.typeFrame_cover | (intros; apply GlobalTheory.TypeFrameCover.typeFrame_cover <;> assumption)
end

section

open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

theorem _root_.GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (γ γ' : Gam Dw l), levR (lift γ, LinearMap.id) y y' → levR (lift γ', LinearMap.id) y y' → γ = γ' := by
  first | exact @GlobalTheory.LevelFree.move_unique | exact GlobalTheory.LevelFree.move_unique | (intros; apply GlobalTheory.LevelFree.move_unique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_additiveFamily_representative_zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  first | exact @GlobalTheory.DualCon.ZarGlue.zariski_glue | exact GlobalTheory.DualCon.ZarGlue.zariski_glue | (intros; apply GlobalTheory.DualCon.ZarGlue.zariski_glue <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.InertChar

section CM

open Formalism.UG Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus
  GlobalTheory.InertDoubleCoset
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem core (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hin : IsInertAt (maximalRealSubfield E) E v P) (h2 : (2 : 𝓞 E) ∉ P.asIdeal)
    (ν : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* Circle)
    (hν : ∀ k, Supp hc V e k → Stab hc V k → ν k = 1) (g : HA (AF (maximalRealSubfield E)) hc.sig V.gram)
    (hg : Supp hc V e g) : ν g = 1 := by
  have hur := unramified hc
  obtain ⟨σ, π, hσE, hσ⟩ := GlobalTheory.FixedPrime.exists_isUnramInv v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion E v P hin σ hσE hσ.2.1
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ E hc V v e he
  let ψ' : LocAlg v →+* P.adicCompletion E := ψ
  let φ : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* GL (Fin V.rank) (P.adicCompletion E) :=
    (bc ψ').comp ((MulAut.conj h⁻¹).toMonoidHom.comp (locMat hc V v))
  have hφ : ∀ k, φ k = bc ψ' (h⁻¹ * locMat hc V v k * h) := fun k => rfl
  have hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ intL (P.adicCompletion E) := fun z => (mem_ordAt_iff v z).trans (hψO z)
  have hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc (ψ.symm : P.adicCompletion E →+* LocAlg v) (bc ψ' x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E),
      bc ψ' (bc (ψ.symm : P.adicCompletion E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hmem : ∀ k, φ k ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) := fun k =>
    bc_mem_UJ_one (σ := locConj v) ψ' hψσ (conj_mem_UJ _ hon (locMat_mem hc V v k))
  have hinj : ∀ k, Supp hc V e k → ∀ k', Supp hc V e k' → φ k = φ k' → k = k' := fun k hk k' hk' e => by
    refine s2 k k' hk hk' ?_
    have := congrArg (bc (ψ.symm : P.adicCompletion E →+* LocAlg v)) e
    rw [hφ, hφ, hback, hback] at this
    exact mul_left_cancel (mul_right_cancel this)
  have hsurj : ∀ u : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)),
      ∃ k, Supp hc V e k ∧ φ k = u := fun ⟨u, hu⟩ => by
    have h1 := bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hu
    obtain ⟨k, hk, ek⟩ := s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)
    refine ⟨k, hk, ?_⟩
    show φ k = u
    rw [hφ, ek, ← hback' u]
    congr 1
    rw [hback']
    group
  have hmul : ∀ k k', Supp hc V e k → Supp hc V e k' → Supp hc V e (k * k') := fun k k' hk hk' => by
    obtain ⟨a1, a2⟩ := (s1 k).1 hk
    obtain ⟨b1, b2⟩ := (s1 k').1 hk'
    refine (s1 _).2 ⟨?_, fun w hw => by rw [map_mul, a2 w hw, b2 w hw, one_mul]⟩
    exact (map_mul (bc (infP (maximalRealSubfield E) E)) (HA.mat _ hc.sig V.gram k)
      (HA.mat _ hc.sig V.gram k')).trans (by rw [a1, b1, one_mul])
  choose l hl1 hl2 using hsurj
  let μ : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) →* Circle :=
    MonoidHom.mk' (fun u => ν (l u)) fun a b => by
      rw [← map_mul, hinj _ (hl1 _) _ (hmul _ _ (hl1 a) (hl1 b)) (by rw [map_mul, hl2, hl2, hl2]; rfl)]
  have hv2 : Valued.v (2 : P.adicCompletion E) = 1 := by
    rw [← map_ofNat (algebraMap E (P.adicCompletion E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 E) E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 h2
  have : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have key := GlobalTheory.T.unitaryGroup_character_eq_one_of_trivial_integral (P.adicCompletion E) π σ _ V.rank 1 hσ hv2 (one_mem _)
    (fun i j => by
      simp only [Units.val_one, Matrix.one_apply, eq_comm (a := j)]
      split_ifs
      · exact map_one σ
      · exact map_zero σ) μ
    (fun k hk => hν _ (hl1 k) ((GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr _ ((s1 _).1 (hl1 k)).2).2
      ((bc_mem_range_iff ψ' hO _).2 (by rw [← hφ, hl2]; exact hk)))) ⟨φ g, hmem g⟩
  rw [hinj g hg _ (hl1 ⟨φ g, hmem g⟩) (hl2 ⟨φ g, hmem g⟩).symm]
  exact key

end CM

section Lattice

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_dual (V : HSpace E) (L : Submodule (𝓞 E) V.V) (z : V.V) :
    z ∈ Formalism.HermitianLatticesTheory.dual V.hT L ↔ ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = V.hT y z := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]

def withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 : Submodule.IsLattice E Λ)
    (h2 : ∀ y : Fin V.rank → E, y ∈ Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j) : HSpace E :=
  let f : (Fin V.rank → E) →ₗ[𝓞 E] V.V :=
    V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 E)
  let L : Submodule (𝓞 E) V.V := Λ.map f
  have hL : Formalism.HermitianLatticesTheory.dual V.hT L = L := by
    refine Submodule.ext fun z => (mem_dual V L z).trans ?_
    obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective z
    constructor
    · intro h
      refine ⟨y, (h2 y).2 fun x hx => ?_, rfl⟩
      rw [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply, ← V.frame.equivFun_symm_apply]
      exact h _ ⟨x, hx, rfl⟩
    · rintro ⟨y', hy, e⟩ _ ⟨x, hx, rfl⟩
      obtain rfl : y' = y := V.frame.equivFun.symm.injective e
      have := (h2 y').1 hy x hx
      rwa [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply,
        ← V.frame.equivFun_symm_apply] at this
  { V with
    L0 := L
    standardTuple_isLattice := Submodule.IsLattice.of_fg E (h1.fg.map f)
    baseLattice_isUnimodular := hL }

theorem coord_withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 h2) :
    {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ (withLat V Λ h1 h2).L0} = Λ := by
  ext x
  rw [Set.mem_ofPred_eq, ← V.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨y, hy, e⟩
    obtain rfl : y = x := V.frame.equivFun.symm.injective e
    exact hy
  · exact fun h => ⟨x, h, rfl⟩

end Lattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_eq_one_of_nonSplit : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  intro D V Λ hΛ v ε hv ν hν g hg
  obtain ⟨⟨α, rfl, a1, a2⟩, hn⟩ := hv
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [a1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [a2 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have hn' : ∀ e : Formalism.L2.Theta.AE D, e * e = e → e * cA D e = 0 → e + cA D e =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) → False :=
    fun e e1 e2 e3 => by
      rw [← hα] at e3
      exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, a1, a2⟩, e3⟩, e3⟩
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    exact hn' e e1 e2 e3
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := fun h0 => v.ne_bot (by
    rw [← hQv, h0, Ideal.under_bot])
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have hin := GlobalTheory.FixedPrime.isInertAt_under P fun x hx => by
    by_contra hx'
    obtain ⟨e, e1, e2, e3⟩ := GlobalTheory.MovedSplit.exists_splitAt D v
      ⟨Q, hQ.isPrime, hQv, _, hx, x, (star_star (x : D.host.E)).symm, hx'⟩
    exact hn' e e1 e2 e3
  have h2' : (2 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => h2 (by
    rw [← hQv, Ideal.mem_comap, map_ofNat]; exact h)
  have he := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  subst hPv
  refine core (E := D.host.E) D.sp.cm (withLat V Λ hΛ.1 hΛ.2) he hin h2' ν (fun k hk hs => hν k hk ?_) g hg
  rw [← coord_withLat V Λ hΛ.1 hΛ.2]
  exact hs

end GlobalTheory.InertChar
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.HSChoice

namespace GlobalTheory.ChowZeroExt

def incIdeal {F : Type} [Field F] (B : ℕ) {N : ℕ} (I : Ideal (MvPolynomial (Fin N) F)) :
    Ideal (MvPolynomial ((Fin B × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
  Ideal.span ((rename (fun j => Sum.inr (Sum.inl j)) '' (I : Set (MvPolynomial (Fin N) F))) ∪
    (Set.range (fun i : Fin B => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr (Sum.inl j))) ∪
      {∑ j, X (Sum.inr (Sum.inr j)) * X (Sum.inr (Sum.inl j)) - 1}))

theorem forall_span_iff {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] (S : Set (MvPolynomial ι F))
    (x : ι → Ω) : (∀ g ∈ Ideal.span S, aeval x g = 0) ↔ ∀ g ∈ S, aeval x g = 0 := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩
  have : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω) :=
    Ideal.span_le.2 fun g hg => h g hg
  exact this hg

theorem forall_incIdeal_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {B N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) F)) (x : (Fin B × Fin N) ⊕ (Fin N ⊕ Fin N) → Ω) :
    (∀ g ∈ incIdeal B I, aeval x g = 0) ↔
      (∀ g ∈ I, aeval (fun j => x (Sum.inr (Sum.inl j))) g = 0) ∧
      (∀ i, ∑ j, x (Sum.inl (i, j)) * x (Sum.inr (Sum.inl j)) = 0) ∧
      ∑ j, x (Sum.inr (Sum.inr j)) * x (Sum.inr (Sum.inl j)) = 1 := by
  rw [incIdeal, forall_span_iff]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun i => ?_, ?_⟩
    · have := h _ (Or.inl ⟨g, hg, rfl⟩)
      rwa [aeval_rename] at this
    · simpa using h _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · simpa [sub_eq_zero] using h _ (Or.inr (Or.inr rfl))
  · rintro ⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · rw [aeval_rename]
      exact h1 g hg
    · simpa using h2 i
    · simpa [sub_eq_zero] using h3

theorem exists_dual {Ω : Type} [Field Ω] {N : ℕ} {y : Fin N → Ω} (hy : y ≠ 0) :
    ∃ z : Fin N → Ω, ∑ j, z j * y j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  refine ⟨Pi.single j (y j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ hj
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem ne_zero_of_dual {Ω : Type} [Field Ω] {N : ℕ} {y z : Fin N → Ω} (h : ∑ j, z j * y j = 1) :
    y ≠ 0 := by
  rintro rfl
  simp at h

variable {F : Type} [Field F] {D N d : ℕ} {I : Ideal (MvPolynomial (Fin N) F)}
  {f : MvPolynomial (Fin (D + 1) × Fin N) F}

theorem aeval_eq_zero_of_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω]
    (u : Fin (D + 1) × Fin N → Ω) (y : Fin N → Ω) (hy : y ≠ 0) (hI : ∀ g ∈ I, aeval y g = 0)
    (hu : ∀ i, ∑ j, u (i, j) * y j = 0) : aeval u f = 0 := by
  obtain ⟨z, hz⟩ := exists_dual hy
  have key := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by
    obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I x).1 hx
    rw [aeval_rename]
    exact (hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))
    ((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)
  rwa [aeval_rename] at key

theorem exists_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (u : Fin (D + 1) × Fin N → Ω) (hu : aeval u f = 0) :
    ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by
    obtain ⟨y, hy, h1, h2⟩ := (hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))
    obtain ⟨z, hz⟩ := exists_dual hy
    exact ⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u
    ((forall_span_iff _ _).2 (by rintro g rfl; exact hu))
  obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I _).1 hw
  exact ⟨_, ne_zero_of_dual h3, h1, h2⟩

theorem forall_join_iff {Ω : Type} [Field Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω) :
    (∀ i, ∑ j, join s ξ (i, j) * y j = 0) ↔ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0 := by
  rw [Fin.forall_fin_succ']
  simp [join]

theorem zero_set_ext : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 →
      (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 →
      aeval (join s ξ) f = 0) ∧
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω),
      aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧
        (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  intro F _ _ D N d I f hf
  refine ⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩
  · exact aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)
  · obtain ⟨y, hy, h1, h2⟩ := exists_common_zero hf _ h
    exact ⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩

end GlobalTheory.ChowZeroExt
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_cube_valuation_eq_discriminant : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  first | exact @GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | exact GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | (intros; apply GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ), IsAdelic A → (∀ σ, (Y σ).det ≠ 0) → (∀ σ, ‖(Y ((starRingEnd ℂ).comp σ)).det‖ = ‖(Y σ).det‖) → slope_sq (matNorm Y) (locLat A) = 2 * detDeg A Y / (Fintype.card ι : ℝ) := by
  first | exact @GlobalTheory.LocMatSlope.slope_sq_locLat | exact GlobalTheory.LocMatSlope.slope_sq_locLat | (intros; apply GlobalTheory.LocMatSlope.slope_sq_locLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.tangentVector_section_value_eq_expansion_sum : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_at_tangent | exact GlobalTheory.MBLow.TanExp.value_at_tangent | (intros; apply GlobalTheory.MBLow.TanExp.value_at_tangent <;> assumption) | exact @GlobalTheory.MBLow.TanExp.ds_sum | exact GlobalTheory.MBLow.TanExp.ds_sum | (intros; apply GlobalTheory.MBLow.TanExp.ds_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ → vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) = (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  first | exact @GlobalTheory.MBLow.Cl.JetGen.tangent_generators | exact GlobalTheory.MBLow.Cl.JetGen.tangent_generators | (intros; apply GlobalTheory.MBLow.Cl.JetGen.tangent_generators <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.pairSections_fg_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  first | exact @GlobalTheory.HSNef.PairFG.h_fg | exact GlobalTheory.HSNef.PairFG.h_fg | (intros; apply GlobalTheory.HSNef.PairFG.h_fg <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ), ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.exists_pos_nonzero_mem_H | exact GlobalTheory.HSNef.exists_pos_nonzero_mem_H | (intros; apply GlobalTheory.HSNef.exists_pos_nonzero_mem_H <;> assumption)
end
