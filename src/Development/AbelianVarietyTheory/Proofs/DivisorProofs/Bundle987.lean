module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle968
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit (R := k) (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : Frac F) (s : ℕ), 1 ≤ s → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ IsCoef (2 * s) 𝔞 𝔟 ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) a := by
  first | exact @GlobalTheory.HilbFam.exists_isCoef | exact GlobalTheory.HilbFam.exists_isCoef | (intros; apply GlobalTheory.HilbFam.exists_isCoef <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_smul_direction | exact GlobalTheory.HilbFam.jet_split_smul_direction | (intros; apply GlobalTheory.HilbFam.jet_split_smul_direction <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

variable (p : ℕ) [Fact p.Prime]

abbrev frobR (R : Type) [CommRing R] (hR : (p : R) = 0) : R →+* R :=
  GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR

theorem frobR_apply (R : Type) [CommRing R] (hR : (p : R) = 0) (x : R) : frobR p R hR x = x ^ p :=
  congrArg (x ^ ·) (pow_one p)

theorem frob_sp (R : Type) [CommRing R] (hR : (p : R) = 0) (h : (p : Γ(Sp R, ⊤)) = 0) :
    GlobalTheory.VB.frob (Sp R) p h = spMap (frobR p R hR) :=
  GlobalTheory.SS.FrobField.absFrob_spec R p 1 Fact.out h _ fun _ ↦ rfl

theorem frob_comp_hom (R : Type) [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}} (f : X ⟶ Sp R)
    (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ f = f ≫ spMap (frobR p R hR) := by
  have h0 : (p : Γ(Sp R, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp R hR
  have hn : GlobalTheory.VB.frob X p h ≫ f = f ≫ GlobalTheory.VB.frob (Sp R) p h0 :=
    GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out h h0
  rw [hn, frob_sp p R hR h0]

theorem cast_left (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) :
    (p : Γ(A.left, ⊤)) = 0 :=
  GlobalTheory.SS.FrobField.cast_zero_of_hom A.hom (GlobalTheory.SS.FrobField.cast_zero_sp R hR)

theorem frobMor (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (h : (p : Γ(A.left, ⊤)) = 0) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p h) := by
  refine { dp := isDPMorphism_of_eq_bot _ rfl _ _, base := ?_,
           w := frob_comp_hom p R hR A.hom h, mul := ?_ }
  · simp
  · intro T x y x₀ y₀ hx hy
    have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
    have hn (f : T.left ⟶ A.left) :
        GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p h :=
      GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT h
    let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
      Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
    have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
      simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
    have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
      simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
    subst ex ey
    rw [← MonObj.comp_mul]
    simp only [Over.comp_left, Over.homMk_left, j]
    exact hn (x * y).left

def frobDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    primDR A →ₛₗ[frobR p R hR] primDR A :=
  (frobMor p R hR A (cast_left p R hR A)).pull

def conjDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    Submodule R (primDR A) :=
  Submodule.span R (Set.range (frobDR p R hR A))

end GlobalTheory.ConjSeq

namespace GlobalTheory.DeRhamSheaf

open Limits

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

end GlobalTheory.DeRhamSheaf
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem idemLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀
  obtain ⟨e, he⟩ := homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀
  set J : Ideal B' := I.map (algebraMap R B') with hJ
  have hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ, ← Ideal.map_pow, hI] at this
    simpa using this
  have hu : ∀ c, e (e c) - e c ∈ J := by
    intro c
    rw [← hker']
    simp [map_sub, he, he₀]
  have hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0 := by
    intro x hx
    rw [hJ, Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      have h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      have h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      rw [h1, h2, ← sub_mul]
      exact hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have := hx c
      have := hy c
      rw [mul_add, map_add (f := _), map_add (f := _)]
      linear_combination hx c + hy c
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact hx (c * a)
  have hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0 := by
    intro c
    have := hkill _ (hu c) 1
    simp only [_root_.one_mul, map_sub] at this
    linear_combination this
  let e' : B' →ₐ[R] B' :=
    { toFun := fun b => 3 * e (e b) - 2 * e (e (e b))
      map_one' := by simp; norm_num
      map_mul' := by
        intro x y
        have h := hJ2 _ (hu (e x)) _ (hu (e y))
        simp only [map_mul]
        linear_combination (-6 : B') * h
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring
      commutes' := by intro r; simp only [AlgHom.commutes]; ring }
  refine ⟨e', ?_, ?_⟩
  · intro b
    show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination (-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))
  · intro b
    show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)
    simp only [map_sub, map_mul, map_ofNat, he, he₀]
    ring

end GlobalTheory.Obs
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumPic

theorem kummer_boundary_picClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ κ h0 _ h2 _ _ h5 z s hz E L hE y hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units q (cokernel κ) _ E L hE h5
  have hy' : y = CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) :=
    (GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E _ (fun U hU => h5 U (hE U hU)) 1).1 (hy.trans (GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass _ _ E L a ha).symm)
  haveI : Injective ((res ℤ (twZ q)).X 0) :=
    inferInstanceAs (Injective ((injectiveResolution (twZ q)).cochainComplex.X 0))
  let φ : Gm ⟶ (res ℤ (twZ q)).X 0 := Injective.factorThru (resι ℤ (twZ q)) κ
  have hφ : κ ≫ φ = resι ℤ (twZ q) := Injective.comp_factorThru _ _
  have hd : κ ≫ (φ ≫ (res ℤ (twZ q)).d 0 1) = 0 := by
    rw [← Category.assoc, hφ, PicSpec.resι_d]
  let ψ : cokernel κ ⟶ (res ℤ (twZ q)).X 1 := cokernel.desc κ (φ ≫ (res ℤ (twZ q)).d 0 1) hd
  have hψ : cokernel.π κ ≫ ψ = φ ≫ (res ℤ (twZ q)).d 0 1 := cokernel.π_desc _ _ _
  have hψd : ψ ≫ (res ℤ (twZ q)).d 1 2 = 0 := by
    rw [← cancel_epi (cokernel.π κ), ← Category.assoc, hψ, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, comp_zero]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term (cokernel κ) (res ℤ (twZ q)) ψ hψd
  have hzw := hz φ ψ hφ hψ w hw
  have hext : HK.ext ℤ _ z 1 (1 + 1) rfl y = s • CohomologyClass.mk (zcomp a w rfl) := by
    rw [hy']
    change CohomologyClass.mk (zcomp (zcomp a (Cocycle.ofHom (resAug _)) (add_zero 1)) z rfl) = _
    have hc : zcomp (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) z rfl =
        zcomp a (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1)) rfl :=
      Cocycle.ext (Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by omega))
    rw [hc, ← cpre_mk, hzw]
    rw [Units.smul_def, Units.smul_def, map_zsmul]
    rfl
  rw [hext]
  congr 1
  refine GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary q E L hE φ (GlobalTheory.T.kummerSplittingDefect_glue_qthRoots q φ (GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq q κ h2 φ hφ)) (cokernel κ) a w (fun U x v hv => ?_)
  obtain ⟨c, hc, hac⟩ := ha U x
  have hU : IsUnit (q : Γ(U, ⊤)) := hE U ⟨x.face 0⟩
  have hpow : ∀ n : ℕ, unitSec (v ^ n) = (n : ℤ) • unitSec v := by
    intro n
    induction n with
    | zero =>
      have := PicSpec.unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1
      rw [mul_one] at this
      simpa using this
    | succ n ih => rw [pow_succ, PicSpec.unitSec_mul, ih]; push_cast; rw [add_smul, one_smul]
  have hcv : c = Sec.map (cokernel.π κ) (unitSec v) := by
    refine (h5 U hU).1 (hc.trans ?_)
    rw [PicSpec.sec_map_comp, cokernel.π_desc, ← hv, hpow]
    exact (map_zsmul (CupSpec.mapHom Gm Gm (unitSec v)) (q : ℤ) (𝟙 Gm)).symm
  rw [hac, PicSpec.sec_map_comp, hw, hcv, PicSpec.sec_map_comp, hψ]
  rfl

end GlobalTheory.EtC.KumPic

end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu WithConv

namespace GlobalTheory.Dieu

theorem hom_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k]
    {G H : PDivGroup p k} (m : ℕ) {f : G ⟶ H} (e : (p : ℤ_[p]) ^ m • f = 0) : f = 0 := by
  induction m generalizing f with
  | zero => simpa using e
  | succ m ih =>
    refine ih ?_
    refine eq_zero_of_prime_smul_eq_zero ?_
    rw [← mul_smul, ← pow_succ']
    exact e

theorem exists_comp_eq_of_kerIdeal_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q →
    kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ k _ _ G Q H m q q' f h1 h2 hk

  have hq : kerIdeal (q.app m) ≤ RingHom.ker (q'.app m : G.A m →ₐ[k] Q.A m) := by
    refine (kerIdeal_le_ker_iff (q.app m) _).2 fun c => ?_
    have e := congrArg (fun x => Hom.conv x m) h2
    simp only [pow_smul_conv] at e
    have e2 := DFunLike.congr_fun (congrArg ofConv (congrArg toPts e)) c
    rw [map_one] at e2
    refine e2.trans ?_
    rfl
  have hf := (kerIdeal_le_ker_iff (f.app m) _).1 (hk.trans hq)
  have hc : Hom.conv (q' ≫ f) m = 1 := by
    refine toPts_injective (ofConv_injective (AlgHom.ext fun c => ?_))
    rw [map_one]
    refine (hf c).trans ?_
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k Q H m (q' ≫ f) hc
  refine ⟨g, sub_eq_zero.1 (hom_eq_zero_of_pow_smul_eq_zero m ?_)⟩
  rw [smul_sub, ← Linear.comp_smul, ← hg, ← Category.assoc, h1, Linear.smul_comp,
    Category.id_comp, sub_self]

end GlobalTheory.Dieu
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S → ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := by
  first | exact @GlobalTheory.FockAlg.fin_harm | exact GlobalTheory.FockAlg.fin_harm | (intros; apply GlobalTheory.FockAlg.fin_harm <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.exists_fockHarmonic_representative : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) → ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  first | exact @GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | exact GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | (intros; apply GlobalTheory.FockAlg.HarmLift.exists_harm2_rep <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.FinSupp

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable (F : Type) [Field F] [NumberField F]

def FinDiv (N : ℕ) (a : AF F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b ∈ v.adicCompletionIntegers F, evFin F v a = (N : Fv F v) * b

def finPart (a : AF F) : AF F := (0, a.2)

end GlobalTheory.FinSupp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM.ProjExt

theorem eq_pt_of_secCoord {o : Type} [CommRing o] {m : ℕ} {A : Type} [CommRing A] (c : o →+* A)
    (y : Sp A ⟶ PSpace o m) (hy : y ≫ PSpace.str o m = spMap c) (v : Fin (m + 1) → A)
    (h : SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v) :
    ∃ hv : Ideal.span (Set.range v) = ⊤, y = GlobalTheory.ProjSpace.pt c v hv := by
  have h1 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (𝟙 _) y v).2
    (by rwa [Category.comp_id])
  obtain ⟨hv, e⟩ := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c y (by rwa [Category.comp_id]) v).1 h1
  exact ⟨hv, (Category.comp_id _).symm.trans e⟩

end GlobalTheory.ZM.ProjExt
end
