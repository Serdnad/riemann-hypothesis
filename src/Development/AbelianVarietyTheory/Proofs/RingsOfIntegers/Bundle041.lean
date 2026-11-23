module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
public import Mathlib.RingTheory.Trace.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle123
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

theorem _root_.GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  first | exact @GlobalTheory.PlaceInt.host_galois_discr_moves | exact GlobalTheory.PlaceInt.host_galois_discr_moves | (intros; apply GlobalTheory.PlaceInt.host_galois_discr_moves <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.isotropic_group_primary_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.isotropic_primary_decomposition | exact GlobalTheory.isotropic_primary_decomposition | (intros; apply GlobalTheory.isotropic_primary_decomposition <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  first | exact @GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | exact GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | (intros; apply GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NonzeroClosedFibre

theorem exists_restrict {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X) (k : ℤ)
    (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k))) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => k)),
      GeneratorPullback.SecScal L (fun _ : Fin 1 => h) (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
  have key : ∀ φ' : Fin 1 → (Y ⟶ X), (fun _ : Fin 1 => h ≫ 𝟙 X) = φ' →
      ∃ s : LB.Sec (LB.LinComb L φ' (fun _ => k)),
        GeneratorPullback.SecScal L φ' (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h,
      SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_⟩
    exact (SectionScalarValuation.sval_pullSec _ _ σ h _ y hJ).symm
  exact key _ (funext fun _ => Category.comp_id h)

theorem secIsMul_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) {k : ℕ} {χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))} {g : D.toPre.SecB k χ}
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s (D.toPre.famφB χ)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1) {r : ℚ} (hr : 0 < r) (hs : VGe D F v k χ s r) :
    ∃ g' : D.toPre.SecB k χ, SecIsMul D.toPre.P.A.hom ϖ g g' := by
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hs
  have hb : ∀ i, 0 < v (a₀ i) := fun i => lt_of_lt_of_le (by exact_mod_cast hr) (hva i)
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv g τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal hg q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero g div₁

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), NonzeroOnSpecial U ϑ → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB 1 α, (∀ e, U.ExpandsAt e 1 ϑ g) ∧ (¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, (g 0).f j = Geo.Tor.constFn D.toPre.P.A.hom _ ϖ * σ'.f j) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre F).left 1) ∧ NuGe D Q F v 1 θ 0 ∧ ¬ ∃ r : ℚ, 0 < r ∧ NuGe D Q F v 1 θ r := by
  intro hG V _ _ _ ϖ hϖ D Q hQ A G _ _ U ϑ hϑ
  obtain ⟨s, hs⟩ := exists_restrict U.LG.isLB (pullback.fst G.hom (jK V)) ((1 : ℕ) : ℤ) ϑ
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 s
  obtain ⟨g, hexp, hgE⟩ := GlobalTheory.T.expansion_of_integral_section_is_integral V ϖ hϖ D A G U.toUnifPre 1 ϑ s hs E hE
  have hdiv := (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ)
    (GlobalTheory.FamInt.valOver_ordVal hϖ) E g hgE).2
  have hind : ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g' :=
    (GlobalTheory.ClosedFibreTerm.main V ϖ hϖ D A G U.toUnifPre ϑ g (hexp 0) hdiv).1 hϑ
  refine ⟨g, hexp, hind, fun F _ _ v hv => ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hG V (maximalIdeal V) D 1 E g hgE F
  refine ⟨θ, hθ, (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ g hθ).1, ?_⟩
  rintro ⟨r, hr, hν⟩
  refine hind (secIsMul_of_vge hϖ D F v hv (hθ 0) ?_ (hν 0))
  rw [QForm.Q_zero hϖ D hQ]
  simpa using hr

end GlobalTheory.NonzeroClosedFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceExtField

theorem cdvrExtSt : PullbackSections.CDVRExtSt := by
  intro T hT K _ jK hfin
  letI := jK.toAlgebra
  obtain ⟨T', iT, e, ψ, _, he, hv, hψ, _, hres⟩ := exists_cdvr_finite_extension T K
  refine ⟨T', ψ.toRingHom, e, he, fun a _ => ?_, hres hT⟩

  have h : ψ.toRingHom (jK a) = iT a := hψ a
  rw [h, hv a]

end GlobalTheory.PlaceExtField
end
