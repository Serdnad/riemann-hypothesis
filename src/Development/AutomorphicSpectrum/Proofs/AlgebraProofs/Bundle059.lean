module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrderPSquaredExtremalColength
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelFacts
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamPull
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle057
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.lattice_family_model_bundles : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (N : I → ℕ) (V : I → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module Ω (V j)] (Γ : ∀ j, (∀ k, ι k) → AddSubgroup (V j)), (∀ j, Module.finrank Ω (V j) = N j ∧ IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset (V j), Γ j c = spanOver (chartRing O (mseg x) c) (S : Set (V j)) ∧ Submodule.span Ω (S : Set (V j)) = ⊤) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j c, mseg (joinCoord x z) c ≠ 0 → LocFree (chartRing O (mseg (joinCoord x z)) c) (N j) (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set (V j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlattenMany.main | exact GlobalTheory.CompanionTheory.Ar.FlattenMany.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FlattenMany.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.line_lattice_family_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlattenLines.main | exact GlobalTheory.CompanionTheory.Ar.FlattenLines.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FlattenLines.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.hodge_image_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.order_p_squared_extremal_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → Fintype.card N = p ^ 2 → ∀ AA : HopfOrder (C := C) R N, ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = v (p : C) ^ (p ^ 2) → (∃ t : N, ∃ g ∈ AA.carrier, v (g t - g 0) = 1) → ∃ e : ZMod p × ZMod p ≃+ N, AA.carrier.map (LinearMap.funLeft R C (e : ZMod p × ZMod p → N)) = tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : (ZMod p)) => ψ x)) (intFun R (ZMod p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split | exact GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.OrdSplit.ord_split <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.model_refinement_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormalJoin.main | exact GlobalTheory.CompanionTheory.Ar.NormalJoin.main | (intros; apply GlobalTheory.CompanionTheory.Ar.NormalJoin.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.lattice_family_model_facts : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamGood1.main | exact GlobalTheory.CompanionTheory.Ar.FamGood1.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamGood1.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamPull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) :=
  @PositivityTheory.Xgn.t_fam_pull

end GlobalTheory.CompanionTheory.Ar.FamPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.alpha_kernel_derivative_vanishes : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv (R := R) ((0 : Fin 2), i) g)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Kill.germKill | exact GlobalTheory.CompanionTheory.Ar.Kill.germKill | (intros; apply GlobalTheory.CompanionTheory.Ar.Kill.germKill <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.sub_degree_bot_and_max_exists : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L → subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max | exact GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.ConjEq

theorem eq_zero_of_scale {S : Type} [Finite S] (h : S → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (H : ∀ s, ∃ u, h u = p * h s) (s : S) : h s = 0 := by
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun s => |h s|)
  obtain ⟨u, hu⟩ := H m
  have h1 : |h u| = p * |h m| := by
    rw [hu, abs_mul, Nat.abs_cast]
  have h2 : |h u| ≤ |h m| := hm u
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have h4 : |h m| = 0 := by
    have h5 : 0 ≤ |h m| := abs_nonneg _
    nlinarith
  have h6 : |h s| ≤ 0 := h4 ▸ hm s
  exact abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))

variable {K : Type} [Field K]

theorem eig_star {O V : Type} [CommRing O] [StarRing O] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ χ' : O → K) (h : ∀ a, χ' a = χ (star a)) :
    eig (fun a => ρ (star a)) χ = eig ρ χ' := by
  ext x
  simp only [eig, Submodule.mem_iInf]
  constructor
  · intro H a
    have := H (star a)
    rwa [star_star, ← h] at this
  · intro H a
    have := H (star a)
    rwa [h, star_star] at this

section Data

variable (C : ACurve K) {p : ℕ} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (D : ConjData C p O d)

theorem lie_hom (a : O) : IsHom C D.lie D.lie (Matrix.toLin' (D.ρ a)) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  refine (D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩
  simpa using D.ρH_fst a y

theorem dual_bun : IsBun C (dotDual C D.lie) :=
  (deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1

variable {k S : Type} [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k))

theorem hodge_eq (hχ : IsSplit χ) (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t : S)
    (hst : ∀ a, χ t a = χ s (star a)) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))) =
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _)
    (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH
    (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge
    (fun a x => by simpa using (D.ρH_inr a x).symm) (fun a y => by simpa using D.ρH_fst a y) s
  have h2 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h3 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, h2, h3]
  ring

theorem conj_eq [Fact p.Prime] [CharP K p] (hχ : IsSplit χ)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t u : S)
    (hst : ∀ a, χ t a = χ s (star a)) (hu : ∀ a, χ u a = χ s a ^ p) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ u a))) =
      p * (subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a)))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie))
    D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH
    (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj
    (fun a x => by simpa using D.α_act a x) (fun a y => by simpa using D.β_act a y) u
  have hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p := by
    funext a
    rw [hu, map_pow]
  have h2 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))
  have h3 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose)
    (fun a => algebraMap k K (χ s a))
  have h4 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h5 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]
  ring

end Data

theorem subDeg_eig_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  intro K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst
  have hp : p.Prime := Fact.out
  haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hall := (isSplit_injective_and_exists O k S χ hχ).2
  have hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a) := fun s => by
    obtain ⟨t, ht⟩ := hall ((χ s).comp (starRingEnd O))
    exact ⟨t, fun a => by rw [ht]; rfl⟩
  have hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p := fun s => by
    obtain ⟨u, hu⟩ := hall ((frobenius k p).comp (χ s))
    exact ⟨u, fun a => by rw [hu]; rfl⟩
  have hzero := eq_zero_of_scale
    (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))))
    p hp.two_le (fun s => by
      obtain ⟨t, ht⟩ := hconj s
      obtain ⟨u, hu⟩ := hfrob s
      refine ⟨u, ?_⟩
      rw [conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s
  have h := hodge_eq C D χ hχ hk s t hst
  rw [hzero] at h
  exact sub_eq_zero.1 h.symm

end GlobalTheory.CompanionTheory.Ar.Crv.ConjEq
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_torsion_augmentation : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt → ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | exact GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  classical
  intro E _ _ _ H D I _ _ e hcard hli
  haveI := D.fin
  have T : ∀ (c : 𝓞 E) (x y : D.La), Algebra.trace ℚ E (algebraMap (𝓞 E) E c * sesq D x y) = ((D.EF (c • x) y : ℤ) : ℚ) := by
    intro c x y
    have key : ∀ j, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * sesq D x y) = ((D.EF (RingOfIntegers.basis E j • x) y : ℤ) : ℚ) := by
      intro j
      have hterm : ∀ k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * (((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : E) * HT.dualInt E k)) = ((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : ℚ) * (if j = k then 1 else 0) := by
        intro k
        rw [← HT.LatBasic.trace_dualInt k j, ← map_intCast (algebraMap ℚ E), mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (algebraMap (𝓞 E) E _), ← NumberField.integralBasis_apply]

      simp only [sesq, Finset.mul_sum, map_sum, hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact mul_one _
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr c]

    simp only [map_sum, Finset.sum_mul, Finset.sum_smul, LinearMap.sum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, smul_mul_assoc, map_zsmul, key j, smul_assoc, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    norm_cast
  have hy : ∀ y : D.La, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    by_contra hne
    push_neg at hne
    have hli' : LinearIndependent (𝓞 E) (fun o : Option I => Option.elim o y e) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fintype.sum_option] at hg
      simp only [Option.elim] at hg
      have hnone : g none = 0 := by
        by_contra h0
        apply hne (g none) h0
        have : g none • y = -∑ i, g (some i) • e i := eq_neg_of_add_eq_zero_left hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
      rw [hnone, zero_smul, zero_add] at hg
      intro o
      cases o with
      | none => exact hnone
      | some i => exact (Fintype.linearIndependent_iff.mp hli) _ hg i
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_option, hcard, D.rank] at this
    omega
  have hfin : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ y : D.La, c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (𝓞 E) D.La).FG)
    choose f hf0 hfm using hy
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr (fun y _ => hf0 y), ?_⟩
    intro y
    have hy' : y ∈ Submodule.span (𝓞 E) (s : Set D.La) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
    · intro z hz
      rw [← Finset.mul_prod_erase s f hz, mul_comm (f z), mul_smul]
      exact Submodule.smul_mem _ _ (hfm z)
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc0, hc⟩ := hfin
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  have hN0 : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  have hNy : ∀ y : D.La, Ideal.absNorm (Ideal.span {c}) • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← ht, mul_smul]
    exact Submodule.smul_mem _ _ (hc y)
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ v
    choose a ha using fun i => RingHom.mem_rangeS.mp (hb i (Finset.mem_univ i))
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv0
    have hai0 : a i0 ≠ 0 := by
      intro h0
      have := ha i0
      rw [h0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
      rcases this with h | h
      · exact nonZeroDivisors.coe_ne_zero b ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h)
      · exact hi0 h
    have hx0 : (∑ i, a i • e i) ≠ 0 := fun h => hai0 ((Fintype.linearIndependent_iff.mp hli) a h i0)
    have hEFc : ∀ (c : 𝓞 E) (n : I), D.EF (c • ∑ i, a i • e i) (e n) = 0 := by
      intro c n
      have h1 : c • ∑ i, a i • e i = ∑ m, (c * a m) • e m := by simp only [Finset.smul_sum, mul_smul]
      apply Int.cast_injective (α := ℚ)

      rw [h1, map_sum, LinearMap.sum_apply, Int.cast_sum, Int.cast_zero]
      simp only [← T]

      rw [← map_sum]
      have h2 : ∑ m, algebraMap (𝓞 E) E (c * a m) * sesq D (e m) (e n) = algebraMap (𝓞 E) E c * (algebraMap (𝓞 E) E b * (v ᵥ* gramE D e) n) := by
        simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, map_mul, ha, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => by ring)
      rw [h2, hv, Pi.zero_apply, mul_zero, mul_zero, map_zero]
    have hEF : ∀ y, D.EF (∑ i, a i • e i) y = 0 := by
      intro y
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp (hNy y)
      have h2 : D.EF (∑ i, a i • e i) (Ideal.absNorm (Ideal.span {c}) • y) = 0 := by

        rw [← hg, map_sum]
        refine Finset.sum_eq_zero (fun n _ => ?_)
        have := D.adj (H.bar.symm (g n)) (∑ i, a i • e i) (e n)
        rw [RingEquiv.apply_symm_apply] at this
        rw [← this]
        exact hEFc _ n
      rw [map_nsmul] at h2
      exact (smul_eq_zero.mp h2).resolve_left hN0
    apply hx0
    apply D.unimod.1
    rw [map_zero]
    exact LinearMap.ext hEF
  · apply Set.Finite.subset ((Nat.divisors (Ideal.absNorm (Ideal.span {c}))).finite_toSet.preimage (f := ((↑) : Nat.Primes → ℕ)) (Set.injOn_of_injective Subtype.val_injective))
    intro ℓ hℓ
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    by_contra hd
    exact hℓ (by unfold IsLocBasis; exact ⟨hli, _, hd, hNy⟩)
end
