module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle026
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XTrivflagmodAt
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem ext_tensor_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) :=
  PositivityTheory.HtPt.Mh.ext_tensor

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.lattice_image_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) :=
  @_root_.PositivityTheory.Xgn.image_lattice_base_change
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.lattice_base_change_larger_ring_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | exact GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b :=
  @PositivityTheory.Xgn.t_trivflagmod_at

end GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_quotient_equivalence : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N₁ V₁), QuotEquiv O x E.lat E'.lat F.lat F'.lat ↔ QuotIso O x E E' F F' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso.main | exact GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.lattice_family_injective_model_facts : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main | exact GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.iso_pow_one_law_formula : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law | exact GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.multiplication_by_p_factors_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ V : Pt R 1 d, (∀ i, constantCoeff (V i) = 0) ∧ B.A.act (p : O) = comp1 V (ptPow R d p 0) ∧ lin V 1 = hw B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.mulp_factors_frobenius | exact GlobalTheory.CompanionTheory.Ar.Conj.mulp_factors_frobenius | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.mulp_factors_frobenius <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.pow_one_pow_two_commutation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.pow_two_symplectic_relation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.pow_one_series_p_formula : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p <;> assumption)
end
