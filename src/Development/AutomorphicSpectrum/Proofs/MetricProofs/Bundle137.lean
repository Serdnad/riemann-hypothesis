module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle128
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeights
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle014
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle127
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle129
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle076
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle024
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle006
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

open GlobalTheory.CompanionTheory.Ar.TiePrimes (dh mem_coord_iff homog_X eval₂_eq_dh_mul exists_form aeval_eq_dh_mul adjoin_eq
  mem_Wp_iff regAt_iff)

theorem exists_point_of_prime : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  intro Sc Ω _ ξ K _ J _ y tie W hWp hPW c hcX
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))
  have hx : seg y c ≠ 0 := GlobalTheory.CompanionTheory.Ar.TiePrimes.seg_ne hc
  haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W
  let F := FractionRing (MRing J ⧸ W)
  let y' : (Σ k, J k) → F := fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (MvPolynomial.X q))
  have ae : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f =
      algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f) := by
    intro f
    have e : MvPolynomial.eval₂Hom (Int.castRingHom F) y' =
        (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W) :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])
    exact RingHom.congr_fun e f
  have hzero : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W := by
    intro f
    rw [ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]
  have hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k ((hzero _).1 (by simpa using h0))
  have memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0) := by
    intro g d hg
    have h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]
  let A := Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)
  have hdhA : ∀ f, dh y c f ∈ A := fun f => by
    show dh y c f ∈ Algebra.adjoin ℤ _
    rw [adjoin_eq hc]
    exact ⟨f, rfl⟩
  let φ : MRing J →+* A := ((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom
  have hφ : ∀ f, ((φ f : A) : Ω) = dh y c f := fun f => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ (dh y c).range := by
      rw [← adjoin_eq hc]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, Subtype.ext rfl⟩
  let Q : Ideal (MRing J) := RingHom.ker (dh y' c : MRing J →+* F)
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker φ ≤ Q := by
    intro f hf
    have hf0 : dh y c f = 0 := by
      rw [← hφ, RingHom.mem_ker.1 hf]
      rfl
    obtain ⟨D, G, hG, e⟩ := exists_form c f
    have e₁ : dh y c G = dh y c f := e Ω _ fun k => div_self (hc k)
    have e₂ : dh y' c G = dh y' c f := e F _ fun k => div_self (hc' k)
    have hGP : G ∈ W := hPW ((mem_coord_iff y hG).2 (by
      rw [aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))
    show dh y' c f = 0
    rw [← e₂]
    exact (memW G D hG).1 hGP
  let I : Ideal A := Q.map φ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨p, ⟨hin, hunit⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point Sc Ω ξ ℤ _ (seg y) tie c hx I hI
  have hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q := by
    intro g
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩
    obtain ⟨x, hx', e⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 h
    have : g - x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 := Q.add_mem (hker this) hx'
    simpa using h2
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d →
      (g ∈ GlobalTheory.CompanionTheory.Ar.TiePrimes.Wp tie p ↔ g ∈ W) := by
    intro g d hg
    rw [mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]
    rfl
  refine ⟨p, hin, fun a ha => ?_⟩
  obtain ⟨d, g, h, hg, hh, hW, e⟩ := (regAt_iff tie p a).1 ha
  exact ⟨d, g, h, hg, hh, fun hm => hW ((key h d hh).2 hm), e⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_unit_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk
  obtain rfl := Option.some.inj hk
  exact BlockEmbeddings.det_fMat_eq A r.1 (stepOf Ψ p q r)
    (BlockEmbeddings.stepOf_fst r) _ (BlockEmbeddings.mem_stepCols_iff r) i
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_minor_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.model_dy_weights : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.FlagTie

theorem flagCoord_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_tie

end GlobalTheory.CompanionTheory.Ar.FlagTie
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.hodgeCpt_morphism_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver | exact GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.flag_variety_boundary_dimension_drop : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | exact GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image <;> assumption)
end

section


theorem _root_.GlobalTheory.T.local_orbit_chart_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.LocalOrbitChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | exact GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem push_chart_integrals : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → (∀ j, AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (volume.restrict (M.atlas.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) volume ∧ (∀ Pt : ChartPartition M.atlas, ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w|) = ∑ j, ∫⁻ u in (M.atlas.chart j).target, ENNReal.ofReal |Pt.χ j ((M.atlas.chart j).symm u) * G₀ ((M.atlas.chart j).symm u) * locDens M.atlas (Φ) j u|) ∧ (MIntegrable M.atlas Φ G₀ → Integrable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) ∧ ptsIntegralAt P Q (fun i z => c i * Real.log ((B i).h z)) g = mInt M.atlas Φ G₀) := by
  intro K _ ι _ P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg hG
  have hS : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelBad M Q (Yᶜ ∪ Z)) = 0 := by
    intro j
    rw [modelBad, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (hnull j) (GlobalTheory.T.volume_modelCrit_chart_eq_zero K ι P n M Q j hP hQ)
  have hq := modelQ_good_of_notMem M Q (Yᶜ ∪ Z)
  have hfin : ∀ y, (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)).Finite := fun y =>
    (ModelFibreFinite.proof K ι P n M Q hP hQ y).subset (Set.sdiff_subset_sdiff_right Set.subset_union_right)
  have hYof : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), x ∈ Y := fun x hx => by
    by_contra h
    exact hx (Or.inl (Or.inl h))
  have hsm : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), ∀ i k, x ∈ (M.atlas.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) := by
    intro x hx i k hk
    have hxk : (M.atlas.chart k).symm (M.atlas.chart k x) = x := (M.atlas.chart k).left_inv hk
    have hmem : M.atlas.chart k x ∈ (M.atlas.chart k).target ∩ (M.atlas.chart k).symm ⁻¹' ((Φ i).U x ∩ Y) :=
      ⟨(M.atlas.chart k).map_source hk, by
        rw [Set.mem_preimage, hxk]; exact ⟨(Φ i).mem_U x, hYof x hx⟩⟩
    have hop := (M.atlas.chart k).isOpen_inter_preimage_symm (((Φ i).isOpen_U x).inter hY)
    exact ((hΦs i x k).contDiffAt (hop.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  have hYnull : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Yᶜ) = 0 := fun j =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.subset_union_left)) (hnull j)
  have hm : ∀ j, AEStronglyMeasurable (fun u => G₀ ((M.atlas.chart j).symm u) * locDens M.atlas Φ j u)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    let _ : MeasurableSpace M.Xc := borel M.Xc
    have : BorelSpace M.Xc := ⟨rfl⟩
    refine AEStronglyMeasurable.mul (hG j) ?_
    rw [MeasOff.restrict_target_eq M.atlas hYnull j]
    exact ((GlobalTheory.T.smooth_local_potential_lift K ι P n M Y c B Φ j hY hΦs hΦt).aestronglyMeasurable
      (MeasOff.isOpen_ov M.atlas hY j).measurableSet)
  have hae := GlobalTheory.T.chart_integral_potential_locally_finite K ι P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg
  have e1 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl ht
  have e2 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w| =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), |G₀ x * pushDens M.atlas Φ (modelQ M Q) x| := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl fun x hx => by rw [ht x hx]
  refine ⟨(GlobalTheory.T.measurable_fibre_count_of_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm).congr (e1.mono fun y hy => hy.symm),
    fun Pt => ?_, fun hI => ?_⟩
  · rw [lintegral_congr_ae (e2.mono fun y hy => congrArg ENNReal.ofReal hy)]
    exact GlobalTheory.T.finite_fibres_of_analytic_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm Pt
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_fibre_sum_change_of_variables M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hI
    refine ⟨h1.congr (e1.mono fun y hy => hy.symm), ?_⟩
    rw [h2]
    exact integral_congr_ae (e1.mono fun y hy => hy)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

set_option maxSynthPendingDepth 1
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem cuspWeight_descends :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
      [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
      [Module O Lt] (X : ComponentSetting D O Lt),
      ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧
        (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, C', hC⟩ := CuspWeightIntegrable.uFn_bound X
  letI : MeasurableSpace X.M.Xc := borel X.M.Xc
  haveI : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ⟨fun x => 2 * CuspWeightIntegrable.uFn X x, 2 * max C C', ?_, ?_, ?_⟩
  · exact ((CuspWeightIntegrable.measurable_uFn X).const_mul 2).indicator X.S.R.isOpen_Yo.measurableSet
  · intro x hx
    have h1 := hC x hx
    have hl := Real.log_nonneg (X.S.R.one_le_r x hx)
    have h2 : C' * Real.log (X.S.R.r x) ≤ max C C' * Real.log (X.S.R.r x) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hl
    have h3 : C ≤ max C C' := le_max_left _ _
    rw [abs_mul, abs_two]
    nlinarith
  · intro z hz hy
    have hzB : z ∉ D.Bd := by
      intro hB
      obtain ⟨z0, ⟨hz0X, hz0m⟩, hp⟩ := X.S.Yo_sub _ hy
      obtain ⟨c, hc, rfl⟩ := (X.M.fibre z hz z0 hz0m).1 hp.symm
      exact hz0X.2 (D.bd_torus z hB c hc)
    have := CuspWeightIntegrable.cuspWeight_eq X hz hzB hy
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end
