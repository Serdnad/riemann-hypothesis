module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle257
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle181
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle171
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle174
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle262
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
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arMix_of_base_int : (∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h → ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧ Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr) → GlobalTheory.Published.ArMix := by
  intro H k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  haveI := hX.finite
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hX' : IsArithVar t D := isArithVar_int k X p t D hX
  have Hc : ∀ (N : HermLB p) (τ : ℤ →+* ℂ), (wZ N t τ).IsCInf := fun N τ => GlobalTheory.T.wZ_isCInf' k X p t N τ
  have hΦ' : IsArFun (fun o : Option ι => o.elim (toZ M t (Hc M)) fun i => toZ (L i) t (Hc (L i))) D Φ := by
    have e := (GlobalTheory.T.toZ_isArFun_iff k X p t D hX (Option ι) (fun o : Option ι => o.elim M L)
      (fun o => Hc _) Φ).2 hΦ
    convert e using 2 with o
    cases o <;> rfl
  have iso : (toZ (comb L n) t (Hc _)).Isometric (comb (fun i => toZ (L i) t (Hc (L i))) n) :=
    (GlobalTheory.T.toZ_pow_comb_isometric k X p t Hc).2 ι L n
  have hh' : (comb (fun i => toZ (L i) t (Hc (L i))) n).IsArithHeight h :=
    iso.isArithHeight hX' ((GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (Hc _) h).2 hh)
  obtain ⟨h₁, h₂⟩ := H X t D hX' ι (toZ M t (Hc M)) (fun i => toZ (L i) t (Hc (L i))) Φ hΦ' n h hh' r hr
  have hA : (toZ (comb L n) t (Hc _)).ArchIntegrable (toZ M t (Hc M)) D hr := fun τ => by
    rw [iso.chernIntegrableOn_eq]
    exact h₁ τ
  have hI : (comb (fun i => toZ (L i) t (Hc (L i))) n).archInt (toZ M t (Hc M)) D hr =
      (toZ (comb L n) t (Hc _)).archInt (toZ M t (Hc M)) D hr := by
    simp only [HermLB.archInt, iso.chernInt_eq]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archInt_toZ_eq k X p t D hX (comb L n) M (Hc _) (Hc _) D r hr
  have hB := e₁.1 hA
  refine ⟨hB, h₂.trans ?_⟩
  rw [hI, e₂ hB]
  rfl

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arFormExists_of_int :
    (∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D →
      ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ) → GlobalTheory.Published.ArFormExists := by
  intro H k _ X _ p D hX ι _ L
  let t : X ⟶ Sp ℤ := specZIsTerminal.from X
  haveI : Module.Finite ℤ k := hX.finite
  have hL : ∀ i τ, (wZ (L i) t τ).IsCInf := fun i τ => GlobalTheory.T.wZ_isCInf' k X p t (L i) τ
  obtain ⟨Φ, hΦ⟩ := H X t D (GlobalTheory.CompanionTheory.Ar.BaseZ.isArithVar_int k X p t D hX) ι
    (fun i => GlobalTheory.CompanionTheory.Ar.BaseZ.toZ (L i) t (hL i))
  exact ⟨Φ, (GlobalTheory.T.toZ_isArFun_iff k X p t D hX ι L hL Φ).1 hΦ⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem or_m1nef : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.ModelNefStatement := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ _ _ B a p hp mu hmu
  have hF : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hS : p ∈ o.S B := (o.S_iff B p).2 hp
  exact GlobalTheory.T.root_lines_weight_bound_of_free hF E H D l (Xo l) c _ _ Y (o.S B) (T.M B a) (o.Or B a).𝔐 (o.Or B a).Fl (o.Or B a).e p hS
    (o.omVB B a p hS) (o.Or B a).lines mu hmu

end GlobalTheory.CompanionTheory.Ar.Top
end
