module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle053
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle041
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantValueCopiesEqZeroOfLowCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle030
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  first | exact @GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | exact GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | (intros; apply GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_mono {R : Type} [CommRing R] {I : Ideal R} {k l : ℕ} (hkl : k ≤ l) {S : Type} [CommRing S]
    [Algebra R S] (h : Kills I k S) : Kills I l S :=
  fun t ht => h t (Ideal.pow_le_pow_right (by omega) ht)

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Out.UnifPre I D A G) (S : Type) [CommRing S] [Algebra R S]

private theorem qRel_mono {k l : ℕ} (hkl : k ≤ l) {z y} (h : QRel (U.gt k) S z y) : QRel (U.gt l) S z y := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.ChF.qRel_succ R I D A G U n S z y ih

private theorem iRel_mono {k l : ℕ} (hkl : k ≤ l) {χ z} (h : IRel (U.gt k) S χ z) : IRel (U.gt l) S χ z := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.T.torus_point_relation_succ_thickening R I D A G U n S χ z ih

private def qFun (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) : sp (R₀ := R) S ⟶ D.toPre.P.A :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose

private theorem qFun_spec (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) :
    QRel (U.gt h.choose) S z (qFun U S h z) :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose_spec

private theorem qFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {z y} (hq : QRel (U.gt k) S z y) : qFun U S h z = y :=
  (((qRel_existsUnique_mul_nat R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 z).unique
    (qRel_mono U S (le_max_left _ _) (qFun_spec U S h z)) (qRel_mono U S (le_max_right _ _) hq)

private def iFun (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) : sp (R₀ := R) S ⟶ G :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose

private theorem iFun_spec (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) :
    IRel (U.gt h.choose) S χ (iFun U S h χ) :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose_spec

private theorem iFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {χ z} (hq : IRel (U.gt k) S χ z) : iFun U S h χ = z :=
  (((GlobalTheory.irel_points R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 χ).unique
    (iRel_mono U S (le_max_left _ _) (iFun_spec U S h χ)) (iRel_mono U S (le_max_right _ _) hq)

end

private def ptExt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Out.UnifPre I D A G) : PtExt I G D.toPre.P.A D.toPre.X where
  q S _ _ h := MonoidHom.mk' (qFun U S h) fun z z' => qFun_eq U S h
    (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2 _ _ _ _
      (qFun_spec U S h z) (qFun_spec U S h z'))
  i S _ _ h := MonoidHom.mk' (iFun U S h) fun χ χ' => iFun_eq U S h
    (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.1 _ _ _ _
      (iFun_spec U S h χ) (iFun_spec U S h χ'))
  q_nat S _ _ S' _ _ φ h h' z := qFun_eq U S' h'
    ((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (qFun_spec U S h z))
  i_nat S _ _ S' _ _ φ h h' χ := iFun_eq U S' h'
    ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (iFun_spec U S h χ))
  i_inj S _ _ h χ χ' e := by
    have e' : iFun U S h χ = iFun U S h χ' := e
    exact ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.2 _ _ _
      (iFun_spec U S h χ) (e' ▸ iFun_spec U S h χ')
  exact S _ _ h z := by
    have key := GlobalTheory.T.thickeningQuotientImage_one_iff_exists_torusImage R I _ h.choose G (U.gt h.choose) S h.choose_spec z
    constructor
    · intro e
      have e' : qFun U S h z = 1 := e
      obtain ⟨χ, hχ⟩ := key.1 (e' ▸ qFun_spec U S h z)
      exact ⟨χ, iFun_eq U S h hχ⟩
    · rintro ⟨χ, e⟩
      have e' : iFun U S h χ = z := e
      exact qFun_eq U S h (key.2 ⟨χ, e' ▸ iFun_spec U S h χ⟩)
  lift S _ _ h S' _ _ ρ σ h1 h2 y hy := by
    obtain ⟨z, hz, hq⟩ := GlobalTheory.T.abelianPart_lift_square_zero_unit_point R I _ h.choose G (U.gt h.choose) S h.choose_spec S' ρ σ h1 h2 y hy
    exact ⟨z, hz, qFun_eq U S h hq⟩

theorem exists_ptExt_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∃ E : PtExt I G D.toPre.P.A D.toPre.X, ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (a : OE) (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S), (∀ z, E.q S h (z ≫ io.act a) = E.q S h z ≫ oD.onB.act a) ∧ ∀ χ χ', (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → E.i S h χ ≫ io.act a = E.i S h χ' := by
  intro R _ _ I D A G _ _ U
  refine ⟨ptExt U, ?_⟩
  intro OE _ _ _ io oD oA hL a S _ _ h
  have key := qRel_iRel_equivariant R I D A G U OE io oD oA hL h.choose a S
  refine ⟨fun z => qFun_eq U S h (key.1 _ _ (qFun_spec U S h z)), fun χ χ' e => ?_⟩
  exact (iFun_eq U S h (key.2 _ _ _ e (iFun_spec U S h χ))).symm

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_linearData_of_split_formalGroup_extension : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  first | exact @GlobalTheory.ChF.exists_linDat_of_extSer | exact GlobalTheory.ChF.exists_linDat_of_extSer | (intros; apply GlobalTheory.ChF.exists_linDat_of_extSer <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.PairCount

theorem pair_kernel_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a' : ZMod d), ¬ X.big g a' → ∀ U' : Fin X.n → I (1 - g) → C, X.SatIn (1 - g) a' U' → ∀ (N : ℕ) (ψ : Fin N → J g → C), (∀ ν κ, V.Ge 0 (ψ ν κ)) → (∀ ν κ, (X.G g).ty (Sum.inr κ) ≠ a' → ψ ν κ = 0) → IndepMod V ψ → (∀ ν b, V.MM (∑ κ : J g, ∑ k : I (1 - g), ψ ν κ * X.pair g κ k * U' b k)) → N ≤ X.j := by
  intro C _ V d _ I J _ _ X g a' hs U' hU N ψ _ hp hind hk
  obtain ⟨s, hsi, hs1⟩ := X.pair_onto g
  have h := GlobalTheory.RowKernel.card_add_le (V := V) (fun k : I (1 - g) => (X.G (1 - g)).ty (Sum.inl k) = a')
    (fun ν k => ∑ κ, ψ ν κ * X.pair g κ k) U' ?_ ?_ hU.1 (fun μ k hk => hU.2 μ k hk) ?_
  · have h2 := X.rk_big (1 - g) a' ((X.big_compl g a').2 hs)
    have h3 : N + X.n ≤ X.n + X.j := by
      rw [← h2]
      convert h
    omega
  · intro c hc hm
    refine hind c hc fun κ' => ?_
    have e : ∑ ν, c ν * ψ ν κ' = ∑ k, (∑ ν, c ν * ∑ κ, ψ ν κ * X.pair g κ k) * s k κ' := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have e1 : ψ ν κ' = ∑ κ, ψ ν κ * ∑ k, X.pair g κ k * s k κ' := by
        simp [hs1]
      rw [e1]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => by ring
    rw [e]
    exact GlobalTheory.RowKernel.mm_sum fun k _ => GlobalTheory.RowKernel.mm_mul_int (hm k) (hsi k κ')
  · intro ν k hk'
    refine Finset.sum_eq_zero fun κ _ => ?_
    by_cases hκ : (X.G g).ty (Sum.inr κ) = a'
    · rw [X.pair_type g κ k (fun h => hk' (h ▸ hκ)), mul_zero]
    · rw [hp ν κ hκ, zero_mul]
  · intro ν μ
    have h := hk ν μ
    rw [Finset.sum_comm] at h
    simpa only [Finset.sum_mul] using h

end GlobalTheory.PairCount
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), HasProj (Y.rawSelf p) V := by
  first | exact @GlobalTheory.ProjSelf.hasProj_self | exact GlobalTheory.ProjSelf.hasProj_self | (intros; apply GlobalTheory.ProjSelf.hasProj_self <;> assumption)
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

theorem _root_.GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  first | exact @GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | exact GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | (intros; apply GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.TangentCob

section Schemes
variable {X Y : Scheme.{0}}

theorem top_le_stalk_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) :
    ⊤ ≤ (Y.fromSpecStalk y ≫ f) ⁻¹ᵁ U ↔ f y ∈ U := by
  refine (top_le_iff_cpt (A := Y.presheaf.stalk y) _ U).trans ?_
  rw [Scheme.Hom.comp_apply,
    show Y.fromSpecStalk y (cpt (Y.presheaf.stalk y)) = y from Scheme.fromSpecStalk_closedPoint]

theorem valR_stalk (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    valR (A := Y.presheaf.stalk y) (Y.fromSpecStalk y ≫ f) U a = gs f y U a := by
  rw [gs_eq f y U h]
  exact (GlobalTheory.HolHom.valR_comp (A := Y.presheaf.stalk y) _ f U a).trans
    (GlobalTheory.FormalValue.valR_fromSpecStalk y (f ⁻¹ᵁ U) h _)

theorem exists_unit (p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (U : X.Opens) (a : Γ(X, U)) :
    ∃ u : Γ(Y, p ⁻¹ᵁ U)ˣ, ∀ y, p y ∈ U →
      (gm (𝟙 Y) y (p ⁻¹ᵁ U) u).val = 1 + gs (𝟙 Y) y ⊤ e * gs p y U a := by
  let e' : Γ(Y, p ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op).hom e
  have he' : e' * e' = 0 := by rw [← map_mul, he, map_zero]
  let b : Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom a
  refine ⟨⟨1 + e' * b, 1 - e' * b, by linear_combination (-(b * b)) * he', by linear_combination (-(b * b)) * he'⟩,
    fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ U := hy
  rw [← gs_unit _ y _ hy']
  show gs (𝟙 Y) y (p ⁻¹ᵁ U) (1 + e' * b) = _
  rw [gs_add _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_pull (𝟙 Y) p y U hy, Category.id_comp,
    gs_eq _ y _ hy', map_one, map_one]

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] {a b c d f g u v : G} (h : a * v = b * u) (h₁ : c * d = f)
    (h₂ : g * a = f) : g * u = c ^ (1 : ℤ) * b ^ (-1 : ℤ) * (d * v) := by
  rw [zpow_one, zpow_neg, zpow_one, _root_.mul_mul_mul_comm, h₁, ← h₂, _root_.mul_assoc, _root_.mul_left_comm a,
    h, inv_mul_cancel_left]

theorem exists_isGen (L : LB X) (hL : L.IsLB) (m p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (H : ∀ j, Γ(X, L.U j))
    (hmp : ∀ (y : Y) (U : X.Opens), p y ∈ U → m y ∈ U)
    (h : ∀ (y : Y) (j j' : L.ι), p y ∈ L.U j → p y ∈ L.U j' → gs m y (L.U j ⊓ L.U j') (L.g j j').val =
      gs p y (L.U j ⊓ L.U j') (L.g j j').val *
        (1 + gs (𝟙 Y) y ⊤ e * (gs p y (L.U j) (H j) - gs p y (L.U j') (H j')))) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![m, p] ![1, -1]), c.IsGen := by
  choose u hu using fun j => exists_unit p e he (L.U j) (H j)
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → m y ∈ L.U (j 0) :=
    fun j y hy => LB.wchart_le L ![m, p] j 0 hy
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → p y ∈ L.U (j 1) :=
    fun j y hy => LB.wchart_le L ![m, p] j 1 hy
  let s : ∀ j : Fin 2 → L.ι, Γ(Y, LB.wchart L ![m, p] j)ˣ := fun j =>
    res (show LB.wchart L ![m, p] j ≤ m ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) from
      fun y hy => ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩) (pullU m _ (L.g (j 0) (j 1))) *
    res (show LB.wchart L ![m, p] j ≤ p ⁻¹ᵁ L.U (j 1) from fun y hy => h1 j y hy) (u (j 1))
  have hs : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → gm (𝟙 Y) y _ (s j) =
      gm m y _ (L.g (j 0) (j 1)) * gm (𝟙 Y) y _ (u (j 1)) := fun j y hy => by
    have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j := hy
    rw [map_mul, gm_res _ y _ hy', gm_res _ y _ hy',
      gm_pull (𝟙 Y) m y (L.U (j 0) ⊓ L.U (j 1)) ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩, Category.id_comp]
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j ⊓ LB.wchart L ![m, p] j' := hy
  refine ((gm_res _ y _ hy' _).trans (hs j y hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L ![m, p] ![1, -1] (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy' _).trans (hs j' y hy.2)))).symm)
  have a0 := h0 j y hy.1
  have a1 := h1 j y hy.1
  have b0 := h0 j' y hy.2
  have b1 := h1 j' y hy.2
  have key : gm m y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j' 1)) =
      gm p y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j 1)) := by
    apply Units.ext
    have hee : gs (𝟙 Y) y ⊤ e * gs (𝟙 Y) y ⊤ e = 0 := by
      rw [← gs_mul (𝟙 Y) y ⊤ trivial, he, gs_eq (𝟙 Y) y ⊤ trivial, map_zero, map_zero]
    rw [Units.val_mul, Units.val_mul, hu _ y a1, hu _ y b1, ← gs_unit m y (L.U (j 1) ⊓ L.U (j' 1)) ⟨hmp y _ a1, hmp y _ b1⟩,
      ← gs_unit p y (L.U (j 1) ⊓ L.U (j' 1)) ⟨a1, b1⟩, h y _ _ a1 b1]
    linear_combination (gs p y (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val *
      (gs p y (L.U (j 1)) (H (j 1)) - gs p y (L.U (j' 1)) (H (j' 1))) * gs p y (L.U (j' 1)) (H (j' 1))) * hee
  have c1 := gm_cocycle hL m y a0 b0 (hmp y _ b1)
  have c2 := gm_cocycle hL m y a0 (hmp y _ a1) (hmp y _ b1)
  rw [Fin.prod_univ_two]
  exact commGroup_coboundary_relation_identity key c1 c2

end Schemes

variable {k : Type} [CommRing k] {B : Over (Sp k)}

theorem exists_alg (D : Type) [CommRing D] [Algebra k D] {S : Type} [CommRing S] (r : Sp S ⟶ (algOver k D ⊗ B).left) :
    ∃ (_ : Algebra k S) (φ : D →ₐ[k] S) (r' : algOver k S ⟶ algOver k D ⊗ B), r'.left = r ∧
      r' ≫ fst _ _ = algOverHom φ ∧ ∀ d : D, φ d =
        valR (r ≫ (fst (algOver k D) B).left) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of D) (S := CommRingCat.of S) (r ≫ (fst (algOver k D) B).left)
  letI : Algebra k S := (ψ.hom.comp (algebraMap k D)).toAlgebra
  refine ⟨this, ⟨ψ.hom, fun _ => rfl⟩, Over.homMk r ?_, rfl, Over.OverMorphism.ext hψ.symm, fun d => ?_⟩
  · rw [← Over.w (fst (algOver k D) B), ← Category.assoc]
    erw [← hψ]
    exact (Spec.map_comp _ _).symm
  · erw [← hψ]
    have := GlobalTheory.HolHom.valR_spMap ψ.hom (𝟙 (Sp D)) ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d)
    rw [Category.comp_id, GlobalTheory.HolHom.valR_eq (𝟙 (Sp D)) ⊤ le_top] at this
    refine Eq.trans ?_ this.symm
    refine congrArg ψ.hom ?_
    simp [GlobalTheory.HolHom.evalHom, Scheme.Hom.appLE]

end GlobalTheory.TangentCob

namespace GlobalTheory
open TangentCob

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.IntegralColumnGerm

theorem prod_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) {ι : Type} [Fintype ι] (α : ι → R)
    (hα : ∀ l, α l - 1 ∈ I) (n : ι → ℕ) : ∏ l, α l ^ n l - 1 ∈ I := by
  rw [← Ideal.Quotient.eq, map_prod, map_one]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [map_pow, Ideal.Quotient.eq.2 (hα l), map_one, one_pow]

theorem exists_eq_of_unit_mul {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) (I : Ideal R) {P x y : R}
    {v : k} (hP : IsUnit P) (hP1 : P - 1 ∈ I) (hxy : x - y ∈ I) (h : φ P * v = φ x) :
    ∃ r ∈ I, v = φ (y + r) := by
  obtain ⟨Q, hQ⟩ := hP.exists_left_inv
  refine ⟨Q * ((x - y) - (P - 1) * y), I.mul_mem_left _ (I.sub_mem hxy (I.mul_mem_right _ hP1)), ?_⟩
  have e : y + Q * ((x - y) - (P - 1) * y) = Q * x := by linear_combination (-y) * hQ
  rw [e, map_mul, ← h, ← mul_assoc, ← map_mul, hQ, map_one, one_mul]

end GlobalTheory.IntegralColumnGerm

namespace GlobalTheory

open IntegralColumnGerm

theorem exists_integral_germ_nabVal_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by
  intro hS hL R _ d O _ _ k _ _ _ B h hh hinj w0 a c N m I hac hN ι _ u α hα1 hαu hα hβ χ
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : ∀ w : O, constantCoeff (B.hL k h w) = 0 := fun w =>
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w) (gp_pt 0))) h hh0
  have e0 : star a * (w0 * a) = (N : O) * (c * w0) := by linear_combination w0 * hac
  have h1 := FramePull.expIntegral_ad hh a 1 (w0 * a)
  rw [e0, mul_one, ← FramePull.ev_actK_hL, ← FramePull.hL_eq] at h1
  obtain ⟨cD, υ, υ1, hυ⟩ := h1
  have hinv : υ * invOfUnit υ 1 = 1 := mul_invOfUnit υ 1 (by simpa using υ1)
  obtain ⟨g, hg⟩ : ∃ g : PS R 1 d, g * υ ^ m = χ :=
    ⟨χ * invOfUnit υ 1 ^ m, by rw [mul_assoc, ← mul_pow, mul_comm _ υ, hinv, one_pow, mul_one]⟩
  refine ⟨g, fun mo => ?_⟩
  have hga : FB.toK k (ev (n := 1) ![B.A.act a] g) = ev (n := 1) ![B.actK k a] (FB.toK k g) := by
    rw [FB.toK, QuadDeriv.map_ev _ _ (single_point_zero_constant (B.A.const a))]
    congr 1
    funext j; fin_cases j; rfl
  have hG : ev (n := 1) ![B.actK k a] (FB.toK k g * FB.expS k ((m : k) • B.hL k h w0)) =
      FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) *
        FB.expS k ((m : k) • B.hL k h ((N : O) * (c * w0))) := by
    have e : FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) =
        FB.toK k (ev (n := 1) ![B.A.act a] g) * FB.toK k υ ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hga, hυ, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, sub_add_cancel]
  have hend := (invariantDeriv_along_endo R d O k B a).2 ι (fun l i => algebraMap R k (u l i))
    (fun l => algebraMap R k (α l)) hα
  have hmap : ∀ (mo : ι →₀ ℕ) (f : PS R 1 d),
      constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (FB.toK k f)) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo f)) := fun mo f => by
    rw [← constantCoeff_map, map_dmonOf]
    rfl
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • B.hL k h ((N : O) * (c * w0)))) = algebraMap R k r := by
    intro mo
    obtain ⟨t, ht⟩ := hS R d O k B h hh (c * w0) N ι u hβ mo
    refine ⟨(m : R) * (N * t), I.mul_mem_left _ (I.mul_mem_right _ hN), ?_⟩
    rw [smul_eq_C_mul, GE.dmonOf_Cmul, map_mul, constantCoeff_C, ht, map_mul (algebraMap R k) (m : R),
      map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cL, mul_zero]) hφ (ev (n := 1) ![B.A.act a] g * υ ^ m) mo
  have hcong : ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) -
      constantCoeff (DmonOf B.G.F u mo g) ∈ I := by
    intro mo
    have e1 : constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) =
        (∏ l, α l ^ mo l) * constantCoeff (DmonOf B.G.F u mo g) := by
      apply hinj
      rw [← hmap, hga, hend, hmap]
      simp only [map_mul, map_prod, map_pow]
    rw [e1, ← sub_one_mul]
    exact I.mul_mem_right _ (prod_pow_sub_one_mem I α hα1 mo)
  have hleib := hL R d B.G.F I ι u _ _ (υ ^ m) hcong mo
  rw [hg] at hleib
  refine exists_eq_of_unit_mul (algebraMap R k) I (P := ∏ l, α l ^ mo l)
    (x := constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g * υ ^ m)) + r)
    (IsUnit.prod_univ_iff.2 fun l => (hαu l).pow _) (prod_pow_sub_one_mem I α hα1 mo) ?_ ?_
  · rw [add_sub_right_comm]
    exact I.add_mem hleib hr
  · unfold FB.nabVal
    rw [PullbackColumn.dpolyOf_monomial_one, ← e]
    simp only [map_prod, map_pow]
    rw [← hend, hG]
    rfl

end GlobalTheory
end
end
