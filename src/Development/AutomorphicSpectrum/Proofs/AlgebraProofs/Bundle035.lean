module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.FunctionField.DivisorDegree
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import GroundTheory.FunctionField.Divisor
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.BilCalc

theorem bil_calc : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 :=
  @PositivityTheory.HtPt.Ca.bil_calc

end GlobalTheory.CompanionTheory.Ar.Conj.BilCalc
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.NatAct

theorem act_nat_iterated : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) :=
  @PositivityTheory.HtPt.Ca.act_zero

end GlobalTheory.CompanionTheory.Ar.Conj.NatAct
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eig_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) :=
  PositivityTheory.HtPt.Ci.eig_frob

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

noncomputable section

open GroundTheory.FunctionField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isFunctionField_of_fg_trdeg {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    (hfg : (⊤ : IntermediateField k κ).FG) (htr : Algebra.trdeg k κ = 1) :
    IsFunctionField k κ := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hcard : Cardinal.mk s = 1 := by rw [hs.cardinalMk_eq_trdeg, htr]
  obtain ⟨⟨x, hx⟩⟩ : Nonempty s := by
    rw [← Cardinal.mk_ne_zero_iff, hcard]
    exact one_ne_zero
  have hsx : s = {x} := by
    have hsub : Subsingleton s := by
      rw [← Cardinal.le_one_iff_subsingleton, hcard]
    ext y
    constructor
    · intro hy
      have := Subsingleton.elim (⟨y, hy⟩ : s) ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    · rintro rfl
      exact hx
  have htrx : Transcendental k x := hs.1.transcendental ⟨x, hx⟩
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) κ := by
    have := hs.isAlgebraic_field
    rwa [Subtype.range_coe, hsx] at this
  obtain ⟨t, ht⟩ := hfg
  have hfd : ∀ F : IntermediateField k κ, Algebra.IsAlgebraic F κ → FiniteDimensional F κ := by
    intro F hF
    have hle : IntermediateField.adjoin k (↑t : Set κ) ≤
        (IntermediateField.adjoin F (↑t : Set κ)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have htop : IntermediateField.adjoin F (↑t : Set κ) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin k (↑t : Set κ) := by
        rw [ht]
        exact IntermediateField.mem_top
      exact hle hy
    have h1 : FiniteDimensional F (IntermediateField.adjoin F (↑t : Set κ)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ => (hF.isAlgebraic y).isIntegral
    rw [htop] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  exact ⟨⟨x, htrx, hfd _ halg⟩⟩

section

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsFunctionField k κ]

def placesCurve : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ where
  I := Place k κ
  v := fun i => i.valuation
  w := fun i => i.deg
  fin := fun x hx => by
    refine (Place.finite_ord_ne_zero (k := k) x).subset fun i hi h0 => hi ?_
    have h := i.valuation_eq_exp_neg_ord hx
    rw [h, h0]
    simp
  prod := fun x hx => by
    classical
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_eq_sum] at h
    rw [finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k κ).support)]
    · have : ∑ i ∈ (divisor x : Divisor k κ).support,
          ((i.deg : ℤ) * WithZero.log (i.valuation x)) =
          - ∑ i ∈ (divisor x : Divisor k κ).support, (divisor x : Divisor k κ) i * (i.deg : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [divisor_apply, Place.ord]
        ring
      rw [this, h, neg_zero]
    · intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, divisor_apply, Place.ord]
      intro h0
      apply hi
      have : WithZero.log (i.valuation x) = 0 := by omega
      rw [this, mul_zero]

end

theorem exists_curve_of_function_field :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ], (⊤ : IntermediateField k κ).FG →
      Algebra.trdeg k κ = 1 → ∃ C : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ, (∀ i, 0 < C.w i) ∧
        (∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1) ∧
        (∀ i, Function.Surjective (C.v i)) ∧
        ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) →
          ∃! i, (C.v i).valuationSubring = W := by
  intro k κ _ _ _ hfg htr
  haveI : IsFunctionField k κ := isFunctionField_of_fg_trdeg hfg htr
  have key : ∀ i : Place k κ, (i.valuation).valuationSubring = i.ring := fun i => by
    ext y
    rw [Valuation.mem_valuationSubring_iff]
    exact Place.valuation_le_one_iff i y
  refine ⟨placesCurve k κ, fun i => ?_, fun i a ha => ?_, fun i => ?_, fun W hW hk => ?_⟩
  · exact Place.deg_pos i
  · exact Place.valuation_algebraMap' i ha
  · exact Place.valuation_surjective i
  · refine ⟨⟨W, hW, hk⟩, key _, fun j hj => ?_⟩
    exact Place.ext ((key j).symm.trans hj)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.EigDual

theorem eig_dual_deg : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) :=
  PositivityTheory.HtPt.Ci.eig_dual

end GlobalTheory.CompanionTheory.Ar.Crv.EigDual
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | exact GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top | exact GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_length : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | exact GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

theorem _root_.GlobalTheory.T.local_comparison_of_orbits_holds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | exact GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem unitRatio_divisor_cycle_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W :=
  @PositivityTheory.UnitarySelfGeneration.i_cycle

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twisted_module_finite_projective_rank : ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L], Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧ Module.finrank O (TwMod s L) = Module.finrank O L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | exact GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem exists_iso_of_effectiveEpi {T Y₁ Y₂ : Scheme.{0}} (q₁ : T ⟶ Y₁) (q₂ : T ⟶ Y₂)
    [EffectiveEpi q₁] [EffectiveEpi q₂]
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ T), g₁ ≫ q₁ = g₂ ≫ q₁ ↔ g₁ ≫ q₂ = g₂ ≫ q₂) :
    ∃ e : Y₁ ≅ Y₂, q₁ ≫ e.hom = q₂ := by
  let f : Y₁ ⟶ Y₂ := EffectiveEpi.desc q₁ q₂ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).1 e
  let g : Y₂ ⟶ Y₁ := EffectiveEpi.desc q₂ q₁ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).2 e
  have hf : q₁ ≫ f = q₂ := EffectiveEpi.fac _ _ _
  have hg : q₂ ≫ g = q₁ := EffectiveEpi.fac _ _ _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_epi q₁, reassoc_of% hf, hg, Category.comp_id]
  · rw [← cancel_epi q₂, reassoc_of% hg, hf, Category.comp_id]

theorem IsChart.exists_isOpenImmersion {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {V V' : X.Opens}
    {q : V.toScheme ⟶ Y} {q' : V'.toScheme ⟶ Y'} (h : IsChart a b V q) (h' : IsChart a b V' q')
    (hle : V' ≤ V) : ∃ k : Y' ⟶ Y, IsOpenImmersion k ∧ q' ≫ k = X.homOfLE hle ≫ q := by
  obtain ⟨D, rfl⟩ := GlobalTheory.T.invariant_open_chart_preimage h V' hle h'.stable
  obtain ⟨hle₂, q'', hc, hq⟩ := GlobalTheory.T.chart_restrict_preimage_open h D
  have := h'.effectiveEpi
  have := hc.effectiveEpi
  obtain ⟨e, he⟩ := exists_iso_of_effectiveEpi q' q'' fun Z g₁ g₂ ↦ by
    rw [h'.comp_eq_iff, hc.comp_eq_iff]
  refine ⟨e.hom ≫ D.ι, inferInstance, ?_⟩
  rw [reassoc_of% he, hq]

theorem exists_common {P X : Scheme.{0}} {a b : P ⟶ X} {U V : X.Opens}
    (hU : HasAffineChart a b U) (hV : HasAffineChart a b V) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W, HasAffineChart a b W ∧ x ∈ W ∧ W ≤ U ∧ W ≤ V := by
  obtain ⟨Y, q, hY, hq⟩ := (hasAffineChart_iff a b U).1 hU
  obtain ⟨D, hD⟩ := GlobalTheory.T.invariant_open_chart_preimage hq (U ⊓ V) inf_le_left (by
    have h1 := hq.stable
    have h2 := hV.1
    ext p
    have h1' := SetLike.ext_iff.1 h1 p
    have h2' := SetLike.ext_iff.1 h2 p
    exact and_congr h1' h2')
  have hx : x ∈ U.ι ''ᵁ (q ⁻¹ᵁ D) := hD ▸ ⟨hxU, hxV⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨D', hD', hm, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := q u) (U := D) hu
  obtain ⟨hW, q', hc, hq'⟩ := GlobalTheory.T.chart_restrict_preimage_open hq D'
  have hle' : U.ι ''ᵁ (q ⁻¹ᵁ D') ≤ U ⊓ V := by
    rw [← hD]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hle hv, rfl⟩
  have : IsAffine D'.toScheme := hD'
  exact ⟨_, (hasAffineChart_iff a b _).2 ⟨_, q', this, hc⟩, ⟨u, hm, rfl⟩, hW, hle'.trans inf_le_right⟩

theorem prop_of_charts (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {X Y' : Scheme.{0}} (π : X ⟶ Y') {J : Type} (V : J → X.Opens)
    (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hcomm : ∀ j, (V j).ι ≫ π = q j ≫ em j)
    (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j) (hsurj : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y)
    (hq : ∀ j, Q (q j)) : Q π := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun j ↦ (em j).opensRange) ?_ fun j ↦ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨j, z, rfl⟩ := hsurj y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, z, rfl⟩
  · refine (Q.arrow_mk_iso_iff (morphismRestrictOpensRange π (em j))).mpr ?_
    have H : IsPullback (q j) (V j).ι (em j) π :=
      IsOpenImmersion.isPullback _ _ _ _ (hcomm j) (by
        rw [Scheme.Opens.opensRange_ι, hpre])
    have e : H.flip.isoPullback.hom ≫ pullback.snd π (em j) = q j := H.flip.isoPullback_hom_snd
    have h' := hq j
    rw [← e] at h'
    exact (Q.cancel_left_of_respectsIso _ _).1 h'

end GlobalTheory.CompanionTheory.FreeQuotGlue


set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  intro P X a b h
  let 𝒰 : Set X.Opens := {V | HasAffineChart a b V}
  have hU (U : 𝒰) := (hasAffineChart_iff a b U.1).1 U.2
  choose Y q hY hq using hU
  let R : X → X → Prop := fun x y ↦ ∃ p : P, a p = x ∧ b p = y
  have hk (U V : 𝒰) (h : U.1 ≤ V.1) := (hq V).exists_isOpenImmersion (hq U) h
  choose k hk hqk using hk
  obtain ⟨Y', π, em, hem, hcomm, hpre, hsurj⟩ := GlobalTheory.T.glue_quotient_charts_cover R 𝒰
    (fun U hU V hV x hx hx' ↦ by
      obtain ⟨W, h1, h2, h3, h4⟩ := exists_common hU hV x hx hx'
      exact ⟨W, h1, h2, h3, h4⟩)
    (fun x ↦ by
      obtain ⟨V, h1, h2⟩ := h x
      exact ⟨⟨V, h2⟩, h1⟩)
    Y q (fun U ↦ by have := (hq U).effectiveEpi; infer_instance)
    (fun U ↦ by have := (hq U).surjective; exact Surjective.surj)
    (fun U u v ↦ (hq U).apply_eq_iff u v)
    (fun U x y ⟨p, h1, h2⟩ hx ↦ by
      have : p ∈ a ⁻¹ᵁ U.1 := by change a p ∈ U.1; rwa [h1]
      rw [(hq U).stable] at this
      rw [← h2]; exact this)
    k hk hqk
  refine ⟨Y', π, ?_, ?_, ?_, ?_, ?_⟩
  · exact prop_of_charts (@IsFinite.{0}) π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).isFinite
  · exact prop_of_charts @Flat.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).flat
  · exact prop_of_charts @LocallyOfFinitePresentation.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).lfp
  · exact prop_of_charts @Surjective.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).surjective
  · exact GlobalTheory.T.pullback_of_glued_charts a b π _ Y q em hq hcomm hpre hsurj
end
end
