module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle331
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle250
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
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
public import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle313
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314

@[expose] public section

section

namespace GlobalTheory.SpanOrbitTop

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by
  apply GlobalTheory.FinGL.GGFree.span_orbit <;> assumption

end GlobalTheory.SpanOrbitTop
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_pow_eq_one_algClosure_coprime (l : ℕ) [Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  apply GlobalTheory.Per.exists_pow_eq_one_of_algClosure_zmod <;> assumption

theorem exists_unit_frobenius_eq_mul (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [IsAlgClosed k]
    (u : WittVector l k) (hu : IsUnit u) :
    ∃ w : WittVector l k, IsUnit w ∧ WittVector.frobenius w = u * w := by
  have h1 : (1 : WittVector l k).coeff 0 ≠ 0 := by simp
  have h2 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := k))).ne_zero
  refine ⟨WittVector.frobeniusRotation l h1 h2, ?_, ?_⟩
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [WittVector.frobeniusRotation, WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero l h1 h2
  · have := WittVector.frobenius_frobeniusRotation l h1 h2
    rwa [mul_one, mul_comm] at this

private theorem padicInt_ringHom_ext (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : R)}) R) _ fun n => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = c * (l : ℤ_[l]) ^ n + (x.appr n : ℤ_[l]) := by rw [hc]; ring
  have h : f x - g x = (f c - g c) * (l : R) ^ n := by
    rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  intro l _ F hF u
  obtain ⟨f⟩ := GlobalTheory.T.nonempty_closure_hom_tilt_field l
  let u' : WittVector l (AlgebraicClosure (ZMod l)) :=
    WittVector.map (ZMod.castHom (dvd_refl l) _) (WittVector.fromPadicInt l u)
  have hu' : IsUnit u' := (u.isUnit.map _).map _
  obtain ⟨w₀, hw₀, hφ⟩ := exists_unit_frobenius_eq_mul l _ u' hu'
  have hfu : WittVector.map f u' = Per.zA l u := by
    exact RingHom.congr_fun (padicInt_ringHom_ext l (R := Per.Ainf l)
      ((WittVector.map f).comp ((WittVector.map (ZMod.castHom (dvd_refl l) _)).comp
        (WittVector.fromPadicInt l))) (Per.zA l)) u
  have hact : ∀ (g : GQ l) (n : ℕ), n ≠ 0 →
      (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → g x = x ^ n) →
      ∀ a, Per.σF g (f a) = f a ^ n := by
    intro g n hn hg a
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero, zero_pow hn]
    · obtain ⟨m, hm, hl, ham⟩ := exists_pow_eq_one_algClosure_coprime l a ha
      exact GlobalTheory.T.tilt_galois_action_root_of_unity_coprime l (f a) m n g hm hl (by rw [← map_pow, ham, map_one])
        fun x hx => hg x m hm hl hx
  have hφA : Per.φA l (WittVector.map f w₀) = Per.zA l u * WittVector.map f w₀ := by
    rw [← hfu, ← map_mul, ← hφ]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.phiA_coeff]
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]
  refine ⟨WittVector.map f w₀, hw₀.map _, fun g hg => ?_, ?_, hφA⟩
  · refine WittVector.ext fun n => ?_
    have := hact g 1 one_ne_zero (fun x m hm hl hx => by
      rw [pow_one]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, hx⟩)) (w₀.coeff n)
    rw [pow_one] at this
    rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff]
    exact this
  · rw [← hφA]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff]
    exact hact F l (Fact.out : l.Prime).ne_zero hF (w₀.coeff n)

end GlobalTheory.MemLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues : ∀ {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A), z ≠ 0 → (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) → (∀ x, AbsIrrDistinct (overK (rep x))) → InRing T rep eB → eB * eB = eB → (∀ x, ((eB x).map (toFr A)).rank = t) → ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable → ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x, (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t := by
  first | exact @GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | exact GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | (intros; apply GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (F : GA E a → ℂ) :
    GA E a → ℂ := fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

structure IsBCC (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  cusp : IsCuspidal F
  left : ∀ γ g, F (ratGL E a γ * g) = F g


variable (E a) in
def lieBasis : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)


variable (E a) in
def lieCoord (i : Fin (Module.finrank ℝ (Lie E a))) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((lieBasis E a).coord i))

def adCoef (γ : GL (Fin a) (Cinf E)) (p : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a))) : ℂ :=
  lieCoord E a p.1 (toL ((γ⁻¹).val * Matrix.of (lieBasis E a p.2) * γ.val))

theorem sum_lieCoord (X : Lie E a) : ∑ i, ((lieBasis E a).coord i X) • lieBasis E a i = X :=
  (lieBasis E a).sum_repr X

end GlobalTheory.JSW
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
  GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.ConjLocal

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem finrank_DdR_congr : finrank LL ↥(DdR PD ρ) = finrank LL ↥(DdR PD ρ') := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  rw [hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq

end DdR

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem exists_ext_entries (L₁ : FinExt l) (A : GL (Fin a) (Om l)) :
    ∃ L₂ : FinExt l, L₁.1 ≤ L₂.1 ∧ (∀ i j, (A : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1) ∧
      ∀ i j, ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1 := by
  let f : Bool × Fin a × Fin a → Om l := fun p => if p.1 then (A : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
    else ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
  have hfin : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨supExt L₁ ⟨_, hfin⟩, le_sup_left, fun i j => ?_, fun i j => ?_⟩
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(true, i, j), rfl⟩)
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(false, i, j), rfl⟩)

theorem repE_apply (L : FinExt l) (r : ↥Gw →* GL (Fin a) ↥L.1) (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L r g x = ((r (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).mulVec x := by
  simp [LocBridge.repE, Matrix.toLinAlgEquiv'_apply]


variable {Bw} in
theorem exists_conj_model {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = A * r g * A⁻¹) {L₁ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1}
    (h₁ : IsModel Bw r L₁ r₁) :
    ∃ (L₂ : FinExt l) (hL : L₁.1 ≤ L₂.1) (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1), IsModel Bw r' L₂ r₂ ∧
      ∃ e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1), ∀ g x,
        e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x) := by
  obtain ⟨L₂, hL, hA, hB⟩ := exists_ext_entries L₁ A
  let A₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hA i j⟩
  let B₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hB i j⟩
  let f : ↥L₂.1 →+* Om l := algebraMap ↥L₂.1 (Om l)
  have fA : f.mapMatrix A₂ = (A : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have fB : f.mapMatrix B₂ = ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have inj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L₂.1 → Matrix (Fin a) (Fin a) (Om l)) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : A₂ * B₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : B₂ * A₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  let U : GL (Fin a) ↥L₂.1 := ⟨A₂, B₂, h1, h2⟩
  refine ⟨L₂, hL, (MulAut.conj U).toMonoidHom.comp
    (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁), ?_, ?_⟩
  · refine ⟨h₁.1.trans hL, ?_⟩
    ext g i j
    rw [hc g, ← h₁.2]
    change (f.mapMatrix (A₂ * ((IntermediateField.inclusion hL).toRingHom.mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1)) * B₂)) i j =
      ((A : Matrix (Fin a) (Fin a) (Om l)) * (algebraMap ↥L₁.1 (Om l)).mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1) *
        ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) i j
    rw [map_mul, map_mul, fA, fB]
    rfl
  · refine ⟨Formalism.MainNotions.N.K.Norm.matEquiv A₂ B₂ h1 h2, fun g x => ?_⟩
    rw [Formalism.MainNotions.N.K.Norm.matEquiv_apply, Formalism.MainNotions.N.K.Norm.matEquiv_apply, repE_apply, repE_apply]
    change A₂.mulVec (Matrix.mulVec _ x) = Matrix.mulVec (A₂ * _ * B₂) (A₂.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem local_conj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω))
    (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)),
    (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧
      (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧
      ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  intro l _ P E Ω _ _ _ _ O _ _ _ Gw Bw a r r' A hc
  have dR : ∀ {L₁ L₂ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1} (hL : L₁.1 ≤ L₂.1)
      (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1) (e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1)),
      (∀ g x, e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x)) → Bw.IsdRE P L₁ r₁ → Bw.IsdRE P L₂ r₂ := by
    intro L₁ L₂ r₁ hL r₂ e he hd
    have h := (local_ext P Bw hL r₁).2.1.2 hd
    unfold LocBridge.IsdRE at h ⊢
    rw [← finrank_DdR_congr (P.PD Bw.Kw) e he, h]
  refine ⟨fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_,
    fun τ J ⟨L₁, r₁, h₁, hd, τ₁, hτ, hJ⟩ => ?_⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, dR hL r₂ e he hd⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD Bw.Kw) e he ((local_ext P Bw hL r₁).1.2 hd)⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    obtain ⟨K', hK, hcr⟩ := (local_ext P Bw hL r₁).2.2.1.2 hd
    exact ⟨L₂, r₂, hm, K', hK, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD K') e (fun g x => he _ x) hcr⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    refine ⟨L₂, r₂, hm, dR hL r₂ e he hd, (IntermediateField.inclusion hL).comp τ₁, fun x => hτ x, fun n => ?_⟩
    rw [hJ n, ← (local_ext P Bw hL r₁).2.2.2 τ₁ n]
    exact Formalism.MainNotions.N.K.Norm.multV_congr (P.PD Bw.Kw) e he _ n

end GlobalTheory.ConjLocal
end
end

section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) = Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧ ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 → ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  first | exact @GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | exact GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | (intros; apply GlobalTheory.Cyc.finrank_Ks_and_chi_surjective <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ (φ' : A.K × A.K → ℂ) (κ : ℂ), IsTest φ' ∧ ∀ a : A.K, IsUnit a → orbG M f' (sec (A.invK τ p lam a)) = κ * A.orbK m.μK φ' a ∧ orbG M (fourG M ψ f') (sec (A.invK τ p lam a)) = κ * A.orbK m.μK (A.fourK m.μK ψ φ') a := by
  first | exact @GlobalTheory.JR.LinDesc.descent | exact GlobalTheory.JR.LinDesc.descent | (intros; apply GlobalTheory.JR.LinDesc.descent <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  first | exact @GlobalTheory.JR.UnitStep.unitMatch_succ | exact GlobalTheory.JR.UnitStep.unitMatch_succ | (intros; apply GlobalTheory.JR.UnitStep.unitMatch_succ <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_aN_eq_range_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  first | exact @GlobalTheory.NL.WkRange.jD_aN_eq_range | exact GlobalTheory.NL.WkRange.jD_aN_eq_range | (intros; apply GlobalTheory.NL.WkRange.jD_aN_eq_range <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_le_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hax hdet
  obtain ⟨j, hinj, hrange, happ, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A

  have haxF : AxIn (IntermediateField.fixedField A) L p := by
    intro J x hx
    obtain ⟨y, hy, hxy⟩ := hax (J.map j) x (by
      rintro σ ⟨τ, hτ, rfl⟩
      rw [happ]
      exact hx τ hτ)
    refine ⟨y, fun τ hτ => ?_, hxy⟩
    rw [← happ]
    exact hy (j τ) ⟨τ, hτ, rfl⟩
  have hdetF : Detects p r ⊤ (B.comap j) := by
    intro τ₀ _ hτ₀
    have hA : j τ₀ ∈ A := hrange.le (MonoidHom.mem_range.mpr ⟨τ₀, rfl⟩)
    obtain ⟨x, a, hxa, hnd⟩ := hdet (j τ₀) hA hτ₀
    refine ⟨x, fun τ => a (j τ), fun τ _ => ?_, hnd⟩
    obtain ⟨z, hz, hzx⟩ := hxa (j τ) (hrange.le (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
    refine ⟨z, hz, ?_⟩
    rw [← happ]
    exact hzx
  have key := GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects (IntermediateField.fixedField A) L p E r (B.comap j) hp hE hord haxF hdetF
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  rw [hwild, jumpSum_comap_injective _ _ j _ B hinj, hrange] at key
  exact key

end GlobalTheory.PMon.Ram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
end
