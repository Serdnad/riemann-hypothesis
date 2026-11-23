module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNormGe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle436
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  apply GlobalTheory.PMon.FrameChange.cont_σC <;> assumption

end GlobalTheory.LTChar
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.baseSize_bounds_along_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  first | exact @GlobalTheory.Proof.baseSize_bounds_along_family.main | exact GlobalTheory.Proof.baseSize_bounds_along_family.main | (intros; apply GlobalTheory.Proof.baseSize_bounds_along_family.main <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.liftingTheorem_phiModules_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  first | exact @GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | exact GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | (intros; apply GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist_comm (x : WD h) (ξ η : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (hη : WeilDeligne.IsSmooth η) : (x.lpTwist ξ hξ).lpTwist η hη = (x.lpTwist η hη).lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  simp only [WD.lpTwist_mk]
  exact WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => smul_comm (η σ : ℂ) (ξ σ : ℂ) (b.ρ σ v), fun v => rfl⟩

theorem hasCentralChar_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := fun z v => by
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have h3 : (IrrRep.det (Fin 1) χ hχ).ρ (GeneralLinearGroup.scalar (Fin 1) z) u = (χ z : ℂ) • u := by
    show (χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • u = _
    rw [h2]
  show (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ (GeneralLinearGroup.scalar (Fin 1) z) (φ.toIntertwiningMap u) =
    _ • φ.toIntertwiningMap u
  rw [← φ.toIntertwiningMap.isIntertwining, h3, map_smul]
  rfl

end GlobalTheory.LocLanglands.ExtTwist

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem trace_almost_onto (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (_hL : ∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a :=
  AlmostTrace.trace_almost_onto_of_levels (GlobalTheory.Cyc.exists_trace_norm_ge l) K L S hKL hS hrep a ha ha1

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, 1 ≤ j → (∀ z ∈ Ohat K, ∃ y ∈ intC (Ks K j), ∃ x ∈ Xj K j, z = y + x) ∧ (∀ y ∈ inC (Ks K j), ∀ x ∈ Xj K j, ∀ n : ℕ, (l : PadicComplex l) ^ n * y = x → y = 0) ∧ (∀ x ∈ Xj K j, x ∈ Ohat K) ∧ (∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, y * x ∈ Xj K j) ∧ (∀ g ∈ (K0 K).fixingSubgroup, ∀ x ∈ Xj K j, act g x ∈ Xj K j) ∧ (∀ x ∈ Ohat K, ∀ y ∈ intC (Ks K j), y ≠ 0 → y * x ∈ Xj K j → x ∈ Xj K j) := by
  first | exact @GlobalTheory.TateDecomp.tate_decomposition | exact GlobalTheory.TateDecomp.tate_decomposition | (intros; apply GlobalTheory.TateDecomp.tate_decomposition <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 → ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧ C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.RegDivide.exists_divide | exact GlobalTheory.MemLoc.RegDivide.exists_divide | (intros; apply GlobalTheory.MemLoc.RegDivide.exists_divide <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcris_regular_of_full_galois_line_units : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_full | exact GlobalTheory.MemLoc.regular_of_full | (intros; apply GlobalTheory.MemLoc.regular_of_full <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := GlobalTheory.T.admA_admB_inert_band_tab D L P X C tf h
  obtain ⟨hE, hExc⟩ := GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded D L P X C tf h
  obtain ⟨hG, hH⟩ := GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab D L P X C tf h
  exact ⟨h.pass, h2, h.rank, GlobalTheory.T.admissible_table_of_local_bounds D L P X C tf h h23, GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive D L P X C tf h,
    GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    GlobalTheory.T.smallPrimeLengthBound_tab D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.specialPrimes_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∀ C : ℝ, 1 ≤ C → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Small (Fm.L x i) C ∧ 8 ≤ (Fm.L x i).sc.L ∧ 60 ≤ (Fm.D x i).host.splitBound ∧ C ≤ (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.SpecialSmall.special_primes_small | exact GlobalTheory.SpecialSmall.special_primes_small | (intros; apply GlobalTheory.SpecialSmall.special_primes_small <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachFrobenius_flat_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 :=
  @GlobalTheory.NL.PhiFlat.main
end
