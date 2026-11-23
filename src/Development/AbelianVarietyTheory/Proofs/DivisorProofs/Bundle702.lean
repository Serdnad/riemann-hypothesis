module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle668
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Renumber

variable {X a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [MeasurableSpace X]

end Renumber

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩



variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

section Pair

variable {n n' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def colDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (X : Matrix (Fin n) D k) : ℂ :=
  stdDatum ν ϖ c (Xᵀ.submatrix σ id)

variable (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D)


omit [Fintype D] [DecidableEq D] in
theorem colDatum_eq {X : Matrix (Fin n) D k} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (h₁ : ∀ i j, X i (σ (.inl j)) = u.val i j) (h₂ : ∀ i j, X i (σ (.inr j)) ∈ cball (ϖ ^ c)) :
    colDatum ν ϖ c σ X = (((ν (GeneralLinearGroup.det u))⁻¹ : ℂˣ) : ℂ) := by
  have e : (Xᵀ.submatrix σ id).toRows₁ = u.valᵀ := by ext i j; exact h₁ j i
  have h : StdSupp ϖ c (Xᵀ.submatrix σ id) :=
    ⟨fun i j => by rw [e]; exact (mem_KO_iff_det.1 hu).1 j i, by rw [e, det_transpose]; exact (mem_KO_iff_det.1 hu).2,
      fun i j => h₂ j i⟩
  rw [colDatum, stdDatum, dite_eq_left h]
  congr 3
  exact Units.ext (by simp [e])

variable [MeasurableSpace k] [BorelSpace k] {m : Measure k}

variable {ν ϖ}


end Pair

section Main

variable {a a' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

end Main

section Place

open IsDedekindDomain NumberField GlobalTheory.CMVal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Place

end GlobalTheory.LocStd

end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC

theorem ker_reduceLoc_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  intro T O _ _ _ _ _ _ A A₁ _ _ f i i₁ EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit hker
  have hψ : ∀ p : A₁[X], algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) p =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) p) :=
    fun _ => rfl
  have hC : ∀ c : A₁, algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) c =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) (C c)) := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), IsScalarTower.algebraMap_apply A₁ A₁[X] (Ext f EA)]
    rfl
  have hlocX : locBC f i i₁ EA QA jA hcomp hj (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA), locBC_algebraMap]
    have h1 : inclE f EA (algebraMap A[X] EA Polynomial.X) =
        algebraMap A[X] (Ext f EA) Polynomial.X :=
      (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
    rw [h1, Algebra.TensorProduct.algebraMap_apply, algebraMap_polyOver, Polynomial.map_X]
    rfl
  have hpol : ∀ q : A₁[X],
      Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X})
        (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) q)) =
      Ideal.Quotient.mk _ (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (Polynomial.eval 0 q)) := by
    intro q
    rw [hC, Ideal.Quotient.eq, ← map_sub, ← map_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [hr, map_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : (Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X}) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* _) =
      (Ideal.Quotient.mk _).comp ((algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x =>
      rw [reduce_tmul]
      dsimp only
      have hsplit : (p ⊗ₜ[A[X]] x : Ext f EA) =
          algebraMap A₁[X] (Ext f EA) p * inclE f EA x := by
        show (p ⊗ₜ[A[X]] x : Ext f EA) = (p ⊗ₜ[A[X]] (1 : EA)) * ((1 : PolyOver f) ⊗ₜ[A[X]] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      simp only [map_mul]
      congr 1
      · exact hpol p
      · rw [← locBC_algebraMap, ← locBC_algebraMap_base]
        have hmem : algebraMap EA (Localization.AtPrime QA) x -
            algebraMap A (Localization.AtPrime QA) (ρ (algebraMap EA (Localization.AtPrime QA) x)) ∈
              RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub]
          have := congrArg (fun w => w (ρ (algebraMap EA (Localization.AtPrime QA) x))) hρA
          simp only [RingHom.comp_apply, RingHom.id_apply] at this
          rw [this, sub_self]
        rw [hker, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, hlocX]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h := congrArg (fun w => w x) key
    simp only [RingHom.comp_apply, hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X) = 0
    rw [hψ, reduceLoc, IsLocalization.lift_eq,
      show algebraMap A₁[X] (Ext f EA) Polynomial.X = (@id (PolyOver f) Polynomial.X) ⊗ₜ[A[X]] (1 : EA)
        from rfl, reduce_tmul]
    show Polynomial.eval 0 (Polynomial.X : A₁[X]) * _ = 0
    rw [Polynomial.eval_X, zero_mul]

end GlobalTheory.KeyOriginBC
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem exists_point_ext (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D]
    (ρ : R →+* A) (hρA : ρ.comp (algebraMap A R) = RingHom.id A)
    (h : GlobalTheory.KeyOriginEnlarge.PointAtZero A R D ρ) :
    ∃ S : D →+* FractionRing A,
      S.comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = (algebraMap A (FractionRing A)).comp ρ := by
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨s, hs⟩ := h
  letI : Algebra (GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  let g : A →+* GlobalTheory.KeyOriginNoeth.closure A R D :=
    (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)).comp (algebraMap A R)
  let M : Submonoid (GlobalTheory.KeyOriginNoeth.closure A R D) := (nonZeroDivisors A).map g
  have hg : ∀ a : A, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) =
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) := fun _ => rfl
  have hR : ∀ r : R, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D
      (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) = GlobalTheory.KeyOriginNoeth.baseHom A R D r :=
    fun _ => rfl
  haveI : IsLocalization M D :=
    { map_units := by
        rintro ⟨_, a, ha, rfl⟩
        show IsUnit (algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a))
        rw [hg]
        exact (IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R)
          (⟨algebraMap A R a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))).map
          (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D)
      surj := fun d => by
        obtain ⟨a, ha, hd⟩ := GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure A R D {d}
        refine ⟨(⟨_, hd d (Finset.mem_singleton_self d)⟩,
          ⟨g a, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩), ?_⟩
        show d * algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) = _
        rw [hg, mul_comm]
        rfl
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [Subtype.ext hxy]⟩ }
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => congrArg (fun w => w a) hρA
  have hsr : ∀ r : R, s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) =
      algebraMap A (FractionRing A) (ρ r) := fun r => congrArg (fun w => w r) hs
  have hu : ∀ y : M, IsUnit (s y) := by
    rintro ⟨_, a, ha, rfl⟩
    show IsUnit (s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a)))
    rw [hsr, hρa]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A (FractionRing A))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A (FractionRing A) h0)
  refine ⟨IsLocalization.lift (M := M) (S := D) hu, ?_⟩
  apply RingHom.ext; intro r
  rw [RingHom.comp_apply, ← hR, IsLocalization.lift_eq, hsr]
  rfl

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem pointAtZero_bc : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ f i i₁ hf EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit DA _ _ q actA
    hq htor hpt
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htor.1
  obtain ⟨S, hS⟩ := exists_point_ext A (Localization.AtPrime QA) DA ρ hρA hpt

  have hfK : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp f) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hf
  let φ : FractionRing A →+* FractionRing A₁ := IsFractionRing.lift hfK
  have hφ : ∀ a : A, φ (algebraMap A (FractionRing A) a) = algebraMap A₁ (FractionRing A₁) (f a) :=
    fun a => IsFractionRing.lift_algebraMap hfK a

  have hρ₁a : ∀ a : A₁, reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) a) = a :=
    fun a => congrArg (fun w => w a) (reduceLoc_algebraMap f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
  have hu₀ : ∀ y : Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁),
      IsUnit (((algebraMap A₁ (FractionRing A₁)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) y) := by
    rintro ⟨_, a, ha, rfl⟩
    simp only [RingHom.coe_comp, Function.comp_apply, hρ₁a]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A₁ (FractionRing A₁))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A₁ (FractionRing A₁) h0)
  let u : GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) →+* FractionRing A₁ :=
    IsLocalization.lift hu₀
  have hu : ∀ r, u (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r) =
      algebraMap A₁ (FractionRing A₁) (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit r) :=
    fun r => IsLocalization.lift_eq hu₀ r

  let v : DA →+* FractionRing A₁ := φ.comp S
  have huv : u.comp (fibBC f i i₁ EA QA jA hcomp hj hf) =
      v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    simp only [RingHom.coe_comp, Function.comp_apply, fibBC_algebraMap, hu]
    have h1 := congrArg (fun w => w r) (reduceLoc_locBC f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
    have h2 := congrArg (fun w => w r) hS
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1]
    show _ = φ (S (GlobalTheory.KeyOriginNoeth.baseHom A _ DA r))
    rw [h2, hφ]

  letI : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) (FractionRing A₁) :=
    (v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).toAlgebra
  let W₁ : BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA →+* FractionRing A₁ :=
    (Algebra.TensorProduct.productMap
      (⟨(u : Over (fibBC f i i₁ EA QA jA hcomp hj hf) →+* FractionRing A₁), fun r =>
        congrArg (fun w => w r) huv⟩ :
          Over (fibBC f i i₁ EA QA jA hcomp hj hf) →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)]
            FractionRing A₁)
      (⟨v, fun _ => rfl⟩ : DA →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] FractionRing A₁)).toRingHom
  have hW : ∀ y, W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA) y) = u y := by
    intro y
    show W₁ ((show Over (fibBC f i i₁ EA QA jA hcomp hj hf) from y) ⊗ₜ (1 : DA)) = u y
    refine (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans ?_
    rw [map_one, mul_one]
    rfl
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
  refine ⟨W₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)).subtype, ?_⟩
  apply RingHom.ext; intro r
  show W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r)) = _
  rw [hW, hu]
  rfl

end GlobalTheory.KeyOriginBC
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}

theorem wachMap_comp_coeff (W : LocWach PD LL O v f) {T T' T'' : LocLat G Qp LL O} {n n' n'' : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
    (b'' : Module.Basis (Fin n'') (LetA O f) ↥(W.N T''))
    (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L)
    (a : Fin n → Fin n' → LetA O f) (a' : Fin n' → Fin n'' → LetA O f) (a'' : Fin n → Fin n'' → LetA O f)
    (h1 : ∀ k, W.map g (b k : W.DD T) = ∑ m, a k m • (b' m : W.DD T'))
    (h2 : ∀ k, W.map g' (b' k : W.DD T') = ∑ m, a' k m • (b'' m : W.DD T''))
    (h3 : ∀ k, W.map g'' (b k : W.DD T) = ∑ m, a'' k m • (b'' m : W.DD T''))
    (hc : ∀ x, g''.f x = g'.f (g.f x)) (k : Fin n) (p : Fin n'') :
    a'' k p = ∑ m, a k m * a' m p := by
  have hg : g'' = latComp g' g := by
    cases g''
    simp only [latComp]
    congr 1
    exact LinearMap.ext hc
  have hsm : ∀ {S S' : LocLat G Qp LL O} (u : LatHom S.L S'.L) (c : LetA O f) (x : W.DD S),
      W.map u (c • x) = c • W.map u x := fun u c x => (W.map u).map_smul_of_tower c x
  have key : W.map g'' (b k : W.DD T) = ∑ q, (∑ m, a k m * a' m q) • (b'' q : W.DD T'') := by

    rw [hg, W.map_comp, h1 k, map_sum]
    simp_rw [hsm, h2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have e : ∑ q, a'' k q • b'' q = ∑ q, (∑ m, a k m * a' m q) • b'' q := by
    apply (W.N T'').subtype_injective

    simpa [map_sum] using (h3 k).symm.trans key
  have := congrArg (fun x => b''.repr x p) e

  simpa [Finset.sum_apply, map_sum, Finsupp.smul_apply, b''.repr_self, Finsupp.single_apply] using this

end Gen




theorem isMapMat_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  intro l _ P H K LL hA T T' T'' n n' n'' b b' b'' g g' g'' A A' A'' h1 h2 h3 hc i
  obtain ⟨hadd, hmul, hC, -, -, -, -, hinj⟩ := Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold l ↥(OL LL)
  let incR : (↥(OL LL))⟦X⟧ →+* (↥(OL LL))⟦X⟧ :=
    { toFun := inc l ↥(OL LL)
      map_one' := by simpa using hC 1
      map_mul' := hmul
      map_zero' := by simpa using hC 0
      map_add' := hadd }
  refine Matrix.ext fun p k => hinj hA.2.1 ?_
  have e := congrFun (wachMap_comp_coeff (H.W K 1 LL hA.2.2) b b' b'' g g' g''
    (fun k m i => inc l ↥(OL LL) (A i m k)) (fun k m i => inc l ↥(OL LL) (A' i m k))
    (fun k m i => inc l ↥(OL LL) (A'' i m k)) h1 h2 h3 hc k p) i
  rw [Finset.sum_apply] at e
  rw [Matrix.mul_apply]
  refine e.trans (Eq.trans ?_ (map_sum incR _ _).symm)
  exact Finset.sum_congr rfl fun m _ => (mul_comm _ _).trans (hmul _ _).symm

end GlobalTheory.WachPlace
end
end
