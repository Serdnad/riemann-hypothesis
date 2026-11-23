module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import ReciprocityTheory.SemistableReduction.SemiDegZA
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle615
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClasses
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocalStage

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  apply GlobalTheory.VertUnitsNoeth.mem_originIdeal_iff' <;> assumption

theorem comap_originIdeal {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom φ) =
      GlobalTheory.KeyOriginCut.originIdeal R := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

theorem localStage : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  intro T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα
  letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra
  letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra
  haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) :=
    Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')
  let f : Polynomial A' →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)
      commutes' := by
        intro p
        change (algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [Polynomial.map_map, hαι] }
  let g : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA))
      commutes' := by
        intro p
        change jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [← IsScalarTower.algebraMap_apply]
        exact congrArg (fun h => h p) hjA }
  let F : (Polynomial A' ⊗[Polynomial A] EA) →+* O :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hF : ∀ a b, F (a ⊗ₜ b) = f a * g b := fun a b => by
    simp [F, Algebra.TensorProduct.productMap_apply_tmul]
  let Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA) := (maximalIdeal O).comap F
  refine ⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q',
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) := by
      refine RingHom.ext fun p => ?_
      rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
      rfl
    change ((maximalIdeal O).comap F).comap _ = _
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]
  let h : EA →+* (Polynomial A' ⊗[Polynomial A] EA) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom
  have hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x) := fun x => by
    change F (1 ⊗ₜ x) = _
    rw [hF, map_one, one_mul]
    rfl
  have hy : QA.primeCompl ≤ Q'.primeCompl.comap h := by
    intro x hx
    have hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x)) :=
      (IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA
    change h x ∉ Q'
    intro hmem
    have hmem' : F (h x) ∈ maximalIdeal O := hmem
    rw [hh] at hmem'
    exact ((mem_maximalIdeal _).mp hmem') hu
  have hγ : ∀ y : Q'.primeCompl, IsUnit (F y) := by
    intro y
    by_contra hc
    exact y.2 ((mem_maximalIdeal _).mpr hc)
  let β : Localization.AtPrime QA →+* Localization.AtPrime Q' :=
    IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q')
      (g := h) (T := Q'.primeCompl) hy
  let γ : Localization.AtPrime Q' →+* O :=
    IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ
  refine ⟨β, γ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA),
      IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q')]
    change _ = β (algebraMap EA (Localization.AtPrime QA) _)
    rw [IsLocalization.map_eq]
    congr 1
    change algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) =
      (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change _ = Polynomial.map ι (Polynomial.C a)
    rw [Polynomial.map_C]
    rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    change γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, hh]
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply,
      hF, map_one, mul_one]
    change algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl

end GlobalTheory.LocalStage
end
end

section

namespace GlobalTheory.HermitianEigenvalueInequality

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  apply ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom <;> assumption

end GlobalTheory.HermitianEigenvalueInequality
end

section


theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  first | exact @GlobalTheory.HerbrandAlg.herbrandDet | exact GlobalTheory.HerbrandAlg.herbrandDet | (intros; apply GlobalTheory.HerbrandAlg.herbrandDet <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, WittVector.frobenius a = WittVector.frobenius (xi ε) * a → ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  first | exact @GlobalTheory.PDivLat.existsUnique_padic_of_eigen | exact GlobalTheory.PDivLat.existsUnique_padic_of_eigen | (intros; apply GlobalTheory.PDivLat.existsUnique_padic_of_eigen <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualBase

theorem dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by
  intro E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have : (d : E) = 0 := by simpa using hδ.symm
    have : d = 0 := by exact_mod_cast this
    omega
  obtain ⟨i0, -⟩ := hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))
  have hconj : IsCMField.complexConj E δ = -δ := by
    apply (φ i0).injective
    rw [IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]
    simp [Complex.conj_ofReal]
  have hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero hδ0)
  have hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹) := by
    rw [map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]
  obtain ⟨h1, h2⟩ := hval _ hξ0 hξc
  refine ⟨h1, fun B hB ε => ?_⟩
  obtain ⟨h3, h4⟩ := h2 B hB ε
  refine ⟨h3, fun i => ?_⟩
  rw [h4 i, map_mul, map_inv₀, map_intCast, hφ]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>
    · push_cast
      field_simp

end GlobalTheory.DualBase
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem iterD_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  intro I J _ _ _ _ e u h A z
  have key : ∀ v : List I, iterD v (fun z ↦ A * h (fun j ↦ z (e.symm j))) =
      fun z ↦ A * iterD (v.map e) h (fun j ↦ z (e.symm j)) := by
    intro v
    induction v with
    | nil => rfl
    | cons i v ih =>
      funext z
      show partialD i (iterD v _) z = A * partialD (e i) (iterD (v.map e) h) _
      rw [ih]
      simp only [partialD, lineDeriv]
      have hpath : (fun t : ℂ ↦ A * iterD (v.map e) h (fun j ↦ (z + t • (Pi.single i 1 : I → ℂ)) (e.symm j))) =
          fun t ↦ A * iterD (v.map e) h ((fun j ↦ z (e.symm j)) + t • (Pi.single (e i) 1 : J → ℂ)) := by
        funext t
        congr 2
        funext j
        simp [Pi.single_apply, Equiv.symm_apply_eq]
      rw [hpath, deriv_const_mul_field]
  exact congrFun (key u) z

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.IterDProd

theorem diffOn_iteratedDeriv {r : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball 0 r) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv Metric.isOpen_ball

theorem hasLineDerivAt_prod {I : Type} [Fintype I] [DecidableEq I] (φ : I → ℂ → ℂ) (A : ℂ)
    (z : I → ℂ) (j : I) (hj : DifferentiableAt ℂ (φ j) (z j)) :
    HasLineDerivAt ℂ (fun z : I → ℂ ↦ A * ∏ i, φ i (z i))
      (A * (deriv (φ j) (z j) * ∏ i ∈ Finset.univ.erase j, φ i (z i))) z (Pi.single j 1) := by
  unfold HasLineDerivAt
  have h1 : (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i))
      = fun t ↦ A * (φ j (z j + t) * ∏ i ∈ Finset.univ.erase j, φ i (z i)) := by
    funext t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
  have h2 : HasDerivAt (fun t : ℂ ↦ φ j (z j + t)) (deriv (φ j) (z j)) 0 := by
    have h : HasDerivAt (φ j) (deriv (φ j) (z j)) (z j + 0) := by simpa using hj.hasDerivAt
    exact h.comp_const_add (z j) 0
  show HasDerivAt (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i)) _ 0
  rw [h1]
  exact (h2.mul_const _).const_mul A

theorem iterD_prod_ball {I : Type} [Fintype I] [DecidableEq I] (u : List I) (r : ℝ)
    (ψ : I → ℂ → ℂ) (A : ℂ) (hr : 0 < r) (hψ : ∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) :
    ∀ z ∈ Metric.ball (0 : I → ℂ) r, iterD u (fun z ↦ A * ∏ i, ψ i (z i)) z
      = A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) := by
  induction u with
  | nil => intro z _; simp [iterD]
  | cons j u ih =>
    intro z hz
    have hzj : z j ∈ Metric.ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff] at hz ⊢
      exact (norm_le_pi_norm z j).trans_lt hz
    have hev : iterD u (fun z ↦ A * ∏ i, ψ i (z i)) =ᶠ[nhds z]
        fun z ↦ A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) ih
    have hd := hasLineDerivAt_prod (fun i ↦ iteratedDeriv (u.count i) (ψ i)) A z j
      ((diffOn_iteratedDeriv (hψ j) _).differentiableAt (Metric.isOpen_ball.mem_nhds hzj))
    show lineDeriv ℂ (iterD u (fun z ↦ A * ∏ i, ψ i (z i))) z (Pi.single j 1) = _
    rw [hev.lineDeriv_eq, hd.lineDeriv,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · rw [List.count_cons_self, iteratedDeriv_succ]
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [List.count_cons_of_ne (Finset.ne_of_mem_erase hi).symm]

theorem iterD_prod : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  intro I _ _ u r ψ A hr hψ
  exact iterD_prod_ball u r ψ A hr hψ 0 (Metric.mem_ball_self hr)

end GlobalTheory.IterDProd
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.ClassInv

theorem finPart_unit {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hχ : IsValChar φ s κ 𝔣 Q χ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits (condQ 𝔣 Q)) : finPart χ u = 1 := by
  refine OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

theorem lamInf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (α : Eˣ) :
    lamInf φ (2 * s) κ α =
      ((χ.inf α : ℂˣ) : ℂ) * (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) := by
  have hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s := by
    rw [← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
  rw [hN, (hasInfRatio_iff χ φ _).1 h α]
  unfold lamInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : φ i α ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i α) ≠ 0 := by simp
  have h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ) := by push_cast; ring
  rw [h3, zpow_natCast, div_pow, inv_pow]
  field_simp
  ring

theorem lattice_princ_mul_unit {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} (y : (Af E)ˣ) (α : Eˣ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom α * y * u) = (fun x => (α : E) * x) '' lattice c y := by
  rw [lattice_mul_unit _ hu]
  ext x
  constructor
  · intro hx
    refine ⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩
    simpa using hx
  · rintro ⟨z, hz, rfl⟩
    exact (mul_mem_lattice_princ c y α z).2 hz

theorem classInvariance : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ (s : ℕ) (L : Set E), Homothety φ (2 * s) L) → ∀ s : ℕ, ClassInvariance φ s := by
  intro E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 := (hH s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := finPart_unit hχ hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, lamInf_eq hφ hχ.2.2.1 α]
  unfold lamFin
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInv
end
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem _root_.GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  first | exact @GlobalTheory.QuadInHost.exists_quadField | exact GlobalTheory.QuadInHost.exists_quadField | (intros; apply GlobalTheory.QuadInHost.exists_quadField <;> assumption)
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair), IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa → IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb → ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟 → nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by
  first | exact @GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | exact GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | (intros; apply GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq <;> assumption)
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  first | exact @GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | exact GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | (intros; apply GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mean_log_norm_conjugates_over_ideal_classes : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (β : ℂ) (F : (ℂ ≃+* ℂ) → ℝ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Equidistributed φK j₀ 𝔞 → IsAlgebraic ℚ β → β ≠ 0 → (∀ σ σ' : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ' → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → F σ = F σ') → (∀ σ : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → Real.log ‖σ β‖ ≤ F σ) → ∃ rep : ClassGroup (𝓞 K) → (ℂ ≃+* ℂ), (∀ c, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK (rep c) ∧ ClassGroup.mk K (𝔞 (rep c)) = c) ∧ Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (NumberField.classNumber K : ℝ)) := by
  first | exact @GlobalTheory.GalMean.galmean | exact GlobalTheory.GalMean.galmean | (intros; apply GlobalTheory.GalMean.galmean <;> assumption)
end
