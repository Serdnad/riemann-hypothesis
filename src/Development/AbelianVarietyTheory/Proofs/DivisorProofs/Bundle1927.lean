module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.RegularGamma

open Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pbL : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

def vec : Fin (pbL P).dim → k ⊗[F] Fld P := fun i => (1 : k) ⊗ₜ (pbL P).basis i

theorem smul_tmul' (a : k) (e : E) (b : k) (l : Fld P) :
    (a ⊗ₜ[F] e : k ⊗[F] E) • (b ⊗ₜ[F] l : k ⊗[F] Fld P) = (a * b) ⊗ₜ (algebraMap E (Fld P) e * l) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem span_vec : Submodule.span (k ⊗[F] E) (Set.range (vec P k)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a l =>
    rw [← (pbL P).basis.sum_repr l, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : a ⊗ₜ[F] ((pbL P).basis.repr l i • (pbL P).basis i) =
        (a ⊗ₜ[F] (pbL P).basis.repr l i : k ⊗[F] E) • vec P k i := by
      rw [vec, smul_tmul', mul_one, Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem bijective_vec (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Function.Bijective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
  have hs : Function.Surjective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_vec]
  have hd : (pbL P).dim = r := (AdjoinRoot.powerBasis_dim _).trans P.2.2.2.1
  let ψ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin (pbL P).dim → k ⊗[F] E) :=
    φ.trans (LinearEquiv.funCongrLeft _ _ (finCongr hd))
  haveI : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.equiv φ.symm
  have hi := OrzechProperty.injective_of_surjective_endomorphism
    ((Fintype.linearCombination (k ⊗[F] E) (vec P k)) ∘ₗ ψ.toLinearMap) (hs.comp ψ.surjective)
  refine ⟨fun y y' hyy => ?_, hs⟩
  obtain ⟨z, rfl⟩ := ψ.surjective y
  obtain ⟨z', rfl⟩ := ψ.surjective y'
  rw [hi hyy]

def bas (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Module.Basis (Fin (pbL P).dim) (k ⊗[F] E) (k ⊗[F] Fld P) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (bijective_vec P k φ)).symm

theorem bas_apply (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (i : Fin (pbL P).dim) :
    bas P k φ i = vec P k i := by
  simp [bas, Module.Basis.coe_ofEquivFun]

theorem mul_vec (j : Fin (pbL P).dim) :
    ((1 : k) ⊗ₜ[F] alpha P) * vec P k j =
      ∑ i, (inclR (F := F) k (Algebra.leftMulMatrix (pbL P).basis (alpha P) i j)) • vec P k i := by
  have hinc : ∀ e : E, inclR (F := F) k e = (1 : k) ⊗ₜ[F] e := fun _ => rfl
  simp only [vec, hinc, smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← Algebra.smul_def]
  exact ((pbL P).basis.sum_repr _).symm

theorem charpoly_mul_alpha (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    haveI := Module.Free.of_basis (bas P k φ)
    haveI := Module.Finite.of_basis (bas P k φ)
    (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  rw [← LinearMap.charpoly_toMatrix _ (bas P k φ)]
  have hM : LinearMap.toMatrix (bas P k φ) (bas P k φ)
      (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)) =
      (Algebra.leftMulMatrix (pbL P).basis (alpha P)).map (inclR (F := F) k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.mul_apply', bas_apply, mul_vec]
    simp_rw [← bas_apply P k φ]
    rw [Module.Basis.repr_sum_self]
    rfl
  rw [hM, Matrix.charpoly_map, show alpha P = (pbL P).gen from (AdjoinRoot.powerBasis_gen _).symm,
    charpoly_leftMulMatrix]
  exact congrArg _ (AdjoinRoot.minpoly_powerBasis_gen_of_monic P.2.1)

theorem charpoly_mulMat (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  change (LinearMap.toMatrix' (φ.conj (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)))).charpoly = _
  rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix, LinearEquiv.charpoly_conj,
    charpoly_mul_alpha P k φ]

variable {P k}

theorem gam_val {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ((gam h).1 : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ (torUnit _).1 = _
  congr 1
  change Matrix.det _ = _
  rw [Matrix.det_fin_one]
  rfl

end GlobalTheory.RegularGamma

namespace GlobalTheory.RegularGamma

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

theorem isRegSS_gam {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) : IsRegSS (matAt V ρ (gam h)) := by
  have hm : matAt V ρ (gam h) = (mulMat φ ((1 : (placeOf D ρ).Completion) ⊗ₜ alpha P)).map (infEmb (embOverOf D ρ)) := by
    rw [← gam_val h]
    rfl
  change (matAt V ρ (gam h)).charpoly.Separable
  rw [hm, Matrix.charpoly_map, charpoly_mulMat, Polynomial.map_map]
  exact (Irreducible.separable P.2.2.1).map

end GlobalTheory.RegularGamma
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult

theorem strictAnti_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) : StrictAnti lam := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by obtain ⟨k, hk⟩ := hr; omega⟩
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

end GlobalTheory.TrMult

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.RealPlaceCentraliser

section Gen
open scoped Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [Field k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem nondeg (hJ : IsHermND σ J) (b : Fin n → k ⊗[F] E)
    (hb : ∀ a, Formalism.UG.hform (sigR k σ) (JR k J) a b = 0) : b = 0 := by
  have hv : JR (F := F) k J *ᵥ b = 0 := by
    funext i
    have := hb (Pi.single i 1)
    simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have hdet : IsUnit (JR (F := F) k J).det := by
    have : (JR (F := F) k J).det = inclR (F := F) k J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hJ.2).map _
  calc b = ((JR (F := F) k J)⁻¹ * JR (F := F) k J) *ᵥ b := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem zero_of_hx (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) (z : k ⊗[F] Fld P)
    (hz : ∀ y', hx P k x z y' = 0) : z = 0 := by
  have : φ z = 0 := nondeg hJ _ fun a => by
    obtain ⟨y', rfl⟩ := φ.surjective a
    rw [h]; exact hz y'
  simpa using this

theorem isUnit_of_isIsom [Module.Finite F (Fld P)] (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) : IsUnit x := by
  haveI : Module.Finite k (k ⊗[F] Fld P) := Module.Finite.base_change F k (Fld P)
  have hinj : Function.Injective (LinearMap.mulLeft k x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    refine zero_of_hx hJ h y fun y' => ?_
    simp only [LinearMap.mulLeft_apply] at hy
    simp [hx, hy]
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] E) : sigR k σ (sigR k σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem hform_herm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (a b : Fin n → k ⊗[F] E) :
    sigR k σ (Formalism.UG.hform (sigR k σ) (JR k J) a b) = Formalism.UG.hform (sigR k σ) (JR k J) b a := by
  have hG : ∀ i j, sigR k σ (JR (F := F) k J i j) = JR (F := F) k J j i := by
    intro i j
    simp only [JR, Matrix.map_apply, inclR]
    change sigR k σ (1 ⊗ₜ J i j) = 1 ⊗ₜ J j i
    simp [sigR, hJ.1]
  unfold Formalism.UG.hform

  simp only [map_sum, map_mul, sigR_sigR hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofBijective σ (Function.Involutive.bijective hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofBijective (star' P) (Algebra.IsAlgebraic.algHom_bijective _)
  have he : (algebraMap E (Fld P)).comp (e₁ : E →+* E) = (e₂ : Fld P →+* Fld P).comp (algebraMap E (Fld P)) :=
    RingHom.ext fun e => (star'_algebraMap P e).symm
  have := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  have h2 := congrArg e₁ this
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.symm

theorem trBase_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] Fld P) :
    trBase P k (sigR k (star' P) z) = sigR k σ (trBase P k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => simp [trBase, sigR, trace_star hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem plusUnits_gen [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ∃ u : plusUnits P k, u.1.1 = x := by
  have hu := isUnit_of_isIsom hJ h
  have hsym : ∀ y, trBase P k ((x - sigR k (star' P) x) * sigR k (star' P) y) = 0 := by
    intro y
    have h1 := h 1 y
    have h2 := h y 1
    have h3 := hform_herm hσ hJ (φ 1) (φ y)
    rw [h2, h1] at h3
    simp only [hx, map_one, mul_one] at h3
    rw [← trBase_star hσ, map_mul] at h3
    rw [sub_mul, map_sub, ← h3, sub_self]
  have hd : x - sigR k (star' P) x = 0 := by
    obtain ⟨v, hv⟩ := hu
    have h0 := zero_of_hx hJ h (↑v⁻¹ * (x - sigR k (star' P) x)) fun y' => by
      simp only [hx]
      rw [show x * (↑v⁻¹ * (x - sigR k (star' P) x)) * sigR k (star' P) y' =
          (x - sigR k (star' P) x) * sigR k (star' P) y' by
        rw [← mul_assoc, ← hv, Units.mul_inv, one_mul]]
      exact hsym y'
    have := congrArg (fun w => (v : k ⊗[F] Fld P) * w) h0
    simpa [← mul_assoc] using this
  refine ⟨⟨hu.unit, ?_⟩, rfl⟩
  show Units.map (sigR k (star' P)).toMonoidHom hu.unit = MonoidHom.id _ hu.unit
  ext
  simpa using (sub_eq_zero.mp hd).symm

end Gen

theorem plusUnits_of_isIsom {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) :
    ∃ u : plusUnits P (placeOf D ρ).Completion, u.1.1 = x := by
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  exact plusUnits_gen (fun e => star_star e) (GlobalTheory.DefiniteQuotient.gram_hermND V) h

theorem topGrp {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borel {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

theorem torComm {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (s t : HA R σ J) : s * t = t * s := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  change (s.1.1 * t.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0 = (t.1.1 * s.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0
  simp [Matrix.mul_apply, mul_comm]

theorem measFacts {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : G, a * b = b * a) (e : G ≃ₜ* H) (dt : Measure G) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant ∧ (dt.map e).real univ = dt.real univ ∧
      (CompactSpace H ↔ CompactSpace G) := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have := congrArg e (hc (e.symm a) (e.symm b))
    simpa [map_mul] using this
  haveI hH : (dt.map e).IsHaarMeasure := e.isHaarMeasure_map dt
  refine ⟨hH, ⟨fun g => ?_⟩, ?_, ?_⟩
  · have : (fun a : H => a * g) = (fun a => g * a) := funext fun a => hcomm a g
    rw [this]
    exact map_mul_left_eq_self _ g
  · rw [Measure.real, Measure.real, Measure.map_apply (show Measurable (e : G → H) from e.continuous.measurable) MeasurableSet.univ, Set.preimage_univ]
  · exact ⟨fun hc => e.toHomeomorph.symm.compactSpace, fun hc => e.toHomeomorph.compactSpace⟩

theorem centMeas_real_place : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  intro D V P ρ dt _ x φ h
  obtain ⟨u, rfl⟩ := plusUnits_of_isIsom V P ρ h
  have H := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure D.host.F D.host.E D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.rank P V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) (placeOf D ρ).Completion u φ h
  obtain ⟨e, H2⟩ := H
  have hm := H2.2
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  haveI := topGrp (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := topGrp (placeOf D ρ).Completion (star' P) (one₁ P)
  haveI := borel (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := borel (placeOf D ρ).Completion (star' P) (one₁ P)

  simp only [hm dt]
  have hc := torComm (placeOf D ρ).Completion (star' P) (one₁ P)
  have hf := measFacts (G := Tor P (placeOf D ρ).Completion) (H := cent (gam h)) hc e dt
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  rw [isCompact_iff_compactSpace]
  exact hf.2.2.2

end GlobalTheory.RealPlaceCentraliser
end

section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' :=
  GlobalTheory.AutGrowth.KilledFin.Zalg_commute hz hz'

end GlobalTheory.LeviGL.ZGood

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  first | exact @GlobalTheory.Mem.HeckeLevel.exists_level_nat | exact GlobalTheory.Mem.HeckeLevel.exists_level_nat | (intros; apply GlobalTheory.Mem.HeckeLevel.exists_level_nat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sobolev_bound_for_smooth_vectors : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  first | exact @GlobalTheory.SobolevGrowth.pointwise_growth | exact GlobalTheory.SobolevGrowth.pointwise_growth | (intros; apply GlobalTheory.SobolevGrowth.pointwise_growth <;> assumption)
end
