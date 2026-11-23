module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle006
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem gaussNormOf_rename {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _

theorem specFirst_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]

theorem gaussNorm_map_eq_one {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem GaussEq.proof (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgFinite

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

def lineSub (y : Par e n → E) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial E :=
  Fin.cases (motive := fun _ => Polynomial E)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def transVar (m : Fin n) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Par e n) k :=
  Fin.cases (motive := fun _ => MvPolynomial (Par e n) k)
    (X (.inr ij.2) - if ij.2 = m then 1 else 0) (fun i => X (.inl (i, ij.2))) ij.1

def transVarInv (m : Fin n) : Par e n → MvPolynomial (Fin (e + 1) × Fin n) k
  | .inl ij => X (ij.1.succ, ij.2)
  | .inr j => X (0, j) + if j = m then 1 else 0

theorem transVar_injective (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by
  have h : (aeval (R := k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.cases with
    | zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]
    | succ i => simp [transVar, transVarInv]
  refine Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_
  simpa using DFunLike.congr_fun h p

theorem coord_integral (h1 : IncidenceNull.Statement) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (hy : AlgebraicIndependent k y)
    (hg : IsChowForm Q (e + 1) g) (m : Fin n) :
    IsIntegral E (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  set x := secCoord Q' y with hx
  have hC : ∀ a : E, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap E (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k E) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap E (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h

    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap E (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h

    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap E (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]

        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
        Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := h1 k n (e + 1) Q g hg
  set P : Polynomial E := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj
  have hP0 : P ≠ 0 := by
    intro h0
    have h1' : Polynomial.aeval (1 : E) P = aeval y (aeval (transVar (k := k) m) g) := by
      have ha := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (1 : E)).restrictScalars k)) g
      have hb := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (transVar (k := k) m) (aeval y)) g
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at ha hb
      have hfun : (fun ij => Polynomial.aeval (1 : E) (lineSub y m ij)) =
          fun ij => aeval y (transVar (k := k) m ij) := by
        funext ⟨i, j⟩
        induction i using Fin.cases with
        | zero => by_cases hj : j = m <;> simp [lineSub, transVar, hj]
        | succ i => simp [lineSub, transVar]
      rw [hP, ha, hb, hfun]
    rw [h0, map_zero] at h1'
    exact hg.1 (transVar_injective m ((hy.eq_zero_of_aeval_eq_zero _ h1'.symm).trans
      (map_zero (aeval (R := k) (transVar (k := k) (e := e) m))).symm))
  obtain ⟨N, hN⟩ := hnil
  exact isAlgebraic_iff_isIntegral.1 ⟨P ^ N, pow_ne_zero _ hP0, by rw [map_pow, hN]⟩

end SecAlgFinite

theorem SecAlgFinite.proof (h1 : IncidenceNull.Statement) : SecAlgFinite.Statement := by
  intro k E _ _ _ n e Q g y hy _ hg
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  have htop : Algebra.adjoin E (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ E (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective E _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecAlgFinite.coord_integral h1 Q g y hy hg m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem genPar_algebraicIndependent (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem secCoord_adjoin {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

theorem secCoord_chart {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem ChowNormFormGeneric.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : GenSecSeparable.Statement) (h₄ : ChowSecDvd.Statement)
    (h₅ : NormFormIrreducible.Statement) (h₆ : GenChowIrreducible.Statement)
    (h₇ : NormFormDvd.Statement) : ChowNormFormGeneric.Statement := by
  intro k _ _ n e Q g hQ hg
  have hfin := h₁ k (GenParField k e n) n e Q g (genPar k e n)
    (genPar_algebraicIndependent k e n) hQ hg
  refine ⟨hfin, ?_⟩
  have := h₂ k n e Q g hQ hg
  have := h₃ k n e Q g hQ hg
  have hirr := h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j))
    (secCoord_adjoin _ _) (secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg
  have hd := h₇ (GenParField k e n) (GenSec k e Q) n _
    ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  obtain ⟨u, hu⟩ := hirr.prime.dvd_of_dvd_pow hd
  rcases (h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'
  · exact absurd hN hirr.not_isUnit
  obtain ⟨c, hc, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem specRest_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem ChowNormForm.proof (h₁ : ChowNormFormGeneric.Statement)
    (h₂ : SecAlgFieldChange.Statement) : ChowNormForm.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  have hinj : Function.Injective
      ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E) :=
    hy
  set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ
  have hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k),
      hφ, IsFractionRing.lift_algebraMap]
    simp
  have hy' : y = φ ∘ genPar k e n := by
    funext p
    simp [hφ, genPar, IsFractionRing.lift_algebraMap]
  have hQ' : Q.map (MvPolynomial.map (algebraMap k E)) =
      (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]
  obtain ⟨hfin₀, c, hc, heq⟩ := h₁ k n e Q g hQ hg
  obtain ⟨hfin, hnorm⟩ := h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀
  rw [hQ', hy']
  refine ⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section DvdBasis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

private def tensorPolyAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

private theorem tensorPolyAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    tensorPolyAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [tensorPolyAlgEquiv]

private def tensorPolyEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := tensorPolyAlgEquiv R A n
  invFun := (tensorPolyAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (tensorPolyAlgEquiv R A n).symm_apply_apply
  right_inv := (tensorPolyAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, tensorPolyAlgEquiv_tmul, tensorPolyAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add (f := _), map_add (f := _), hs, ht, smul_add]

private def tensorPolyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (tensorPolyEquiv R A n)

end DvdBasis

theorem NormFormDvd.proof : NormFormDvd.Statement := by
  intro R A _ _ _ _ _ n x p hdvd
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨h, hh⟩ := hdvd
  let b := Module.Free.chooseBasis R A
  let bP := tensorPolyBasis b n
  have hmap : (p.map (algebraMap R A) : MvPolynomial (Fin n) A) =
      algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p := by
    rw [MvPolynomial.algebraMap_def]
  have hnorm : Algebra.norm (MvPolynomial (Fin n) R)
      (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p) = p ^ Module.finrank R A := by
    rw [Algebra.norm_algebraMap_of_basis bP, Module.finrank_eq_card_basis b]
  refine ⟨Algebra.norm (MvPolynomial (Fin n) R) h, ?_⟩
  rw [← hnorm, ← hmap, hh, map_mul]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end
