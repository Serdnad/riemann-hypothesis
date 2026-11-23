module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

end Core

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push Not at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
end
end

section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
end

section

open Ad3 (Pl Qv pOf)
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

end GlobalTheory.CompanionTheory.HalfIntegral
end
end
