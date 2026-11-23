module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem ea_finite_bad {E R : Type*} [Field E] [CommRing R] (ι : E →+* R)
    {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) (m : Ideal R) [m.IsMaximal] :
    {μ : E | (1 + ι μ • g).det ∈ m}.Finite := by
  classical
  let f : E →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ι
  let gb : Matrix n n (R ⧸ m) := g.map (Ideal.Quotient.mk m)
  let P : Polynomial (R ⧸ m) :=
    ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det
  have hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det := by
    intro c
    have h := (Polynomial.evalRingHom c).map_det
      ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at h
    show Polynomial.eval c (Matrix.det _) = _
    rw [h]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  have hfin : {c : R ⧸ m | P.eval c = 0}.Finite := by
    apply (P.roots.toFinset.finite_toSet).subset
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp [Polynomial.mem_roots hP0, hc]
  apply (hfin.preimage (fun _ _ _ _ h => f.injective h)).subset
  intro μ hμ
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢
  rw [hev]
  have h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hμ
  rw [RingHom.map_det] at h1
  convert h1 using 2
  ext i j
  by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]

theorem ea_artinian {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
  have hs : Function.Surjective (Algebra.TensorProduct.comm F (v.adicCompletion F) E) :=
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective
  first
    | exact hs.isArtinianRing
    | exact IsArtinianRing.of_surjective _ hs
    | exact Function.Surjective.isArtinianRing hs

theorem eigenvalue_avoidance : EigAvoid := by
  intro F E _ _ _ _ _ n _ _ σ hσ hθ T g
  classical
  obtain ⟨θ, hθ⟩ := hθ
  let bad : Set E := ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
    ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal},
      {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
    haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v
    refine Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_
    haveI : m.IsMaximal := hm
    exact ea_finite_bad _ (g v) m
  have hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : θ = -(t : E) := by linear_combination h
    rw [h', map_neg, map_natCast]
  have hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : σ θ = -(t : E) := by linear_combination h
    have h'' : θ = -(t : E) := by rw [← hσ θ, h', map_neg, map_natCast]
    rw [h', h'']
  let f : ℕ → E := fun t => ((t : E) + θ) / ((t : E) + σ θ)
  have hinj : Function.Injective f := by
    intro s t hst
    have hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ) := hst
    rw [div_eq_div_iff (hnz2 s) (hnz2 t)] at hst'
    have h2 : ((s : E) - t) * (σ θ - θ) = 0 := by linear_combination hst'
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hθ
  have hrange : ¬ Set.range f ⊆ bad := fun h =>
    Set.infinite_range_of_injective hinj (hbad.subset h)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hrange
  refine ⟨f t, ?_, ?_⟩
  · show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1
    rw [map_div₀, map_add (f := _), map_add (f := _), map_natCast, hσ]
    have h1 := hnz1 t
    have h2 := hnz2 t
    field_simp
  · intro v hv
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    exact ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem bd_int_mult {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : K) * e) := by
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  exact ⟨y, hy0, by rwa [zsmul_eq_mul] at hyint⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bd_local (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ Valued.v ((N : v.adicCompletion F) * a) ≤ 1 := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨(Ideal.absNorm (Ideal.span {b}) : ℤ), ?_, ?_⟩
  · have h0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    exact_mod_cast h0
  · have hab' : a * algebraMap F (v.adicCompletion F) (b : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact hab
      | (convert hab using 2)
      | simpa using hab
    have hc' : algebraMap F (v.adicCompletion F) (c : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
      | (convert IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c using 1)
      | simpa using IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c
    have hcast : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) =
        ((Ideal.absNorm (Ideal.span {b}) : ℤ) : v.adicCompletion F) := by
      rw [← map_mul, show (c : F) * (b : F) = ((c * b : 𝓞 F) : F) from rfl, hc]
      simp
    rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← hcast]
    have e : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) * a =
        algebraMap F (v.adicCompletion F) (c : F) * (a * algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact mul_mem hc' hab'

theorem bd_main (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E ⊗[F] v.adicCompletion F) * x ∈ Sv E v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | tmul e t =>
    obtain ⟨N₁, hN₁, h₁⟩ := bd_int_mult e
    obtain ⟨N₂, hN₂, h₂⟩ := bd_local v t
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have hL : ((N₁ : ℤ) : E ⊗[F] v.adicCompletion F) = (N₁ : E) ⊗ₜ[F] (1 : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_intCast]
    have hR : ((N₂ : ℤ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (N₂ : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    have e1 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (e ⊗ₜ[F] t) =
        ((N₁ : E) * e) ⊗ₜ[F] (1 : v.adicCompletion F) *
          ((1 : E) ⊗ₜ[F] ((N₂ : v.adicCompletion F) * t)) := by
      rw [Int.cast_mul, hL, hR]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨⟨(N₁ : E) * e,
      RingHom.mem_range.2 ⟨⟨_, h₁⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Set.mem_union_right _ ⟨⟨(N₂ : v.adicCompletion F) * t, ?_⟩, rfl⟩))
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 h₂
  | add x y hx hy =>
    obtain ⟨N₁, hN₁, h₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have e2 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (x + y) =
        (N₂ : E ⊗[F] v.adicCompletion F) * ((N₁ : E ⊗[F] v.adicCompletion F) * x) +
          (N₁ : E ⊗[F] v.adicCompletion F) * ((N₂ : E ⊗[F] v.adicCompletion F) * y) := by
      push_cast
      ring
    rw [e2]
    exact Subring.add_mem _ (Subring.mul_mem _ (intCast_mem _ N₂) h₁)
      (Subring.mul_mem _ (intCast_mem _ N₁) h₂)

theorem bounded_rational_unitary : BddR := by
  intro F E _ _ _ _ _ v x
  obtain ⟨N, hN, h⟩ := bd_main v x
  refine ⟨(N : 𝓞 F), by exact_mod_cast hN, ?_⟩
  have e : dv E v (N : 𝓞 F) = (N : E ⊗[F] v.adicCompletion F) := by
    unfold dv
    simp [PI.UnitaryApproxDefs.inclE]
  rw [e]
  exact h

end PI.UnitaryApproxFinWork

end
end
