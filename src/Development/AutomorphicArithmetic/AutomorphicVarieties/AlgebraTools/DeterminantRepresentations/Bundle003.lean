module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.adicContIff :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R), IsAdic I →
    ∀ f : Γ → R, UpperTheory.V.Alg.AdicCont I f ↔ Continuous f := by
  intro Γ R _ _ _ _ I hI f
  rw [isAdic_iff] at hI
  obtain ⟨hopen, hsmall⟩ := hI
  unfold UpperTheory.V.Alg.AdicCont
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, tendsto_sub_nhds_zero_iff.symm]
    intro s hs
    obtain ⟨N, hN⟩ := hsmall s hs
    have hloc := (IsLocallyConstant.iff_eventually_eq _).mp (hf N) g
    rw [Filter.mem_map]
    filter_upwards [hloc] with y hy
    exact hN (Ideal.Quotient.eq.mp hy)
  · intro hf N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hO : IsOpen {r : R | r - f g ∈ I ^ N} :=
      (hopen N).preimage (continuous_id.sub continuous_const)
    have hmem : f g ∈ {r : R | r - f g ∈ I ^ N} := by
      simp
    filter_upwards [hf.continuousAt (hO.mem_nhds hmem)] with y hy
    exact Ideal.Quotient.eq.mpr hy
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.genSpan :
    ∀ {A G : Type} [CommRing A] [Group G] (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G),
    ∃ (m : ℕ) (g : Fin m → G) (b : Fin m → B), x = ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
  intro A G _ _ B _ _ x
  have hs : ∀ g : G, MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single g 1)
      = MonoidAlgebra.single g (1 : B) := by
    intro g
    simp
  simp only [hs]
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    exact ⟨1, fun _ => g, fun _ => 1, by simp [MonoidAlgebra.of_apply]⟩
  | add x y hx hy =>
    obtain ⟨m, g, b, rfl⟩ := hx
    obtain ⟨n, h, c, rfl⟩ := hy
    refine ⟨m + n, Fin.append g h, Fin.append b c, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x hx =>
    obtain ⟨m, g, b, rfl⟩ := hx
    refine ⟨m, g, fun j => r * b j, ?_⟩
    rw [Finset.smul_sum]
    simp [smul_smul]
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.liftIndep :
    ∀ {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    ∀ (B : Type) [CommRing B] [Algebra A B] (σ τ : Type) (p : MvPolynomial σ A →ₐ[A] B) (q : MvPolynomial τ A →ₐ[A] B)
      (x : MonoidAlgebra (MvPolynomial σ A) G) (z : MonoidAlgebra (MvPolynomial τ A) G),
      MonoidAlgebra.mapRingHom G (p : MvPolynomial σ A →+* B) x = MonoidAlgebra.mapRingHom G (q : MvPolynomial τ A →+* B) z →
      p (d σ x) = q (d τ z) := by
  intro A G _ _ d hd B _ _ σ τ p q x z hxz
  classical
  let S : Finset G := x.coeff.support ∪ z.coeff.support
  let w : MonoidAlgebra (MvPolynomial G A) G := ∑ g ∈ S, MonoidAlgebra.single g (MvPolynomial.X g)
  let φ : MvPolynomial G A →ₐ[A] MvPolynomial σ A := MvPolynomial.aeval fun g => x.coeff g
  let ψ : MvPolynomial G A →ₐ[A] MvPolynomial τ A := MvPolynomial.aeval fun g => z.coeff g
  have hx : MonoidAlgebra.mapRingHom G (φ : MvPolynomial G A →+* MvPolynomial σ A) w = x := by
    ext g
    by_cases hg : g ∈ S

    · simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : x.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))

      simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have hz : MonoidAlgebra.mapRingHom G (ψ : MvPolynomial G A →+* MvPolynomial τ A) w = z := by
    ext g
    by_cases hg : g ∈ S

    · simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : z.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))

      simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have key : p.comp φ = q.comp ψ := by
    refine MvPolynomial.algHom_ext fun g => ?_
    have h := congrArg (fun y : MonoidAlgebra B G => y.coeff g) hxz
    simpa [φ, ψ] using h
  calc p (d σ x) = p (φ (d G w)) := by rw [← hd, hx]
    _ = (p.comp φ) (d G w) := rfl
    _ = (q.comp ψ) (d G w) := by rw [key]
    _ = q (d τ z) := by
      change q (ψ (d G w)) = q (d τ z)
      rw [← hd, hz]
end
