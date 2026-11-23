module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial (stdBlocks_ones)

namespace GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_block {N : ℕ} {a : Fin N} (i j : Fin (ones N a)) :
    (1 : Matrix (Fin (ones N a)) (Fin (ones N a)) k) i j = 1 := by
  have : i = j := by
    apply Fin.ext
    have h1 := i.2
    have h2 := j.2
    simp only [ones] at h1 h2
    omega
  subst this
  exact Matrix.one_apply_eq i

theorem mem_Nup_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

theorem mem_Nlo_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

end GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

end
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.HeckeAvg

theorem heckeG_eq_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  intro G _ _ _ J _ hJc V _ _ π hπ g U hU r x hr hxJ hx v
  obtain ⟨E, _hE1, hE2, _hE3, hE4, hE5⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJc V π hπ
  have hcomp : ∀ (a b : G) (w : V), π a (π b w) = π (a * b) w := by
    intro a b w
    rw [map_mul]
    rfl
  have hv : ∀ k ∈ J, π k (v : V) = v := by
    intro k hk
    have h0 : ∀ hh : J, π hh (v : V) = ((1 : J →* ℂˣ) hh : ℂ) • (v : V) := v.2
    simpa using h0 ⟨k, hk⟩
  have hH : J ⊓ J.map (MulAut.conj g).toMonoidHom ≤ J := inf_le_left
  have hu : ∀ h ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom, π h (π g (v : V)) = π g (v : V) := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hh).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcomp, show g * k * g⁻¹ * g = g * k by group, ← hcomp, hv k hk]
  have hEu : E (π g (v : V)) = (r : ℂ)⁻¹ • ∑ i, π (x i) (π g (v : V)) :=
    hE5 (π g (v : V)) _ hH hu r x hr hxJ hx
  have hUv : ((U v : fixed π J) : V) = E (π g (v : V)) := by
    have h1 : E ((U v : fixed π J) : V) = ((U v : fixed π J) : V) := hE2 _ (U v).2
    have key : ∀ l : Module.Dual ℂ V, l (E ((U v : fixed π J) : V) - E (π g (v : V))) = 0 := by
      intro l
      have hf : ∀ y ∈ J, (l ∘ₗ E) ∘ₗ π y = l ∘ₗ E := by
        intro y hy
        rw [LinearMap.comp_assoc, hE4 y hy]
      have h2 := hU v (l ∘ₗ E) hf
      simp only [LinearMap.comp_apply] at h2
      rw [map_sub, h2, sub_self]
    have h3 := (Module.forall_dual_apply_eq_zero_iff ℂ _).mp key
    rw [← h1]
    exact sub_eq_zero.mp h3
  rw [hUv, hEu]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hcomp _ _ _

end GlobalTheory.CompanionTheory.HeckeAvg
end
