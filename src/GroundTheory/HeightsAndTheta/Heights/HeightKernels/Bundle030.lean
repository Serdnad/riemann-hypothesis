module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle025
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
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
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle027
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedBase {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span (Set.range fun t => C (a t) * graphFirst t)

def IsStackedExc {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (E : Ideal (MRing (stackedBlocks T))) :
    Prop :=
  E ∈ (stackedBase b' a).minimalPrimes ∧ IsRelevant E

def DualStackedExcCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧ ¬ IsHorizontal E ∧
      ∀ t : T,
        ((divCycle (stackedGraph b' a) (C (a t) * graphFirst t) E : ℤ) =
            divCycle (stackedGraph b' a) (graphSecond t) E + 1) ∧
        ∀ W : Ideal (MRing (stackedBlocks T)), ¬ IsHorizontal W → W ≠ E →
          divCycle (stackedGraph b' a) (C (a t) * graphFirst t) W = divCycle (stackedGraph b' a) (graphSecond t) W

def DualStackedExcGeoSecond.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      (geoNum (i - 1) E (fun _ => degSecond) : ℝ) * Real.log (charOf E) =
        Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup)

def DualStackedExcGeoFirst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∀ d : Fin (i - 1) → Unit ⊕ Unit → ℤ, (∀ j, d j = degFirst ∨ d j = degSecond) → (∃ j, d j = degFirst) →
        geoNum (i - 1) E d = 0

namespace DualStackedExcExample

open DualTopSimpleSubExample

end DualStackedExcExample

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeModPrimeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

abbrev locAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (L : Submodule (𝓞 K) (Fin i → K)) {x : Fin i → K}
    (hx : x ∈ Submodule.span (locAt 𝔭) (L : Set (Fin i → K))) :
    ∃ s ∈ 𝔭.primeCompl, s • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, 𝔭.primeCompl.one_mem, by rwa [one_smul]⟩
  | zero => exact ⟨1, 𝔭.primeCompl.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    refine ⟨q * s, 𝔭.primeCompl.mul_mem q.2 hs, ?_⟩
    have hq : (q : 𝓞 K) • (IsLocalization.mk' (locAt 𝔭) p q) = algebraMap (𝓞 K) (locAt 𝔭) p := by
      rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    have e : (q * s) • (IsLocalization.mk' (locAt 𝔭) p q • x) = p • (s • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (q : 𝓞 K), hq, algebraMap_smul, smul_comm]
    rw [e]
    exact L.smul_mem _ hx

theorem span_dual_eq_top (F : HermLattice K i) :
    Submodule.span K (DualLatticeIndexAlt.dual F.lattice : Set (Fin i → K)) = ⊤ := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_le_box F.lattice F.fg
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  have hbox : DualLatticeIndexAlt.box (i := i) (algebraMap (𝓞 K) K e) ≤ DualLatticeIndexAlt.dual F.lattice := by
    have := DualLatticeIndexAlt.dual_anti hle
    rwa [DualLatticeIndexAlt.dual_box (inv_ne_zero heK), inv_inv] at this
  rw [eq_top_iff, ← (Pi.basisFun K (Fin i)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) ∈ DualLatticeIndexAlt.dual F.lattice := by
    refine hbox (DualLatticeIndexAlt.mem_box.mpr fun l => ?_)
    by_cases hl : l = j
    · subst hl
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hl]⟩
  have e1 : Pi.basisFun K (Fin i) j = (algebraMap (𝓞 K) K e)⁻¹ • (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) := by
    ext l
    by_cases hl : l = j
    · subst hl
      simp [heK]
    · simp [Pi.basisFun_apply, hl]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hj)

theorem dual_le_span (F : HermLattice K i) :
    ∃ u : Fin i → Fin i → K, DualLatticeIndexAlt.dual F.lattice ≤ Submodule.span (𝓞 K) (Set.range u) := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_box_le F.lattice F.span_eq
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨fun j => Pi.single j (algebraMap (𝓞 K) K e)⁻¹, fun x hx => ?_⟩
  have hx' := DualLatticeIndexAlt.dual_anti hle hx
  rw [DualLatticeIndexAlt.dual_box heK, DualLatticeIndexAlt.mem_box] at hx'
  choose a ha using hx'
  have e1 : x = ∑ j, a j • (Pi.single j (algebraMap (𝓞 K) K e)⁻¹ : Fin i → K) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (ha l).symm
  rw [e1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLatticeModPrimeAlt


open DualLatticeModPrimeAlt in
theorem DualLatticeModPrime.proof : DualLatticeModPrime.Statement := by
  intro K _ _ i F 𝔭 h𝔭
  classical
  have hbot : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField K)
  have : IsDiscreteValuationRing (locAt 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hbot (locAt 𝔭)
  set D := DualLatticeIndexAlt.dual F.lattice
  set DA := Submodule.span (locAt 𝔭) (D : Set (Fin i → K))
  obtain ⟨u, hu⟩ := dual_le_span F
  have hDA : DA ≤ Submodule.span (locAt 𝔭) (Set.range u) :=
    Submodule.span_le.mpr fun x hx =>
      Submodule.span_le_restrictScalars (𝓞 K) (locAt 𝔭) _ (hu hx)
  have := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range u)) (R := locAt 𝔭)
  have : Module.Finite (locAt 𝔭) DA := Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp this DA hDA)
  have : Module.IsTorsionFree (locAt 𝔭) DA := inferInstance
  let b := Module.Free.chooseBasis (locAt 𝔭) DA
  have hspan : Submodule.span K (Set.range fun j => (b j : Fin i → K)) = ⊤ := by
    rw [eq_top_iff, ← span_dual_eq_top F, Submodule.span_le]
    intro d hd
    have e0 : d = ∑ j, ((b.repr ⟨d, Submodule.subset_span hd⟩ j • b j : DA) : Fin i → K) := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [e0, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.span_le_restrictScalars (locAt 𝔭) K _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hcard : Fintype.card (Fin i) ≤ Fintype.card (Module.Free.ChooseBasisIndex (locAt 𝔭) DA) := by
    have := finrank_range_le_card (R := K) fun j => (b j : Fin i → K)
    rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at this
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ρ : locAt 𝔭 →+* 𝓞 K ⧸ 𝔭 := IsLocalization.lift (M := 𝔭.primeCompl) (g := Ideal.Quotient.mk 𝔭)
    fun s => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := 𝔭) (a := Ideal.Quotient.mk 𝔭 s)
        fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact ⟨⟨_, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hρ : ∀ a, ρ (algebraMap (𝓞 K) (locAt 𝔭) a) = Ideal.Quotient.mk 𝔭 a := fun a =>
    IsLocalization.lift_eq _ _
  have incl : ∀ φ : dualLattice F, (φ : Fin i → K) ∈ DA := fun φ => Submodule.subset_span φ.2
  let ι : dualLattice F →+ DA := AddMonoidHom.mk' (fun φ => ⟨φ, incl φ⟩) fun _ _ => rfl
  let τ : DA →+ (Fin i → 𝓞 K ⧸ 𝔭) := AddMonoidHom.mk' (fun x l => ρ (b.repr x (g l)))
    fun x y => by funext l; simp [map_add (f := _)]
  have hsmul : ∀ (μ : 𝓞 K) (x : DA), ((algebraMap (𝓞 K) (locAt 𝔭) μ • x : DA) : Fin i → K) =
      algebraMap (𝓞 K) K μ • (x : Fin i → K) := fun μ x => by
    rw [Submodule.coe_smul, algebraMap_smul, algebraMap_smul]
  refine ⟨τ.comp ι, ?_, ?_⟩
  · intro v
    let w : Module.Free.ChooseBasisIndex (locAt 𝔭) DA → 𝓞 K ⧸ 𝔭 := Function.extend g v 0
    choose a ha using fun j => Ideal.Quotient.mk_surjective (I := 𝔭) (w j)
    let x : DA := ∑ j, algebraMap (𝓞 K) (locAt 𝔭) (a j) • b j
    have hx : ∀ j, b.repr x j = algebraMap (𝓞 K) (locAt 𝔭) (a j) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem 𝔭 D x.2
    have hs0 : Ideal.Quotient.mk 𝔭 s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) c
    refine ⟨⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩, ?_⟩
    have e1 : ι ⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩ = algebraMap (𝓞 K) (locAt 𝔭) (t * s) • x := by
      apply Subtype.ext
      rw [hsmul, algebraMap_smul, mul_smul]
      rfl
    funext l
    have key : ∀ y : DA, τ y l = ρ (b.repr y (g l)) := fun _ => rfl
    rw [AddMonoidHom.comp_apply, e1, key, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, hx, hρ,
      map_mul, ht, mul_comm c, hc, one_mul, ha]
    exact g.injective.extend_apply _ _ _
  · intro μ φ ψ h
    have e1 : ι ψ = algebraMap (𝓞 K) (locAt 𝔭) μ • ι φ := by
      apply Subtype.ext
      rw [hsmul]
      exact h
    funext l
    have key : ∀ x : DA, τ x l = ρ (b.repr x (g l)) := fun _ => rfl
    rw [Pi.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e1, key, key, map_smul,
      Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace DualStdGenDeg

def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩

theorem eq_fibreBlk₀ (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h

def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h

theorem range_eq {T Φ' : Type} [Field Φ'] {i : ℕ} (x' : (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → Φ') (d : Φ') :
    (Set.range fun p : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
        fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k) => x' ⟨p.1.1, p.2⟩ / d) =
      Set.range fun t : T => x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / d := by
  ext y
  constructor
  · rintro ⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩
    · exact ⟨t, rfl⟩
    · exact absurd ⟨(), rfl⟩ h
  · rintro ⟨t, rfl⟩
    exact ⟨⟨fibreBlk₀, t⟩, rfl⟩

end DualStdGenDeg


open DualStdGenDeg in
theorem DualStdGenDeg.proof (hPt : OneBlockPointDeg.Statement) (hRat : DualStdFibreRatios.Statement) :
    DualStdGenDeg.Statement := by
  intro K _ _ i T _ _ b G J hi hJ
  obtain ⟨c, hc, hrank, htr⟩ := hRat K i T b G hi
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
      G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
        G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) :=
    Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have key := hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀
    (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc
  beta_reduce at key
  rw [range_eq G.x'] at key
  obtain ⟨hV, hch, hdeg⟩ := key hfin htr
  have hJ0 := hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch
  rw [hJ0]
  exact congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace OneBlockPointDeg

variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem isMultiHomog_of_isHomogeneous (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h

theorem aeval_homog (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h

theorem ringKrullDim_adjoin_eq_one {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl

end OneBlockPointDeg


open OneBlockPointDeg in
theorem OneBlockPointDeg.proof : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf

      rw [← sum_homogeneousComponent f, map_sum] at h0

      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]

end

end GroundTheory.Heights₂.Heights
end
