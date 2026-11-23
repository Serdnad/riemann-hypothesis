module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle079
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle047
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNormalizedLocalHaarSelfDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.OSplitCore

theorem mem_mul_of_mem {A : Type} [CommRing A] (R : Subring A) {m n q : ℕ} (X : Matrix (Fin m) (Fin n) A)
    (Y : Matrix (Fin n) (Fin q) A) (hX : ∀ i j, X i j ∈ R) (hY : ∀ i j, Y i j ∈ R) :
    ∀ i j, (X * Y) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R.mul_mem (hX _ _) (hY _ _)

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f :=
  rfl

theorem mapped_props (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (U : Set Γ) (p : Γ → ℂ[X]) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hadic : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (r : Γ →* GL (Fin a) O) (hr : Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)))
    (hss : IsSSRep (mapRep (algebraMap O (FractionRing O)) r))
    (hp : ∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map
      (ι.toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) :
    IsSSRep (mapRep iq (mapRep (algebraMap O (FractionRing O)) r)) ∧
    Continuous (fun g => ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l))) ∧
    (∀ σ ∈ U, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) σ : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
      (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j,
      ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R := by
  have hcz : CharZero (FractionRing O) := ⟨fun m n h => by
    have := congrArg iq h
    simpa using this⟩
  have hcoe : ∀ g, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)) =
      ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (iq.comp (algebraMap O (FractionRing O))) := by
    intro g
    rw [coe_mapRep, coe_mapRep, Matrix.map_map]
    rfl
  refine ⟨GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ iq a _ hss, ?_, ?_, ?_⟩
  · simp only [hcoe]
    exact hr.matrix_map (GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure l O hadic iq hiq)
  · intro σ hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map]
    exact hp σ hσ
  · obtain ⟨T, hT⟩ := GlobalTheory.T.exists_finset_image_mem_subring l O iq hiq
    refine ⟨T, fun R hR hTR g i j => ?_⟩
    rw [hcoe]
    exact hT R hR hTR _

theorem exists_splitting_set : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ (ρ₀ : G E Ω →* GL (Fin a) (Qbar l)) (T : Finset (Qbar l)), IsSSRep ρ₀ ∧
      Continuous (fun g => ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
      ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
        (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j, ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R
  swap
  · refine ⟨∅, ?_⟩
    intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq _ r hr hss hp
    subst h
    exfalso
    obtain ⟨h1, h2, h3, T, h4⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
    exact hex ⟨_, T, h1, h2, h3, h4⟩
  obtain ⟨ρ₀, T, hss₀, hc₀, hp₀, hT⟩ := hex
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.semisimple_matrix_rep_decomp ρ₀ hss₀
  choose b E D σ₀ hDE hran hσ₀ using fun j => GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep ρ₀ (Vs j) (hirr j).2.1
  let T' : Finset (Qbar l) := T ∪ Finset.univ.biUnion (fun j : Fin n =>
    Finset.univ.image (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) ∪
      Finset.univ.image (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2))
  refine ⟨T'.image ι, ?_⟩
  intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq hS r hr hss hp
  subst h
  obtain ⟨hss', hc', hp', -⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
  have hT'R : ∀ t ∈ T', t ∈ iq.range := by
    intro t ht
    obtain ⟨x, hx⟩ := hS (ι t) (Finset.mem_image_of_mem _ ht)
    exact ⟨x, ι.injective hx⟩
  have hRz : ∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ iq.range := fun z => ⟨_, hiq z⟩
  have hTR : (↑T : Set (Qbar l)) ⊆ (iq.range : Set (Qbar l)) := fun t ht => hT'R t (Finset.mem_union_left _ ht)
  have hER : ∀ j i s, E j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hDR : ∀ j i s, D j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hρ₀R := hT iq.range hRz hTR
  set ρ := mapRep (algebraMap O (FractionRing O)) r with hρ
  have hcp : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
    GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense _ _ hc' hc₀ U hU fun x hx =>
      Polynomial.map_injective _ ι.injective (by rw [hp' x hx, hp₀ x hx])
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (mapRep iq ρ) ρ₀ hss' hss₀ hcp
  have hint' : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) =
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g
    rw [hPm g]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  apply GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models iq ρ
  intro V hV
  obtain ⟨j, M, hM, hMV, hMd⟩ := GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub (mapRep iq ρ) ρ₀ Pm hint' hss' Vs
    hint.submodule_iSup_eq_top hirr V hV
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_rep_lift_of_entries_mem_range iq (σ₀ j) fun g i s => by
    have : ((σ₀ j g : GL (Fin (b j)) (Qbar l)) : Matrix (Fin (b j)) (Fin (b j)) (Qbar l)) i s ∈ iq.range := by
      rw [(hσ₀ j g).1]
      exact mem_mul_of_mem _ _ _ (mem_mul_of_mem _ _ _ (hDR j) (hρ₀R g)) (hER j) i s
    exact this
  refine ⟨b j, σ, M * E j, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [← Matrix.mulVec_mulVec] at hvw
    have hv : (E j).mulVec v ∈ Vs j := hran j ▸ ⟨v, rfl⟩
    have hw : (E j).mulVec w ∈ Vs j := hran j ▸ ⟨w, rfl⟩
    have hsub : (E j).mulVec v - (E j).mulVec w ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hvw
    have h0 := hMd.le_bot ⟨hsub, Submodule.sub_mem _ hv hw⟩
    have hEq : (E j).mulVec v = (E j).mulVec w := sub_eq_zero.1 h0
    have := congrArg (D j).mulVec hEq
    simpa [Matrix.mulVec_mulVec, hDE j] using this
  · rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hran j, hMV]
  · intro g
    rw [hσ, ← Matrix.mul_assoc, hM g, Matrix.mul_assoc, (hσ₀ j g).2, Matrix.mul_assoc]

end GlobalTheory.OSplitCore
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

theorem exists_equiv_of_counts {A B : Type} [Fintype A] [Fintype B] (a : A → ℕ) (b : B → ℕ)
    (hb : ∀ x, 0 < b x)
    (h : ∀ t : ℕ, (Finset.univ.filter fun x => t < a x).card = (Finset.univ.filter fun x => t < b x).card) :
    ∃ e : {x // 0 < a x} ≃ B, ∀ x, b (e x) = a x.1 := by
  classical
  have key : ∀ {C : Type} [Fintype C] (f : C → ℕ) (c : ℕ), 0 < c →
      (Finset.univ.filter fun x => f x = c).card + (Finset.univ.filter fun x => c < f x).card =
        (Finset.univ.filter fun x => c - 1 < f x).card := by
    intro C _ f c hc
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      omega
  have fib : ∀ c, Fintype.card {x : {x // 0 < a x} // a x.1 = c} = Fintype.card {y // b y = c} := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · have h1 : IsEmpty {x : {x // 0 < a x} // a x.1 = 0} := ⟨fun x => by have := x.1.2; have := x.2; omega⟩
      have h2 : IsEmpty {y // b y = 0} := ⟨fun y => by have := hb y.1; have := y.2; omega⟩
      simp
    · have e1 : Fintype.card {x : {x // 0 < a x} // a x.1 = c} = (Finset.univ.filter fun x => a x = c).card := by
        rw [← Fintype.card_subtype]
        refine Fintype.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, by have := x.2; omega⟩, x.2⟩, ?_, ?_⟩
        · intro x; rfl
        · intro x; rfl
      have e2 : Fintype.card {y // b y = c} = (Finset.univ.filter fun x => b x = c).card := by
        rw [Fintype.card_subtype]
      rw [e1, e2]
      have k1 := key a c hc
      have k2 := key b c hc
      have h1 := h c
      have h2 := h (c - 1)
      omega
  refine ⟨Equiv.ofFiberEquiv (f := fun x : {x // 0 < a x} => a x.1) (g := b)
    (fun c => Fintype.equivOfCardEq (fib c)), fun x => ?_⟩
  exact Equiv.ofFiberEquiv_map _ x

theorem card_colLen_gt (μ : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card = μ.rowLen t := by
  classical
  have hle : μ.rowLen t ≤ μ.rowLen 0 := μ.rowLen_anti 0 t (Nat.zero_le _)
  have : (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c) =
      Finset.univ.filter fun c : Fin (μ.rowLen 0) => c.val < μ.rowLen t := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  rw [this, ← Fintype.card_subtype]
  rw [Fintype.card_congr (β := Fin (μ.rowLen t))
    ⟨fun c => ⟨c.1.1, c.2⟩, fun c => ⟨⟨c.1, by have := c.2; omega⟩, c.2⟩, fun _ => rfl, fun _ => rfl⟩]
  simp

theorem minor_cast {K : Type} [CommRing K] {N h h' : ℕ} (Y : Matrix (Fin N) (Fin N) K) (e : h = h') (hN : h ≤ N)
    (I : Fin h → Fin N) :
    Matrix.det (Matrix.of fun p q : Fin h => Y (I p) (Fin.castLE hN q)) =
      Matrix.det (Matrix.of fun i j : Fin h' => GL3Columns.colsOf Y (I (Fin.cast e.symm i)) (j : ℕ)) := by
  subst e
  congr 1
  ext p q
  have hq : (q : ℕ) < N := lt_of_lt_of_le q.2 hN
  simp [GL3Columns.colsOf, hq, Fin.castLE]

theorem bidFns_eq_minors {K : Type} [CommRing K] {N : ℕ} (μ : YoungDiagram) (ν : Fin N → ℕ)
    (h1 : ∀ r : Fin N, μ.rowLen r = ν r) (h2 : ∀ r, N ≤ r → μ.rowLen r = 0)
    (g : Matrix (Fin N) (Fin N) K → K) (hg : g ∈ bideterminantFunctionsOfShape K N ν) :
    ∃ J : ∀ c : Fin (μ.rowLen 0), Fin (μ.colLen c) ↪o Fin N, ∀ Y : Matrix (Fin N) (Fin N) K,
      g Y = ∏ c : Fin (μ.rowLen 0), Matrix.det (Matrix.of fun i j : Fin (μ.colLen c) =>
        GL3Columns.colsOf Y (J c i) (j : ℕ)) := by
  classical
  obtain ⟨Kc, sz, hsz, I, hshape, hI, rfl⟩ := hg
  have count : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < N
    · have := congrFun hshape ⟨t, ht⟩
      rw [h1 ⟨t, ht⟩, ← this]
      simp only [Formalism.GradedWeylDivisibility.shapeDeg]
    · rw [h2 t (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hpos : ∀ c : Fin (μ.rowLen 0), 0 < μ.colLen c := by
    intro c
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    exact c.2
  obtain ⟨e, he⟩ := exists_equiv_of_counts sz (fun c : Fin (μ.rowLen 0) => μ.colLen c) hpos count
  have hk : ∀ c, sz (e.symm c).1 = μ.colLen c := by
    intro c
    have := he (e.symm c)
    simpa using this.symm
  refine ⟨fun c => OrderEmbedding.ofStrictMono (fun i => I (e.symm c).1 (Fin.cast (hk c).symm i))
    (fun i j hij => hI _ (by simpa using hij)), fun Y => ?_⟩
  have hone : ∀ k, ¬ 0 < sz k → Matrix.det (Matrix.of fun p q : Fin (sz k) =>
      Y (I k p) (Fin.castLE (hsz k) q)) = 1 := by
    intro k hk0
    have h0 : sz k = 0 := by omega
    haveI : IsEmpty (Fin (sz k)) := by rw [h0]; infer_instance
    exact Matrix.det_isEmpty
  have hev : MvPolynomial.eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I) =
      ∏ k, Matrix.det (Matrix.of fun p q : Fin (sz k) => Y (I k p) (Fin.castLE (hsz k) q)) := by
    simp only [Formalism.GradedWeylDivisibility.bideterminant, Formalism.GradedWeylDivisibility.initMinor, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp
  show MvPolynomial.eval _ _ = _
  rw [hev, ← Finset.prod_filter_of_ne (p := fun k => 0 < sz k)
    (fun k _ hne => by by_contra hc; exact hne (hone k hc)), Finset.prod_subtype _ (p := fun k => 0 < sz k) (by simp)]
  refine (Fintype.prod_equiv e.symm _ _ fun c => ?_).symm
  exact (minor_cast Y (hk c) (hsz _) (I (e.symm c).1)).symm

theorem prod_bidFns_eq_minY : ∀ (D : D7) (K : Type) [CommRing K] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν → ∀ g : D.what₂.Tau → Matrix (Fin N) (Fin N) K → K,
    (∀ τ, g τ ∈ bideterminantFunctionsOfShape K N (ν τ)) → ∃ J : KM.ColChoice N nu, ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) K,
      ∏ τ, g τ (y τ) = GL3Columns.minY N nu J (fun s => GL3Columns.colsOf (y (tauPl D s))) := by
  classical
  intro D K _ N nu ν hfit g hg
  have hJ := fun z => bidFns_eq_minors (nu z) (ν (tauPl D z)) (hfit.1 z) (hfit.2 z) (g (tauPl D z)) (hg _)
  choose J hJ using hJ
  refine ⟨J, fun y => ?_⟩
  refine ((tauPl_bij D).prod_comp (fun τ => g τ (y τ))).symm.trans ?_
  exact Finset.prod_congr rfl fun z _ => hJ z (y (tauPl D z))

end GlobalTheory.Mem.CanonicalSurjection
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftMult

open Matrix

theorem sig_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem actT_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

theorem mem_multT_of_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  intro D θ V S M π J χ L hθ hs hp hfd hT hinj hπ haut hlev heq
  have hd := isDefinite hs hp
  refine (mem_multT θ M J χ L).2 (Submodule.subset_span ?_)
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm L v = L (PiTensorProduct.tprod ℂ v) := fun v => rfl
  refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk g => hlev _ k hk g,
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    refine (GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd _).1 ⟨haut _, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine rTr_mem hθ _ (fun τ g hg => ?_) hk _ (LinearMap.mem_range_self L _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    exact ⟨_, heq τ u x⟩
  · obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    rw [e, e, ← heq]
    congr 1
    exact hinj ((actT_tprod τ _ v w hw).trans (hπ τ u _).symm)
  · haveI := (hfd τ).1
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x

end GlobalTheory.DefLiftMult

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equivariant_local_pair_map_adelic : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  first | exact @GlobalTheory.LevelHecke.exists_pmap | exact GlobalTheory.LevelHecke.exists_pmap | (intros; apply GlobalTheory.LevelHecke.exists_pmap <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.eventually_normalizedLocalHaar_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, SdR (Fv F v) (psiV F ψ v) (s.nuV v) ∧ SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (tupMeas (s.lamV v) 1 M) := by
  first | exact @GlobalTheory.GaugeEx.SelfDualAE.main | exact GlobalTheory.GaugeEx.SelfDualAE.main | (intros; apply GlobalTheory.GaugeEx.SelfDualAE.main <;> assumption)
end
