module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem genU_diag (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_above (s : S) (l k : Fin (r s)) (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.mpr h.le
  simp [genU, h1, h.ne]

theorem genU_below (s : S) (l k : Fin (r s)) (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r)
      (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) := by
  simp only [genU, dif_pos h]

theorem genU_det (s : S) : (genU Ω r s).det = 1 := by
  have hlow : (genU Ω r s).IsLowerTriangular := by
    intro i j hij
    exact genU_above s i j (by simpa using hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun i _ => genU_diag s i

theorem genField_adjoin_eq_top :
    IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) = ⊤ := by
  set K := IntermediateField.adjoin Ω
    (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) with hK
  have hX : ∀ i : GenIx r,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X i) ∈ K := by
    intro i
    obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
    apply IntermediateField.subset_adjoin
    exact ⟨⟨s, (l, k)⟩, genU_below s l k h⟩
  have hP : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun p => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K) p ?_ ?_ ?_
    · intro a
      have h1 := IsScalarTower.algebraMap_apply Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r) a
      rw [MvPolynomial.algebraMap_eq] at h1
      rw [← h1]
      exact IntermediateField.algebraMap_mem K a
    · intro p q hp hq
      rw [map_add (f := _)]
      exact add_mem hp hq
    · intro p n hp
      rw [map_mul]
      exact mul_mem hp (hX n)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (GenIx r) Ω) z
  exact div_mem (hP a) (hP b)

theorem linearIndependent_one_tmul {ι : Type} {v : ι → E} (hv : LinearIndependent Ω v) :
    LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (v k) := by
  simpa only [TensorProduct.mk_apply] using
    Module.Flat.linearIndependent_one_tmul (S := GenField Ω r) hv

theorem genB_linearIndependent (c : ∀ s, Fin (r s) → E) (s : S)
    (h : LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c s k)) :
    LinearIndependent (GenField Ω r) (genB (Ω := Ω) c s) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hz : ∀ l, ∑ k, genU Ω r s l k * g k = 0 := by
    refine h (fun l => ∑ k, genU Ω r s l k * g k) ?_
    rw [← hg]
    simp only [genB, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hv : Matrix.mulVec (genU Ω r s) g = 0 := by
    ext l
    exact hz l
  have hU : IsUnit (genU Ω r s).det := by
    rw [genU_det]
    exact isUnit_one
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((genU Ω r s)⁻¹ * genU Ω r s) g := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = Matrix.mulVec (genU Ω r s)⁻¹ (Matrix.mulVec (genU Ω r s) g) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  intro k
  simp [hg0]

theorem genB_isGenericFlag : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type)
    (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E),
    (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) →
    IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  intro Ω hΩ E hE hEm S r V c hc
  unfold IsGenericFlag
  have hli : ∀ σ, LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c σ k) :=
    fun σ => linearIndependent_one_tmul (r := r) (hc σ).1
  refine ⟨c, genU Ω r, hc, ?_, fun σ => hli σ, fun σ => genB_linearIndependent c σ (hli σ),
    fun σ k => genU_diag σ k, fun σ l k h => genU_above σ l k h, fun σ i => rfl, ?_, Nat.one_pos, ?_⟩
  · intro a e
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · have hai : AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
      (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
        (IsFractionRing.injective (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    have hfam : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        fun q => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext fun q => genU_below q.1 q.2.1.1 q.2.1.2 q.2.2
    rw [hfam]
    exact hai
  · rw [genField_adjoin_eq_top]
    exact IntermediateField.finrank_top

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem eval_map_mul_of_isHomogeneous {σ : Type} [Fintype σ] {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d)
    (r : σ → ℂ) (t : ℂ) :
    MvPolynomial.eval (fun i => r i * t) (MvPolynomial.map (Int.castRingHom ℂ) G) =
      t ^ d * MvPolynomial.eval r (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  have hP : (MvPolynomial.map (Int.castRingHom ℂ) G).IsHomogeneous d := hG.map _
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_ratEval_val {Ω : Type} [Field Ω] {N : ℕ} {S : Subring Ω} (φ : S →+* ℂ) (x : Fin (N + 1) → Ω)
    (c : Fin (N + 1)) (r : Fin (N + 1) → ℂ) (hreg : ∀ i, x i / x c ∈ S) (hval : ∀ i, φ ⟨_, hreg i⟩ = r i)
    (G : MRing (fun _ : Unit => Fin (N + 1))) :
    ∃ ha : ratEval x c G ∈ S, φ ⟨_, ha⟩ =
      MvPolynomial.eval (fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2) (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  induction G using MvPolynomial.induction_on with
  | C n =>
    have h : ratEval x c (MvPolynomial.C n) = ((n : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (n : S).2, ?_⟩
    have e : (⟨ratEval x c (MvPolynomial.C n), h ▸ (n : S).2⟩ : S) = (n : S) := Subtype.ext h
    rw [e]
    simp
  | add f g hf hg =>
    obtain ⟨ha, hA⟩ := hf
    obtain ⟨hb, hB⟩ := hg
    have h : ratEval x c (f + g) = ((⟨_, ha⟩ + ⟨_, hb⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f + g), h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2⟩ : S) = ⟨_, ha⟩ + ⟨_, hb⟩ := Subtype.ext h
    rw [e, map_add (f := _), hA, hB]
    simp
  | mul_X f i hf =>
    obtain ⟨ha, hA⟩ := hf
    have h : ratEval x c (f * MvPolynomial.X i) = ((⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f * MvPolynomial.X i), h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2⟩ : S) =
        ⟨_, ha⟩ * ⟨_, hreg i.2⟩ := Subtype.ext h
    rw [e, map_mul, hA, hval]
    simp

theorem mem_mcPts_span_bdGens_iff : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)), IsCptGen ξ →
    (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G)) →
    ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
      (w ∈ mcPts (Ideal.span (Mdl.bdGens ξ x B)) ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ X ξ N x B hξ hB z w hC
  obtain ⟨hu, hco⟩ := hC
  obtain ⟨c, hc⟩ := hu ()
  obtain ⟨hxc, hr⟩ := hco () c hc
  choose r hrV hrw using hr
  obtain ⟨h, -⟩ := hrV c
  obtain ⟨φ, hφ, hφu⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z h hξ
  have hreg : ∀ i, x i / x c ∈ regAt ξ ⟨centre z, h⟩ := fun i => ((hφ _ _).1 (hrV i)).choose
  have hval : ∀ i, φ ⟨_, hreg i⟩ = r i := fun i => ((hφ _ _).1 (hrV i)).choose_spec
  have hchart : InChart ξ x c ⟨centre z, h⟩ := ⟨hxc, hreg⟩
  have hp0 : Char0 ξ ⟨centre z, h⟩ := char_zero_centre_complex_point Ω X ξ z h hξ
  have hw0 : w ⟨(), c⟩ ≠ 0 := hc.ne_zero
  have hw : w = fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2 * w ⟨(), c⟩ := by
    funext ⟨u, i⟩
    exact hrw i

  have key : ∀ (G : MRing (fun _ : Unit => Fin (N + 1))) (d : ℕ), G.IsHomogeneous d →
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) G) = 0 ↔
        ¬ unitAt ξ ⟨centre z, h⟩ (ratEval x c G)) := by
    intro G d hG
    obtain ⟨ha, hA⟩ := exists_ratEval_val φ x c r hreg hval G
    have hu' := hφu ⟨_, ha⟩
    rw [hw, eval_map_mul_of_isHomogeneous hG, ← hA]
    simp only [mul_eq_zero, pow_eq_zero_iff', hw0, false_and, false_or]
    rw [← show IsUnit (φ ⟨_, ha⟩) ↔ unitAt ξ ⟨centre z, h⟩ (ratEval x c G) from hu', isUnit_iff_ne_zero, not_not]
  constructor
  · rintro ⟨-, hv⟩
    refine ⟨h, ?_⟩
    by_contra hpB
    obtain ⟨G, hG, hGu⟩ := hB c ⟨centre z, h⟩ hp0 hchart hpB
    obtain ⟨d, hd, -⟩ := id hG
    exact (key G d hd).1 (hv G (Ideal.subset_span hG)) hGu
  · rintro ⟨h', hpB⟩
    refine ⟨fun _ => ⟨c, hw0⟩, fun f hf => ?_⟩
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨d, hd, hv⟩ := hG
      exact (key G d hd).2 (hv c _ hpB hchart)
    | zero => simp
    | add f g _ _ hf hg => simp [hf, hg]
    | smul a f _ hf => simp [hf]

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.TwistLine

theorem twisted_hermitian_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) :=
  @PositivityTheory.Xgn.multihomogeneous_line_bundle

end GlobalTheory.CompanionTheory.TwistLine
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.relevant_prime_over_multihomog : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → z ∈ ReciprocityTheory.ChartRestriction.G.Geo.mcPts P → ∃ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime ∧ P ≤ W ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W ∧ (∀ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) ∧ ∀ s : MvPolynomial (Σ k, ι k) ℤ, s ∉ W → ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ) (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a s)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime | exact GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem _root_.GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  first | exact @PositivityTheory.HtPt.Mi.open_crit | exact PositivityTheory.HtPt.Mi.open_crit
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_comp_surjective_of_open_part :
    ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens)
      (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW →
      jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  intro S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx
  have := he
  have hO : IsOpenImmersion (W'.ι ≫ f) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y) :=
    Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y
  have := (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y
  have hι : Function.Bijective (W'.ι.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have key : Function.Surjective (f.stalkMap (W'.ι y)) := by
    intro t
    obtain ⟨s, hs⟩ := h1 (W'.ι.stalkMap y t)
    refine ⟨s, hι.1 ?_⟩
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  rw [Scheme.Hom.stalkMap_comp]
  exact key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.smooth_scheme_stalks_domains : ∀ (K : Type) [Field K] (e : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K), SmoothOfRelativeDimension e g → ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | exact GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.reversed_dual_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | exact GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | (intros; apply GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.chart_bundle_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | exact GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg <;> assumption)
end
