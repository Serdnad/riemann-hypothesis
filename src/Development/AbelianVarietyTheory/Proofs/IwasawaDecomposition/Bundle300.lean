module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle202
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

open NumberField IsDedekindDomain Matrix in
private theorem sum_smulRight_finBasis_mul_smulRight_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (w : W) (ℓ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ∑ i, ℓ.smulRight (Module.finBasis ℂ W i) * ((Module.finBasis ℂ W).coord i).smulRight w = 1 := by
  ext x
  simpa [h] using (Module.finBasis ℂ W).sum_repr x

open NumberField IsDedekindDomain Matrix in
private theorem exists_dual_algHom_smulRight_apply_ne_zero {W V : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (w : W) (ℓ : Module.Dual ℂ W)
    (h : ℓ w = 1) (Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V) {y : V} (hy : y ≠ 0) :
    ∃ φ : Module.Dual ℂ W, Φ (φ.smulRight w) y ≠ 0 := by
  by_contra! hzero
  apply hy
  calc y = Φ 1 y := by simp
    _ = ∑ i, Φ (ℓ.smulRight (Module.finBasis ℂ W i))
          (Φ (((Module.finBasis ℂ W).coord i).smulRight w) y) := by

        rw [← sum_smulRight_finBasis_mul_smulRight_eq_one w ℓ h, map_sum, LinearMap.sum_apply]
        simp only [map_mul, Module.End.mul_apply]
    _ = 0 := by simp [hzero]

open NumberField IsDedekindDomain Matrix in
private theorem smulRight_mul_smulRight_of_apply_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    (w : W) (ℓ φ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ℓ.smulRight w * φ.smulRight w = φ.smulRight w := by
  ext x
  simp [h]


open NumberField IsDedekindDomain Matrix in
theorem _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector :
    ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
      [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) →
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  intro ι _ Wv _ _ _ V _ _ Φ w ℓ _ hℓ hcomm
  classical
  have key : ∀ s : Finset ι, ∃ y : V, y ≠ 0 ∧ ∀ v ∈ s, Φ v ((ℓ v).smulRight (w v)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y, hy⟩ := exists_ne (0 : V)
      exact ⟨y, hy, by simp⟩
    | insert v s hv ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨φ, hφ⟩ := exists_dual_algHom_smulRight_apply_ne_zero (w v) (ℓ v) (hℓ v) (Φ v) hy0
      refine ⟨Φ v (φ.smulRight (w v)) y, hφ, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← Module.End.mul_apply, ← map_mul,
          smulRight_mul_smulRight_of_apply_eq_one _ _ _ (hℓ u)]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        rw [← Module.End.mul_apply, (hcomm u v huv _ _).eq, Module.End.mul_apply, hy u hu]
  obtain ⟨y, hy0, hy⟩ := key Finset.univ
  exact ⟨y, hy0, fun v => hy v (Finset.mem_univ v)⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add (f := _)]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
end
