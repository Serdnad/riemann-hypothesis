module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoEmbConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkRes :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), c ∈ Z1 ρ → IsBK l ρ c → (fun s : G K Ω => c (s.restrictScalars ℚ)) ∈ Z1 (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧ IsBK l (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (fun s : G K Ω => c (s.restrictScalars ℚ)) := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ _ _ _ _ _ _ ρ c hc hbk
  obtain ⟨hcont, hcc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  have hcont' : Continuous fun s : G K Ω => c (s.restrictScalars ℚ) :=
    hcont.comp (continuous_restrictScalarsHom ℚ K Ω)
  have hcc' : ∀ s t : G K Ω, c ((s * t).restrictScalars ℚ) =
      c (s.restrictScalars ℚ) + ρ (s.restrictScalars ℚ) (c (t.restrictScalars ℚ)) :=
    fun s t => hcc (s.restrictScalars ℚ) (t.restrictScalars ℚ)
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨hcont', hcc'⟩,
    UpperTheory.V.X.Kato.resAway l K Ω C V ρ c hcc hbk.away, fun τ => ?_⟩
  obtain ⟨j₀, -, -, x, hx⟩ := hbk.above (τ.comp (algebraMap ℚ K))
  obtain ⟨g, hg⟩ := UpperTheory.V.X.Kato.embConj l K Ω j₀ τ
  refine ⟨j₀.comp (g : Ω →+* Ω), hg, ⟨hcont'.comp (continuous_fst.comp continuous_subtype_val),
    fun s t => hcc' s.1.1 t.1.1⟩,
    TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id x - c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l), ?_⟩
  rintro ⟨⟨s, σ⟩, hs⟩
  have ht : (g * s.restrictScalars ℚ * g⁻¹, σ) ∈ decJ ℚ j₀ := by
    intro y
    have h := hs (g⁻¹ y)
    change σ (j₀ (g (g.symm y))) = j₀ (g (s (g.symm y))) at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h
  have h1 := hx ⟨_, ht⟩
  change c (s.restrictScalars ℚ) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (s.restrictScalars ℚ)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap _ - _
  change c (g * s.restrictScalars ℚ * g⁻¹) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (g * s.restrictScalars ℚ * g⁻¹))
      ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap x - x at h1
  generalize s.restrictScalars ℚ = u at h1 ⊢
  have e1 : g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ := by group
  have e2 := hcc g⁻¹ (g * u * g⁻¹)
  rw [e1, hcc] at e2
  have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
      TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id
        (TensorProduct.AlgebraTensorModule.map (ρ (g * u * g⁻¹)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap y) =
      TensorProduct.AlgebraTensorModule.map (ρ u) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap
        (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹)
    (LinearMap.id : UpperTheory.V.Loc.Bcr l →ₗ[ℚ_[l]] UpperTheory.V.Loc.Bcr l)) h1
  rw [map_sub, key, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h2
  rw [map_sub, TensorProduct.AlgebraTensorModule.map_tmul, eq_sub_of_add_eq e2, TensorProduct.sub_tmul,
    TensorProduct.add_tmul, h2]
  simp only [AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_one]
  abel
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.conj :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep r') := by
  intro l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk
  let f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l) :=
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]
  have hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ => rfl
  have hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x,
      Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ _ _ => rfl
  have hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x) := by
    intro g x
    rw [hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]
    congr 2
    group
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy
    rwa [hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩
    rw [hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcont : Continuous (fun g => f (c g)) := by
    simp only [hfa]
    exact continuous_const.matrix_mulVec hc.1
  have hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r) := by
    refine ⟨hcont, fun g g' => ?_⟩
    have h1 := congrArg f (hc.2 g g')
    simpa only [map_add (f := _), hf] using h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))
  obtain ⟨m', rfl⟩ := hsurj m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩
  have := hm g
  simp only [map_sub, hf]
  exact this
end
