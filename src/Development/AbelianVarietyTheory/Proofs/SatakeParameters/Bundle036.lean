module

public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle026
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle029
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle030
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.AdjoinRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle001

@[expose] public section

section

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem latA_single_mem {ι : Type} [DecidableEq ι] (j i : ι) : (Pi.single j (1 : L) : ι → L) i ∈ Formalism.UG.intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem latA_dot_mem {ι : Type} [Fintype ι] {u w : ι → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : u ⬝ᵥ w ∈ Formalism.UG.intL L :=
  sum_mem fun i _ => mul_mem (hu i) (hw i)

theorem latA_sum {n m : ℕ} (c : Matrix (Fin n) (Fin n) L) (hc : c.det ≠ 0) (y : Matrix (Fin n) (Fin m) L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_square_matrix_span_columns_integral L n (Fin n ⊕ Fin m) (Matrix.fromCols c y)
  have key : ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
    intro v
    rw [← hb v]
    constructor
    · rintro ⟨u, w, hu, hw, rfl⟩
      refine ⟨Sum.elim u w, ?_, ?_⟩
      · rintro (i | i)
        · exact hu i
        · exact hw i
      · rw [Matrix.fromCols_mulVec_sumElim]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u ∘ Sum.inl, u ∘ Sum.inr, fun i => hu _, fun i => hu _, ?_⟩
      rw [← Matrix.fromCols_mulVec_sumElim, Sum.elim_comp_inl_inr]
  have hcol : ∀ j : Fin n, ∃ t : Fin n → L, c *ᵥ Pi.single j 1 = b *ᵥ t := by
    intro j
    obtain ⟨t, -, ht⟩ := (key (c *ᵥ Pi.single j 1)).1
      ⟨Pi.single j 1, 0, latA_single_mem j, fun _ => zero_mem _, by simp⟩
    exact ⟨t, ht⟩
  choose t ht using hcol
  have hT : b * (Matrix.of t)ᵀ = c := by
    ext i j
    have := congrFun (ht j) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    rfl
  have hdet : b.det ≠ 0 := by
    intro h
    apply hc
    rw [← hT, Matrix.det_mul, h, zero_mul]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero b hdet, key⟩

theorem latA_basis (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ)
    (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := latA_sum (1 : Matrix (Fin n) (Fin n) L) (by simp) xᵀ
  have hN : ∀ u : Fin n → L, ((∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L)) ↔
      ∀ j, ((b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u) j ∈ Formalism.UG.intL L := by
    intro u
    have dual : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) L) (t : Fin k → L), (M *ᵥ t) ⬝ᵥ u = t ⬝ᵥ (Mᵀ *ᵥ u) := by
      intro k M t
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    constructor
    · rintro ⟨h1, h2⟩ j
      obtain ⟨l, w, hl, hw, e⟩ := (hb ((b : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1)).2
        ⟨_, latA_single_mem j, rfl⟩
      have e2 := dual (b : Matrix (Fin n) (Fin n) L) (Pi.single j 1)
      rw [single_one_dotProduct, e, add_dotProduct, dual xᵀ, Matrix.one_mulVec, Matrix.transpose_transpose] at e2
      rw [← e2]
      exact add_mem (latA_dot_mem hl h1) (latA_dot_mem hw h2)
    · intro h
      refine ⟨fun i => ?_, fun k => ?_⟩
      · obtain ⟨t, ht, e⟩ := (hb (Pi.single i 1)).1
          ⟨Pi.single i 1, 0, latA_single_mem i, fun _ => zero_mem _, by
            rw [Matrix.one_mulVec, Matrix.mulVec_zero, add_zero]⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
      · obtain ⟨t, ht, e⟩ := (hb (xᵀ *ᵥ Pi.single k 1)).1
          ⟨0, Pi.single k 1, fun _ => zero_mem _, latA_single_mem k, by simp⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, dual xᵀ, Matrix.transpose_transpose, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
  have hmul : (b : Matrix (Fin n) (Fin n) L)ᵀ * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hmul' : ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (b : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hdet : (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨a, ha⟩ := latA_sum _ hdet y
  refine ⟨a, fun v => ?_⟩
  rw [← ha v]
  constructor
  · rintro ⟨u, w, h1, h2, hw, rfl⟩
    refine ⟨(b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u, w, (hN u).1 ⟨h1, h2⟩, hw, ?_⟩
    rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
  · rintro ⟨u, w, hu, hw, rfl⟩
    have := (hN (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u)).2 (by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]; exact hu)
    exact ⟨_, w, this.1, this.2, hw, rfl⟩

end GlobalTheory.Hk3.HoweG
end

section

namespace GlobalTheory

theorem freeAlgebra_compHom_isScalarTower {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by
  letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom
  refine ⟨fun c r w => ?_⟩
  show φ (c • r) w = c • φ r w
  rw [map_smul]
  rfl

theorem endFamily_cancel : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  intro k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩
  let φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V := FreeAlgebra.lift k a
  let φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V' := FreeAlgebra.lift k b
  let φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U := FreeAlgebra.lift k c
  letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom
  letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom
  letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom
  haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa
  haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb
  haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc
  haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance

  have key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2) := by
    intro r
    induction r using FreeAlgebra.induction with
    | grade0 s =>
      intro x
      simp only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]
      exact e.map_smul s x
    | grade1 i =>
      intro x
      have := he i x
      simp only [φa, φb, φc, FreeAlgebra.lift_ι_apply]
      simpa using this
    | mul r s hr hs =>
      intro x
      have h1 := hs x
      have h2 := hr (φa s x.1, φc s x.2)
      simp only [map_mul, Module.End.mul_apply]
      rw [h2, h1]
    | add r s hr hs =>
      intro x
      have h1 := hr x
      have h2 := hs x
      have hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2)
          = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2) := by
        simp [map_add (f := _)]
      rw [hsum, map_add (f := _), h1, h2]
      simp [map_add (f := _)]
  let eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U) :=
    { e.toAddEquiv with
      map_smul' := fun r x => key r x }
  obtain ⟨f⟩ := GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩
  refine ⟨f.restrictScalars k, fun i x => ?_⟩
  have h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x := f.map_smul _ _
  change f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h
  simp only [φa, φb, FreeAlgebra.lift_ι_apply] at h
  exact h

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.InertNorm

theorem isAdicComplete_map_of_finite {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsHausdorff I R := IsHausdorff.of_le_jacobson I R (IsAdicComplete.le_jacobson I)
  have : IsPrecomplete I R := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I R
  exact ⟨⟩

theorem finite_quotient_map_of_finite {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by
  have : Module.Finite O (R ⧸ I.map (algebraMap O R)) := inferInstance
  have : Module.Finite (O ⧸ I) (R ⧸ I.map (algebraMap O R)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
  exact Module.finite_of_finite (O ⧸ I)

theorem exists_dvd_mul_map_sub_X : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  intro O _ _ I _ _ c hcc hcI hω f hf hfc hf0
  have : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  let J : Ideal (AdjoinRoot f) := I.map (algebraMap O (AdjoinRoot f))
  have : IsAdicComplete J (AdjoinRoot f) := isAdicComplete_map_of_finite I (AdjoinRoot f)
  have : Finite (AdjoinRoot f ⧸ J) := finite_quotient_map_of_finite I (AdjoinRoot f)

  have hev : f.eval₂ ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) = 0 := by
    rw [← Polynomial.eval₂_map, hfc, AdjoinRoot.eval₂_root]
  let c' : AdjoinRoot f →+* AdjoinRoot f :=
    AdjoinRoot.lift ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) hev
  have hc'mk : ∀ p : Polynomial O, c' (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map c) := by
    intro p
    simp only [c', AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
  have hc'of : ∀ x : O, c' (algebraMap O (AdjoinRoot f) x) = algebraMap O (AdjoinRoot f) (c x) := by
    intro x
    simp only [AdjoinRoot.algebraMap_eq, c', AdjoinRoot.lift_of, RingHom.comp_apply]
  have hcomp : c.comp c = RingHom.id O := RingHom.ext hcc
  have hinv : ∀ y, c' (c' y) = y := by
    intro y
    induction y using AdjoinRoot.induction_on with
    | ih p => rw [hc'mk, hc'mk, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hJ : ∀ y ∈ J, c' y ∈ J := by
    have : J ≤ J.comap c' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hc'of]
      exact Ideal.mem_map_of_mem _ (hcI x hx)
    exact fun y hy => this hy
  have hω' : ∃ ω, IsUnit (ω - c' ω) := by
    obtain ⟨ω, hu⟩ := hω
    refine ⟨algebraMap O (AdjoinRoot f) ω, ?_⟩
    rw [hc'of, ← map_sub]
    exact hu.map _
  have hroot : c' (AdjoinRoot.root f) = AdjoinRoot.root f := AdjoinRoot.lift_root _

  have hunit : IsUnit (AdjoinRoot.root f) := by
    have h0 : (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 := by simp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hm : AdjoinRoot.root f * AdjoinRoot.mk f q = -AdjoinRoot.of f (f.coeff 0) := by
      have := congrArg (AdjoinRoot.mk f) hq
      rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, zero_sub] at this
      exact this.symm
    exact isUnit_of_mul_isUnit_left (hm ▸ (hf0.map (AdjoinRoot.of f)).neg)
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_norm_eq_fixed_unit_henselian (AdjoinRoot f) J c' hinv hJ hω' (AdjoinRoot.root f) hroot hunit
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, ← hc'mk, hx, AdjoinRoot.mk_X, sub_self]

end GlobalTheory.InertNorm
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem finiteDimensional_of_finite_subring_fraction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L)
      (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite →
      (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  intro K L _ _ _ B B' φ hφ hfin hfrac
  letI : Algebra B B' := φ.toAlgebra
  have hMF : Module.Finite B B' := hfin
  obtain ⟨s, hs⟩ := hMF.fg_top

  have hB'span : ∀ x : B', (x : L) ∈ Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    intro x
    have hx : x ∈ Submodule.span B (s : Set B') := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul b u _ hu =>
      have : ((b • u : B') : L) = (b : K) • (u : L) := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Subring.coe_mul, hφ, Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ hu
  let S : Subalgebra K L := Algebra.adjoin K (B' : Set L)
  have hSsub : Subalgebra.toSubmodule S =
      Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    apply le_antisymm
    · rw [Algebra.adjoin_eq_span]
      apply Submodule.span_le.mpr
      intro y hy
      have hy' : y ∈ B'.toSubmonoid := by
        rw [← Submonoid.closure_eq B'.toSubmonoid]; exact hy
      exact hB'span ⟨y, hy'⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, _, rfl⟩
      exact Algebra.subset_adjoin z.2
  have hFG : (Subalgebra.toSubmodule S).FG := by
    rw [hSsub]
    exact Submodule.fg_span ((s.finite_toSet).image _)
  have hB'S : ∀ y ∈ B', y ∈ S := fun y hy => Algebra.subset_adjoin hy
  have htop : ∀ y : L, y ∈ S := by
    intro y
    obtain ⟨a, ha, b, hb, hb0, hyb⟩ := hfrac y
    have hbinv : b⁻¹ ∈ S := by
      have hint : IsIntegral K b := IsIntegral.of_mem_of_fg S hFG b (hB'S b hb)
      exact Subalgebra.inv_mem_of_algebraic (A := S) (x := ⟨b, hB'S b hb⟩) hint.isAlgebraic
    have : y = a * b⁻¹ := by rw [← hyb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
    rw [this]; exact S.mul_mem (hB'S a ha) hbinv
  refine ⟨?_⟩
  obtain ⟨t, ht⟩ := hFG
  refine ⟨t, ?_⟩
  rw [ht, eq_top_iff]
  intro y _
  exact htop y

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.ThetaLiftGL

theorem compactOpen_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.ThetaLiftGL
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem integralClosure_of_finite_map : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hfin hB hB' hK hL
  letI : Algebra B B' := φ.toAlgebra
  haveI : IsScalarTower B B' L := IsScalarTower.of_algebraMap_eq fun x => (hφ x).symm
  have fracK : IsFractionRing B K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hK z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have fracL : IsFractionRing B' L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hL z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have hint : (algebraMap B B').IsIntegral := RingHom.Finite.to_isIntegral hfin
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : IsIntegral B (⟨y, hy⟩ : B') := hint _
    have := h1.algebraMap (B := L)
    simpa using this
  · obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff K).mp hB hx
    rw [← hc]; exact c.2
  · have h2 : IsIntegral B' y := hy.tower_top
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff L).mp hB' h2
    rw [← hc]; exact c.2

end GlobalTheory.W1
end
