module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Mathlib.Algebra.Module.SpanRankOperations
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle001
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.RegSmooth

theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top,
    ← Module.finrank_eq_spanFinrank_of_free]
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R))
    (Submodule.topEquiv (R := R) (M := M))).finrank_eq

theorem spanFinrank_top_tensor_eq {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    (⊤ : Submodule B (B ⊗[A] N)).spanFinrank = (⊤ : Submodule A N).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B)
    (ResidueField B) N
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
    (ResidueField B) N
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

theorem spanFinrank_map_eq_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).spanFinrank = (⊤ : Submodule B (B ⊗[A] I)).spanFinrank := by
  let g : B ⊗[A] I →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  have hg : Function.Injective g := by
    have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    exact (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1
  have hr : Submodule.map g ⊤ = I.map (algebraMap A B) := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      induction x with
      | tmul b i =>
        have : g (b ⊗ₜ i) = b * algebraMap A B i := by
          simp [g, Algebra.smul_def, mul_comm]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩
      simp [g, Algebra.smul_def]
  rw [← hr, Submodule.spanFinrank_map_eq_of_injective g hg]

theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at e
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal h
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩
  have e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    rw [← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]
  rw [e, hd]
  exact ((isRegularLocalRing_iff B).mp inferInstance).le

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal' {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hf : φ.Flat)
    (h : (maximalIdeal A).map φ = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  algebraize [φ]
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have : algebraMap A B a ∈ maximalIdeal B := h ▸ Ideal.mem_map_of_mem _ hm
    exact (mem_maximalIdeal _).1 this ha
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal h

theorem isRegularLocalRing_of_isEtaleCompletion {A B : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (h : GlobalTheory.Toroidal.IsEtaleCompletion φ) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1

theorem smoothOfRelativeDimension_of_isRegularLocalRing {F : Type} [Field F] [PerfectField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] (n : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    X.affineOpenCover.openCover fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of F ⟶ R := Spec.preimage (x ≫ f)
  letI : Algebra F R := φ.hom.toAlgebra
  have hφ : x ≫ f = spMap (algebraMap F R) := (Spec.map_preimage (x ≫ f)).symm
  change SmoothOfRelativeDimension n (x ≫ f)
  rw [hφ]
  have hft : LocallyOfFiniteType (spMap (algebraMap F R)) := by rw [← hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType F R := RingHom.finiteType_algebraMap.mp hft
  refine GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_
  let y : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  have hcl : IsClosed ({x y} : Set X) := by
    have h1 : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
    have he := x.isOpenEmbedding
    have hlc := IsLocallyClosed.image h1.isLocallyClosed he.isInducing
      he.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  obtain ⟨h1, h2⟩ := h (x y) hcl
  let e := (asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

end GlobalTheory.RegSmooth
end

section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.ConeDim

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {N : ℕ}

theorem isAlgebraic_of_closure_eq_top (y : Fin N → Ω) (hy : y ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap k Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤)
    (A : Subalgebra k (Polynomial Ω)) (hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A) :
    Algebra.IsAlgebraic A (Polynomial Ω) := by
  classical
  let ι : Polynomial Ω →+* FractionRing (Polynomial Ω) := algebraMap _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let L : Subfield (FractionRing (Polynomial Ω)) := Subfield.closure (ι '' (A : Set (Polynomial Ω)))
  have hA : ∀ a ∈ A, ι a ∈ L := fun a ha => Subfield.subset_closure ⟨a, ha, rfl⟩
  have hne : ∀ j, y j ≠ 0 → ι (Polynomial.X * Polynomial.C (y j)) ≠ 0 := fun j hj =>
    (map_ne_zero_iff ι hι).2 (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.2 hj))
  let M : Subfield Ω := L.comap (ι.comp Polynomial.C)
  have hM : M = ⊤ := by
    refine top_unique (hgen ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨i, j, rfl⟩)
    · show ι (Polynomial.C (algebraMap k Ω c)) ∈ L
      rw [← Polynomial.algebraMap_apply]
      exact hA _ (A.algebraMap_mem c)
    · show ι (Polynomial.C (y i / y j)) ∈ L
      by_cases hj : y j = 0
      · rw [hj, div_zero, Polynomial.C_0, map_zero]
        exact zero_mem L
      · have e : ι (Polynomial.C (y i / y j)) =
            ι (Polynomial.X * Polynomial.C (y i)) / ι (Polynomial.X * Polynomial.C (y j)) := by
          rw [eq_div_iff (hne j hj), ← map_mul]
          congr 1
          rw [mul_left_comm, ← Polynomial.C_mul, div_mul_cancel₀ _ hj]
        rw [e]
        exact div_mem (hA _ (hXy i)) (hA _ (hXy j))
  have hC : ∀ c, ι (Polynomial.C c) ∈ L := fun c => by
    have h : c ∈ M := hM ▸ Subfield.mem_top c
    exact h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hX : ι Polynomial.X ∈ L := by
    have e : ι Polynomial.X = ι (Polynomial.X * Polynomial.C (y j)) * ι (Polynomial.C (y j)⁻¹) := by
      rw [← map_mul, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hj, Polynomial.C_1, mul_one]
    rw [e]
    exact mul_mem (hA _ (hXy j)) (hC _)
  have hall : ∀ p, ι p ∈ L := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hC c) (pow_mem hX n)
  have hcl : Subring.closure (ι '' (A : Set (Polynomial Ω))) ≤ (A.toSubring.map ι) :=
    Subring.closure_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
  refine ⟨fun p => ?_⟩
  obtain ⟨_, ha₀, _, hb₀, hab⟩ := Subfield.mem_closure_iff.1 (hall p)
  obtain ⟨a, ha, rfl⟩ := hcl ha₀
  obtain ⟨b, hb, rfl⟩ := hcl hb₀
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, div_zero, eq_comm, map_eq_zero_iff ι hι] at hab
    rw [hab]
    exact isAlgebraic_zero
  · have e : b * p = a := by
      apply hι
      rw [map_mul, ← hab, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).2 hb0)]
    refine ⟨Polynomial.C (⟨b, hb⟩ : A) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : A), fun h => hb0 ?_, ?_⟩
    · have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) h
      simp at this
      exact congrArg Subtype.val this
    · simp [e]

theorem ringKrullDim_imageIdeal_of_birational : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety →
    S.BasePointFree → S.Birational →
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  intro k _ S h hb ⟨η, hη, hr⟩
  have := HeightExists.isIntegral h
  let Ω := S.Y.residueField η
  let : Algebra k Ω := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt Ω := ⟨resPt η, S.comp_str _⟩
  set y : Fin S.N → Ω := S.coords (resPt η) with hy
  have hI : S.imageIdeal = coneIdeal k y :=
    imageIdeal_eq_coneIdeal_of_generic k Ω S x (by rw [ptOf_resPt]; exact hη) 1 y one_ne_zero
      (one_smul _ _).symm
  have hD : Algebra.trdeg k Ω = S.D :=
    (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth η
      fun z hz => (hz.antisymm (hη.specializes trivial)).eq).2
  rw [hI]
  have := isPrime_coneIdeal (K := k) y
  refine ringKrullDim_eq_of_trdeg_eq k _ ?_
  let f := Ideal.kerLiftAlg (coneMap k y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg k (MvPolynomial (Fin S.N) k ⧸ coneIdeal k y) = Algebra.trdeg k A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := ConeDim.isAlgebraic_of_closure_eq_top y (hb.coords_ne_zero _) hr A hXy
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (Polynomial Ω), ← trdeg_add_eq k Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, hD]
  norm_cast

end GlobalTheory.Adelic.ConeDim
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CentCpt

theorem twCent_inf_conjKK_le_cptPart (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E)
    (m q : GLw a w × GLw b w) :
    twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id _) m) := by
  rintro t ⟨ht, hK⟩
  apply Subgroup.subset_closure
  refine ⟨ht, ?_⟩
  have hc : IsCompact ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom :
      Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    refine ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2).image ?_
    show Continuous fun x : GLw a w × GLw b w => q * x * q⁻¹
    fun_prop
  have hz : (Subgroup.zpowers t : Set (GLw a w × GLw b w)) ⊆ _ :=
    (Subgroup.zpowers_le (H := ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom)).2 hK
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hz hc.isClosed)

end GlobalTheory.CentCpt
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

theorem _root_.GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  first | exact @GlobalTheory.OrbReindex.twOrb_eq_orbSum | exact GlobalTheory.OrbReindex.twOrb_eq_orbSum | (intros; apply GlobalTheory.OrbReindex.twOrb_eq_orbSum <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

theorem _root_.GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  first | exact @GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | exact GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | (intros; apply GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.subgroupAverage_prod_mul_eq_mul : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  first | exact @GlobalTheory.AvgProd.avg_prod | exact GlobalTheory.AvgProd.avg_prod | (intros; apply GlobalTheory.AvgProd.avg_prod <;> assumption)
end
