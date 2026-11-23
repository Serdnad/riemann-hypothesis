module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle114
public import Formalism.LocalToGlobal.Divisibility.RowLat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.FrobeniusOrbits.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  first | exact @GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | exact GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | (intros; apply GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  first | exact @GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral | exact GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral | (intros; apply GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFinLoc.finite_image_tSet_loc | exact GlobalTheory.TSetFinLoc.finite_image_tSet_loc | (intros; apply GlobalTheory.TSetFinLoc.finite_image_tSet_loc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.residue_field_over_place_alg_closure : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first | exact @GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | exact GlobalTheory.ResidueBar.residueField_ringEquiv_fbar | (intros; apply GlobalTheory.ResidueBar.residueField_ringEquiv_fbar <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_divisible_of_kernel_powers : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l, (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) → (l : Per.Acris0 l) ∣ s := by
  first | exact @GlobalTheory.MemLoc.dvd_of_forall_fil_add | exact GlobalTheory.MemLoc.dvd_of_forall_fil_add | (intros; apply GlobalTheory.MemLoc.dvd_of_forall_fil_add <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  first | exact @GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | exact GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | (intros; apply GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
    (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  first | exact @GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks | exact GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks | (intros; apply GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.dBlk_eq_blkDet_coarse : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  first | exact @GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | exact GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | (intros; apply GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  first | exact @GlobalTheory.topBlock_eq_one_iff_mem_colHK | exact GlobalTheory.topBlock_eq_one_iff_mem_colHK | (intros; apply GlobalTheory.topBlock_eq_one_iff_mem_colHK <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV


theorem _root_.GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  first | exact @GlobalTheory.reduction_blockTri_detDD | exact GlobalTheory.reduction_blockTri_detDD | (intros; apply GlobalTheory.reduction_blockTri_detDD <;> assumption)
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.isAbsIrrChar_map_ringHom : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G] (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  first | exact @GlobalTheory.AbsIrrMap.isAbsIrrChar_map | exact GlobalTheory.AbsIrrMap.isAbsIrrChar_map | (intros; apply GlobalTheory.AbsIrrMap.isAbsIrrChar_map <;> assumption)
end

section

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

section Csd

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem csum_coords (u v : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm u : S.Cl → S.V) (S.basis.equivFun.symm v : S.Cl → S.V) =
      ∑ i, ∑ j, star (u i) * S.H i j * v j := by

  simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, CSD.csum, CSD.H,
  Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply,
  LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem mem_nabLat_iff (x : Fin S.dim → K) :
    x ∈ S.nabLat ↔ ∀ c, (S.basis.equivFun.symm x : S.Cl → S.V) c ∈ S.Nab c := by
  simp [CSD.nabLat, valLatF, Submodule.mem_pi, CSD.I]

end Csd

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

theorem forms_of_semilinear (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  set C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := Matrix.of fun i k => B'.S.basis.repr (L (B.S.basis k)) i with hCdef

  have hcol : ∀ k, B'.S.basis.equivFun.symm (fun i => C i k) = L (B.S.basis k) := by
    intro k
    rw [LinearEquiv.symm_apply_eq]
    ext i
    simp [hCdef]
  have hC : ∀ y, C *ᵥ y = B'.S.basis.equivFun (∑ k, y k • L (B.S.basis k)) := by
    intro y
    ext i
    simp [hCdef, Matrix.mulVec, dotProduct, mul_comm]
  have hLsum : ∀ x : Fin B.S.dim → K, L (B.S.basis.equivFun.symm x) = ∑ k, φ (x k) • L (B.S.basis k) := by
    intro x

    rw [Basis.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _
  have hT : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) = B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    rw [hC, hLsum]
  have hTf : ∀ f : B.S.Forms, C *ᵥ (fun k => φ (B.S.basis.repr f k)) = ⇑(B'.S.basis.repr (L f)) := by
    intro f
    have := hT (B.S.basis.equivFun f)
    simpa using this
  refine ⟨C, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    have h0 : ∑ k, (y₁ - y₂) k • L (B.S.basis k) = 0 := by
      have : C *ᵥ (y₁ - y₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
      rw [hC] at this
      exact (LinearEquiv.map_eq_zero_iff _).mp this
    have := Fintype.linearIndependent_iff.mp hli _ h0
    funext k
    exact sub_eq_zero.mp (this k)
  ·
    intro y
    have hmem : B'.S.basis.equivFun.symm y ∈ Submodule.span K' (Set.range fun k => L (B.S.basis k)) := hsp trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K').mp hmem
    refine ⟨c, ?_⟩
    rw [hC, hc, LinearEquiv.apply_symm_apply]
  ·
    ext a b
    have h1 := hcs (B.S.basis a) (B.S.basis b)
    rw [← hcol a, ← hcol b, csum_coords] at h1
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply] at h1 ⊢
    rw [← h1, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Matrix.of_apply]
  ·
    intro g
    have hv : ∀ f : B.S.Forms, (B'.S.actMat B'.r (e g) * C) *ᵥ (fun k => φ (B.S.basis.repr f k)) =
        (C * (B.S.actMat B.r g).map φ) *ᵥ (fun k => φ (B.S.basis.repr f k)) := by
      intro f
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTf]
      have h2 : (B.S.actMat B.r g).map φ *ᵥ (fun k => φ (B.S.basis.repr f k)) =
          fun k => φ (B.S.basis.repr (B.r g f) k) := by
        funext k
        rw [show (fun k => φ (B.S.basis.repr f k)) = φ ∘ (B.S.basis.repr f) from rfl, ← RingHom.map_mulVec φ]
        simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr]
      rw [h2, hTf]
      simp only [CSD.actMat, LinearMap.toMatrix_mulVec_repr, hact]
    ext i k
    have hs : (fun j => φ (B.S.basis.repr (B.S.basis k) j)) = Pi.single k 1 := by
      funext j
      by_cases h : j = k
      · subst h; simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    have := congrFun (hv (B.S.basis k)) i
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  ·
    let eO := (B'.S.basis.equivFun).restrictScalars (𝓞 K')
    have himg : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        eO '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨L (B.S.basis.equivFun.symm x), ⟨_, (mem_nabLat_iff _ _).mp hx, rfl⟩, (hT x).symm⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff _ _).mpr (by simpa using hf), ?_⟩
        show C *ᵥ (fun k => φ (B.S.basis.equivFun f k)) = _
        rw [hT, LinearEquiv.symm_apply_apply]
        rfl
    ext y
    rw [himg, ← LinearEquiv.coe_coe, Submodule.span_image, Submodule.mem_map_equiv, ← hnab, mem_nabLat_iff]
    rfl
  ·
    rw [hZ, BlockDat.coord, BlockDat.coord, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
    refine Set.image_congr fun f _ => ?_
    rw [hT]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.DefLatBC
end
end
