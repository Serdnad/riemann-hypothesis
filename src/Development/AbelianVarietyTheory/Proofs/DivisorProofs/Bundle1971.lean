module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
public import GroundTheory.GlobalFields.Adele.Bundle002
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

namespace GlobalTheory.CondLESplit

open ValuativeRel

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))

theorem valued_unifAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have he := isEquiv_Fv v
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ' : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    he.lt_one_iff_lt_one.1 (hϖ ▸ uniformizer_lt_one)
  apply le_antisymm
  · have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · rw [← hπ']
    have hπ1 : valuation (Fv F v) ((π : F) : Fv F v) < 1 := by
      refine he.lt_one_iff_lt_one.2 ?_
      rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    exact (he _ _).1 (hϖ ▸ le_uniformizer_iff.2 hπ1)

end GlobalTheory.CondLESplit

open GlobalTheory.CondLESplit in
theorem GlobalTheory.CondLESplit.condLE_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (ρ : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ →* ℂˣ) (n : ℕ),
    GlobalTheory.SplitFlip.CondLE (unifAt v) n (ρ.comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔
      ∀ x : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ, Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) x →
        Valued.v ((x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρ x = 1 := by
  intro F E _ _ _ _ _ v τ ρ n
  set hw := GlobalTheory.AdelicU.splitPrime_under τ
  set f := GlobalTheory.LFun.complMap hw
  have he := isEquiv_Fv v
  have hval : ∀ a : Fv F v, Valued.v (f a) = Valued.v a := GlobalTheory.LFun.SplitTie.valued_complMap τ hw
  have hbij : Function.Bijective f := GlobalTheory.LFun.SplitTie.complMap_bijective τ hw
  have key : ∀ y : (Fv F v)ˣ, y ∈ GlobalTheory.SplitFlip.unitCong (unifAt v ^ n) ↔
      (Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map f.toMonoidHom y) ∧
        Valued.v (((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
          (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) := by
    intro y
    have h1 : ((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
        (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) = f y := rfl
    have hp : Valued.v (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v) = WithZero.exp (-(n : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, map_pow, valued_unifAt, ← WithZero.exp_nsmul]
      congr 1; simp
    show (ValuativeRel.valuation (Fv F v) (y : Fv F v) = 1 ∧ ValuativeRel.valuation (Fv F v) ((y : Fv F v) - 1) ≤
        ValuativeRel.valuation (Fv F v) (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v)) ↔ _
    unfold Formalism.L2.Host.IsUnitAt
    rw [h1, he.eq_one_iff_eq_one, he, hp, ← map_one f, ← map_sub, hval, hval]
  constructor
  · intro h x hx1 hx2
    obtain ⟨a, ha⟩ := hbij.2 (x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero] at ha; exact x.ne_zero ha.symm
    set y := Units.mk0 a ha0
    have hy : Units.map f.toMonoidHom y = x := Units.ext ha
    have := h y ((key y).2 (hy ▸ ⟨hx1, hx2⟩))
    rw [← hy]; exact this
  · intro h y hy
    exact h _ ((key y).1 hy).1 ((key y).1 hy).2
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.RatAnnihF

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] e) = (1 : AF F) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem psiV_exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra h
  push_neg at h
  refine GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (DFunLike.ext _ _ fun t => ?_)
  rw [AddChar.one_apply]
  exact h t

theorem adele_rat_of_isGood {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (a : AF F)
    (h : ∀ c : F, B.ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨⟨θ, hθ⟩, -⟩ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ w, θ w (x ⊗ₜ[F] (1 : E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  have hL : ∀ x, L x = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) :=
    fun x => GlobalTheory.StdCharWeilDatum.sum_infFam B θ hθ x
  refine GlobalTheory.RatAnnih.adele_rat (GlobalTheory.StdCharWeilDatum.isCharAF hB.std) (psiV_exists_ne_one hB.std) L
    (continuous_finsetSum _ fun w _ => (hθ w).2) (fun x => ?_) (fun x => ?_) a h
  · rw [hL]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) x) = mixedEmbedding F x := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [e, GlobalTheory.LatVacArith.trace_mixedEmbedding]
    exact Complex.ofReal_ratCast _
  · show B.ψ (pairA F x 0) = _
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA hB.std, hL]
    congr 1
    ring

theorem exists_symplOF_eq (σ : E →ₐ[F] E) (hσ : Function.Surjective σ) {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT)
    {ξ₀ : E} (hξ : ξ₀ ≠ 0) (x : WOF F E nS nT) (i : Fin nT) (j : Fin nS) (e : E) :
    ∃ γ ∈ ratLF F E nS nT, symplOF σ JS JT ξ₀ x γ = Algebra.trace (AF F) (AEF F E) (incAF F E e * x i j) := by
  let g := Function.surjInv hσ
  let P := JS * Matrix.single j i (ξ₀⁻¹ * e) * JT⁻¹
  refine ⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c)), ⟨_, rfl⟩, ?_⟩
  have h := GlobalTheory.RatAnnih.sum_single (incAF F E) JS JT (isUnit_iff_ne_zero.2 hS.2) (isUnit_iff_ne_zero.2 hT.2) j i
    (ξ₀⁻¹ * e) x
  have h2 : hOF σ JS JT x ((incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c))) =
      incAF F E (ξ₀⁻¹ * e) * x i j := by
    rw [← h, hOF]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, g, Function.surjInv_eq hσ]
    rfl
  rw [symplOF, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ hξ]

theorem symplOF_rat (σ : E →ₐ[F] E) [Module.Finite F E] {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (M N : Matrix (Fin nT) (Fin nS) E) :
    ∃ a : F, symplOF σ JS JT ξ₀ ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      algebraMap F (AF F) a := by
  refine ⟨Algebra.trace F E (ξ₀ * ∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a), ?_⟩
  have h : hOF σ JS JT ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      incAF F E (∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hOF, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, map_sum, map_mul]
  rw [symplOF, h, ← map_mul]
  show Algebra.trace (AF F) (AEF F E) ((1 : AF F) ⊗ₜ[F] _) = _
  rw [GlobalTheory.LatVac.trace_tmul, one_mul]
end

theorem ratLF_annihilator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ x
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  have hσ : Function.Surjective σ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  constructor
  · intro h
    have hent : ∀ i j, ∃ e : E, x i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => adele_rat_of_isGood hB _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplOF_eq σ hσ hS hT hξ x i j (c • e)
        exact (congrArg B.ψ ((GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    refine ⟨Matrix.of M, Matrix.ext fun i j => ?_⟩
    rw [hM i j]
    rfl
  · rintro ⟨M, rfl⟩ _ ⟨N, rfl⟩
    obtain ⟨a, ha⟩ := symplOF_rat σ JS JT ξ₀ M N
    rw [ha]
    exact (GlobalTheory.StdCharWeilDatum.isCharAF hB.std).2.2.1 a

end GlobalTheory.RatAnnihF
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Topology

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_zero : pairA F 0 (0 : Af F) = 0 := Prod.ext rfl rfl

theorem pairA_zero_neg (b : Af F) : pairA F 0 (-b) = -pairA F 0 b :=
  Prod.ext (neg_zero (G := Ainf F)).symm rfl

theorem algebraMap_mul_inv {a : F} (ha : a ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) a * algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ ha, map_one]

def ann (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}
  zero_mem' := fun y _ => by
    show ψ (pairA F 0 (0 ⬝ᵥ y)) = 1
    rw [zero_dotProduct, pairA_zero_zero, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb y hy => by
    show ψ (pairA F 0 ((a + b) ⬝ᵥ y)) = 1
    rw [add_dotProduct, GlobalTheory.AnnCompactStd.pairA_zero_add, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  neg_mem' := fun {a} ha y hy => by
    show ψ (pairA F 0 ((-a) ⬝ᵥ y)) = 1
    rw [neg_dotProduct, pairA_zero_neg, AddChar.map_neg_eq_inv, ha y hy, inv_one]

theorem mem_ann {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)}
    {x : κ → FiniteAdeleRing (𝓞 F) F} : x ∈ ann ψ κ L ↔ ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1 := Iff.rfl

def scaledInt (κ : Type) (a : FiniteAdeleRing (𝓞 F) F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {y | ∀ i, a * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by
    show a * 0 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_zero]; exact Subring.zero_mem _
  add_mem' := fun {u v} hu hv i => by
    show a * (u i + v i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_add]; exact Subring.add_mem _ (hu i) (hv i)
  neg_mem' := fun {u} hu i => by
    show a * (-u i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_neg]; exact Subring.neg_mem _ (hu i)

theorem isOpen_scaledInt (κ : Type) [Fintype κ] (a : FiniteAdeleRing (𝓞 F) F) :
    IsOpen (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => a * y i) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext y; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.FinSepChar

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem exists_compact_open_separating {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) : ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.AnnCompactStd.exists_mul_mem_of_forall hψ
  obtain ⟨e, he0, he⟩ := GlobalTheory.AnnCompactStd.exists_psi_fin_trivial hψ
  have hinj : ∀ a : 𝓞 F, a ≠ 0 → algebraMap (𝓞 F) F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  set cc := algebraMap (𝓞 F) F c with hcc
  set dd := algebraMap (𝓞 F) F d with hdd
  set ee := algebraMap (𝓞 F) F e with hee
  have hC := algebraMap_mul_inv (F := F) (hinj c hc0)
  have hD := algebraMap_mul_inv (F := F) (hinj d hd0)
  have hE := algebraMap_mul_inv (F := F) (hinj e he0)
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 F) F with hO

  set L := scaledInt (F := F) κ (ι cc * ι dd) with hL
  have hLo : IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
  refine ⟨ann ψ κ L, ?_, ?_, ?_, ?_⟩
  ·
    set δ := ι ee⁻¹ * (ι cc⁻¹ * ι dd⁻¹) with hδ
    have hVo : IsOpen (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
    have hVU : (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ ann ψ κ L := by
      intro x hx y hy
      have hsum : x ⬝ᵥ y = ι ee * ∑ i, (δ * x i) * ((ι cc * ι dd) * y i) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ]
        linear_combination (-(x i * y i * (ι cc * ι dd) * (ι cc⁻¹ * ι dd⁻¹))) * hE
          + (-(x i * y i * ι dd * ι dd⁻¹)) * hC + (-(x i * y i)) * hD
      rw [hsum]
      exact he _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (hy i))
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hVo.mem_nhds (scaledInt (F := F) κ δ).zero_mem) hVU)
  · exact GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ L hLo
  · intro x hx
    apply hsub
    intro i _
    have hz : ∀ s ∈ O, ψ (pairA F 0 ((ι cc⁻¹ * ι dd⁻¹ * x i) * s)) = 1 := by
      intro s hs
      have hy : (Pi.single i (ι cc⁻¹ * ι dd⁻¹ * s) : κ → FiniteAdeleRing (𝓞 F) F) ∈ L := by
        intro k
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same]
          have : ι cc * ι dd * (ι cc⁻¹ * ι dd⁻¹ * s) = s := by
            linear_combination (ι dd * ι dd⁻¹ * s) * hC + s * hD
          rw [this]; exact hs
        · rw [Pi.single_eq_of_ne hk, mul_zero]; exact Subring.zero_mem _
      have h1 := hx _ hy
      rw [dotProduct_single] at h1
      rw [show ι cc⁻¹ * ι dd⁻¹ * x i * s = x i * (ι cc⁻¹ * ι dd⁻¹ * s) by ring]
      exact h1
    have h2 := hc _ hz
    have h3 := hd _ h2
    have h4 : ι dd * (ι cc * (ι cc⁻¹ * ι dd⁻¹ * x i)) = x i := by
      linear_combination (ι dd * ι dd⁻¹ * x i) * hC + x i * hD
    rw [h4] at h3
    exact Set.mem_iInter.mp h3 i
  · intro x₀ hx₀
    rw [mem_ann] at hx₀
    push_neg at hx₀
    obtain ⟨y, hy, hne⟩ := hx₀
    exact ⟨y, fun u hu => hu y hy, hne⟩

end GlobalTheory.FinSepChar

theorem GlobalTheory.FinSepChar.finite_chars_separate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∀ N ∈ nhds (0 : κ → Af F), ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 :=
  fun _ _ _ _ hψ κ _ _ hN => GlobalTheory.FinSepChar.exists_compact_open_separating hψ κ hN
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  first | exact @GlobalTheory.StdCharEq.eq_adelicChar | exact GlobalTheory.StdCharEq.eq_adelicChar | (intros; apply GlobalTheory.StdCharEq.eq_adelicChar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section


theorem _root_.GlobalTheory.T.psi_unramified_away_different : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  first | exact @GlobalTheory.StdCharUnrF.psiUnr_of_not_le | exact GlobalTheory.StdCharUnrF.psiUnr_of_not_le | (intros; apply GlobalTheory.StdCharUnrF.psiUnr_of_not_le <;> assumption)
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct


theorem _root_.GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  first | exact @GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | exact GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | (intros; apply GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct


theorem _root_.GlobalTheory.T.isotropicIdempotent_gives_dual_stable_subspaces : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  first | exact @GlobalTheory.IdemIsotropic.idem_isotropic_pair | exact GlobalTheory.IdemIsotropic.idem_isotropic_pair | (intros; apply GlobalTheory.IdemIsotropic.idem_isotropic_pair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  first | exact @GlobalTheory.UAut.isRealLine_oneP | exact GlobalTheory.UAut.isRealLine_oneP | (intros; apply GlobalTheory.UAut.isRealLine_oneP <;> assumption)
end
