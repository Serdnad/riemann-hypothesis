module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.integralPointsIndicator_fourier_self_unramified : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  first | exact @GlobalTheory.RatWeilOp.ind_fourier_self | exact GlobalTheory.RatWeilOp.ind_fourier_self | (intros; apply GlobalTheory.RatWeilOp.ind_fourier_self <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.adelicSchwartzSpace_mem_span_pureTensors : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  first | exact @GlobalTheory.SchASpan.mem_span_pure | exact GlobalTheory.SchASpan.mem_span_pure | (intros; apply GlobalTheory.SchASpan.mem_span_pure <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.rational_darboux_coordinates_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  first | exact @GlobalTheory.SympChange.darboux_change_rat | exact GlobalTheory.SympChange.darboux_change_rat | (intros; apply GlobalTheory.SympChange.darboux_change_rat <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.weil_operator_for_levi_matrix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  first | exact @GlobalTheory.LeviOp.hasOp_levi | exact GlobalTheory.LeviOp.hasOp_levi | (intros; apply GlobalTheory.LeviOp.hasOp_levi <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  first | exact @GlobalTheory.RatWeilOp.hasOp_levi | exact GlobalTheory.RatWeilOp.hasOp_levi | (intros; apply GlobalTheory.RatWeilOp.hasOp_levi <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.weil_operator_for_unipotent_matrix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.unipM S) := by
  first | exact @GlobalTheory.SympUnip.hasOp_unipM | exact GlobalTheory.SympUnip.hasOp_unipM | (intros; apply GlobalTheory.SympUnip.hasOp_unipM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section
namespace GlobalTheory.PureMatch

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowB (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i, j)) ≃ Fin (spW₁ G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨i.2.le, j.2.le⟩)

def trB (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Y : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Y (rowB t w i j r) (GlobalTheory.SquareFlipReach.colE t w e c))

def blockV {i j : Fin D.R.m} (e : Num G i j) : Finset (Fin ((spW G i j).rank + (spW₁ G i j).rank)) :=
  Finset.univ.image fun k => e (Sum.inl k)

end GlobalTheory.PureMatch
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem idem_split_mul {R S : Type} [CommRing R] [Ring S] (e : R) (ι : S →+ R)
    (he : (1 - e) * (1 - e) = 1 - e) (hι : ∀ x, (1 - e) * ι x = 0) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    {l m n : Type} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) (X : Matrix l m S) (Y : Matrix m n S) :
    ((1 - e) • A + X.map ι) * ((1 - e) • B + Y.map ι) = (1 - e) • (A * B) + (X * Y).map ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
  Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmul]
  linear_combination (A i k * B k j) * he + A i k * hι (Y k j) + B k j * hι (X i k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) :=
  (GlobalTheory.InertLocField.liftT_injective v).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective

theorem iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [iotaW_apply, iotaW_apply, iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem one_sub_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, idem_mul_iotaW, sub_self]

theorem one_sub_idem (v : Pl (F := F)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
    rw [← map_mul, ← GlobalTheory.InertLocField.liftV_mul, mul_one]
  linear_combination h

theorem complEquiv_symm_algebraMap' (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (algebraMap E _ x) = (1 : Fv F v) ⊗ₜ[F] x := by
  rw [RingEquiv.symm_apply_eq]
  change _ = toCompl (under_eq_of_isInertAt hw) ((1 : Fv F v) ⊗ₜ[F] x)
  rw [toCompl_tmul, map_one, one_mul]

theorem iotaW_algebraMap (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    iotaW hw (algebraMap E _ x) = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) x := by
  rw [iotaW_apply, complEquiv_symm_algebraMap', GlobalTheory.InertLocField.liftT_tmul]
  change _ = (GlobalTheory.LatVac.liftV v 1 ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem iotaW_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw (conjW σ hw x) = cA σ (iotaW hw x) := by
  rw [iotaW_apply, iotaW_apply, ← GlobalTheory.InertLocField.liftT_sigR]
  congr 1
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply _

theorem incM_split (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} (J : Matrix l m E) :
    incM F J = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • incM F J +
      (J.map (algebraMap E (w.adicCompletion E))).map (iotaW hw) := by
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, iotaW_algebraMap]
  ring

end GlobalTheory.InertBigCell

namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  rw [← map_one (algebraMap E (w.adicCompletion E)), iotaW_algebraMap]
  change _ * inclR (F := F) (AF F) 1 = _
  rw [(inclR (F := F) (AF F)).map_one, mul_one]

theorem diagCols_split (hw : Formalism.UG.IsInertAt F E v w) (ι : Type) [DecidableEq ι] :
    (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) =
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) +
        (diagCols ι : Matrix (ι ⊕ ι) ι (w.adicCompletion E)).map (iotaW hw) := by
  ext i j
  rcases i with i | i <;>
  · simp only [diagCols, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]
    split_ifs
    · rw [iotaW_one]; ring
    · rw [map_zero]; ring

theorem invOf_two_smul_add_iotaW (hw : Formalism.UG.IsInertAt F E v w) (t : AE F E) (x : w.adicCompletion E) :
    ⅟(2 : AF F) • (t + t + iotaW hw x) = t + iotaW hw ((2 : w.adicCompletion E)⁻¹ * x) := by
  have h2 : (2 : w.adicCompletion E) ≠ 0 := by
    rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hx : iotaW hw x = iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x) := by
    rw [← map_add (f := _), ← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
  rw [hx, show t + t + (iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x)) =
      (2 : AF F) • (t + iotaW hw (2⁻¹ * x)) by rw [two_smul]; abel, smul_smul, invOf_mul_self, one_smul]

theorem glueW_transpose (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P)ᵀ = glueW hw Pᵀ := by
  rw [glueW, glueW, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

theorem glueW_map_cA (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P).map (cA σ) = glueW hw (P.map (conjW σ hw)) := by
  ext i j
  simp only [glueW, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, AlgHom.commutes, iotaW_conjW]
  congr 2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem glueW_read_at_place (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι] :
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he_def
  refine ⟨fun J P => ?_, fun P hP => ?_, fun P => ?_⟩
  · rw [glueW_transpose, glueW_map_cA, glueW, glueW, incM_split hw J, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), Matrix.one_mul, Matrix.mul_one,
      add_right_inj]
    exact (Matrix.map_injective (iotaW_injective hw)).eq_iff
  · rw [diagCols_split hw ι, glueW, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.one_mul]
    exact congrArg (fun M => (1 - e) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) + M.map (iotaW hw)) hP
  · ext i j
    simp only [glueW, Matrix.smul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, add_zero]
    rw [← invOf_two_smul_add_iotaW hw, map_add (f := _), map_add (f := _), map_add (f := _)]
    congr 1
    abel

end GlobalTheory.InertBigCell
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem gl_iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem gl_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [gl_iotaW_apply, gl_iotaW_apply, gl_iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem gl_iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) := fun x y hxy =>
  (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective (GlobalTheory.InertLocField.liftT_injective v hxy)

theorem gl_idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, gl_iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem gl_iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) := by
  have h := GlobalTheory.InertLocField.liftV_one_smul (E := E) v 1
  rw [Algebra.smul_def, mul_one, _root_.map_one (GlobalTheory.InertLocField.evT E v)] at h
  rw [gl_iotaW_apply, _root_.map_one]
  exact h.symm

theorem gl_compl_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, gl_idem_mul_iotaW, sub_self]

theorem gl_compl_idem (hw : Formalism.UG.IsInertAt F E v w) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) := by
  have h := gl_idem_mul_iotaW hw 1
  rw [gl_iotaW_one] at h
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gl_compl_smul_map (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • P.map (iotaW hw) = 0 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, gl_compl_mul_iotaW, Matrix.zero_apply]

theorem gl_map_mul_map (hw : Formalism.UG.IsInertAt F E v w) (P Q : Matrix ι ι (w.adicCompletion E)) :
    P.map (iotaW hw) * Q.map (iotaW hw) = (P * Q).map (iotaW hw) := by
  ext i k

  rw [Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, gl_iotaW_mul]

theorem gl_map_one_eq (hw : Formalism.UG.IsInertAt F E v w) :
    (1 : Matrix ι ι (w.adicCompletion E)).map (iotaW hw) =
      algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [gl_iotaW_one, smul_eq_mul, mul_one]
  · rw [map_zero, smul_zero]

theorem gl_glueW_sub_one (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    glueW hw P - 1 = (P - 1).map (iotaW hw) := by
  rw [Matrix.map_sub _ (map_sub (iotaW hw)), gl_map_one_eq, glueW, sub_smul, one_smul]
  abel

theorem glueW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  intro F E _ _ _ _ _ v w hw ι _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    have h1 : ∀ B : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) * B =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • B := fun B => by
      rw [Matrix.smul_mul, Matrix.one_mul]
    have h2 : ∀ A : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), A * ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • A := fun A => by
      rw [Matrix.mul_smul, Matrix.mul_one]
    rw [glueW, glueW, glueW, add_mul, mul_add, mul_add, h1, h1, h2, smul_smul, gl_compl_idem hw, gl_compl_smul_map,
      gl_compl_smul_map, gl_map_mul_map, add_zero, zero_add]
  · rw [glueW, gl_map_one_eq, ← add_smul, sub_add_cancel, one_smul]
  · intro P Q hPQ
    have h : P.map (iotaW hw) = Q.map (iotaW hw) := add_left_cancel hPQ
    exact Matrix.ext fun i j => gl_iotaW_injective hw (congrFun (congrFun h i) j)
  · intro P u hu
    rw [gl_glueW_sub_one]
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, gl_iotaW_apply]
    exact GlobalTheory.InertLocField.at_liftT v _ u hu
  · intro M hM
    have hent : ∀ i j, ∃ y, GlobalTheory.InertLocField.liftT E v y = (M - 1) i j := fun i j =>
      (GlobalTheory.InertLocField.at_iff v _).1 (fun u hu => by
        have := congrFun (congrFun (hM u hu) i) j
        rwa [Matrix.smul_apply] at this)
    choose y hy using hent
    refine ⟨1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j), ?_⟩
    have hX : (Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j)).map (iotaW hw) = M - 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, gl_iotaW_apply, RingEquiv.symm_apply_apply, hy]
    have h := gl_glueW_sub_one hw (1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j))
    rw [add_sub_cancel_left, hX] at h
    exact sub_left_inj.mp h
  · intro P u
    have hd : ∀ x : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *ᵥ x =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • x := fun x => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    funext i

    rw [glueW, Matrix.add_mulVec, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    gl_compl_mul_iotaW, zero_add, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, gl_iotaW_mul]

end GlobalTheory.InertBigCell
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT


theorem _root_.GlobalTheory.T.birigidified_bundle_translation_invariant_first_factor : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A, (∃ t : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  first | exact @GlobalTheory.TranslFst.iso_transl_fst | exact GlobalTheory.TranslFst.iso_transl_fst | (intros; apply GlobalTheory.TranslFst.iso_transl_fst <;> assumption)
end
