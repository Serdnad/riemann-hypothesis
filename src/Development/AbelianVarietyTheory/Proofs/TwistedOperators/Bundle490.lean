module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle456
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx


theorem _root_.GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  first | exact @GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | exact GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | (intros; apply GlobalTheory.HalfSplit.relIndex_nsmul_half_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hn : 0 < n) (hL : X.L.IsFullLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [Submodule.IsFullLattice.span_eq_top (self := hL)] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), 0 < n → X.L.IsFullLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_col (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t := by
  change (columnBlock L j).sp.rank = _
  rcases hj.eq_or_lt with rfl | hk
  · rw [colY_m]; exact D.sp.X'_rank
  · rw [colY_lt L hk]; exact Comparison₂.rank_Yc hk.le


open Classical in
def topPl (L : LevCh D T) (t : T) : Finset (Pl D.host.E) := L.Pg ∪ L.Q t


open Classical in
def topFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ topPl L t, stepFn L t w j
      (((Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb)
        (Comparison₂.ixOf G t w ha))
  else 0

end GlobalTheory.FlipTop

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum

end GlobalTheory.FiniteGKSum
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
theorem _root_.GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) :=
  GlobalTheory.Twist.multEq_rowTest_of_copy
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx


theorem _root_.GlobalTheory.T.conjugate_idempotent_chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  first | exact @GlobalTheory.ChartPlaces.chart_places_injective | exact GlobalTheory.ChartPlaces.chart_places_injective | (intros; apply GlobalTheory.ChartPlaces.chart_places_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localZetaSums_absolutely_convergent_uniform : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  first | exact @GlobalTheory.FinZeta.AbsConv.absConv_localZeta | exact GlobalTheory.FinZeta.AbsConv.absConv_localZeta | (intros; apply GlobalTheory.FinZeta.AbsConv.absConv_localZeta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.thetaTransform_darbouxModel_linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  first | exact @GlobalTheory.ThetaTransformInj.linear_injective | exact GlobalTheory.ThetaTransformInj.linear_injective | (intros; apply GlobalTheory.ThetaTransformInj.linear_injective <;> assumption)
end
