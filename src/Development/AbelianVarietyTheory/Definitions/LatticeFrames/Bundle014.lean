module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
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
import Mathlib.RingTheory.PicardGroup
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

end GlobalTheory.Core.Rk.IP.FockModel

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DblInh

variable {D : D7}

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def conjHom {R : Type} [CommRing R] (x : Matrix n m R) (y : Matrix m n R) (hx : x * y = 1) (hy : y * x = 1) :
    Matrix m m R →* Matrix n n R where
  toFun g := x * g * y
  map_one' := by rw [Matrix.mul_one, hx]
  map_mul' g h := by
    rw [Matrix.mul_assoc (x * g), ← Matrix.mul_assoc y, ← Matrix.mul_assoc y, hy, Matrix.one_mul]
    simp only [Matrix.mul_assoc]

def rebase {S : HSp D} (β : Frame p S n) (b : Matrix (Fin S.rank) m k) (b' : Matrix m (Fin S.rank) k) (h : b * b' = 1)
    (h' : b' * b = 1) : Frame p S m where
  b := b
  b' := b'
  bb' := h
  b'b := h'
  gl := β.gl.comp (Units.map (conjHom (β.b' * b) (b' * β.b)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc b, h, Matrix.one_mul, β.b'b])
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, h'])))
  gl_supp g := β.gl_supp _
  gl_mat g := by
    refine (β.gl_mat _).trans ?_
    change β.b * (β.b' * b * g.val * (b' * β.b)) * β.b' = _
    simp only [← Matrix.mul_assoc, β.bb', Matrix.one_mul]
    rw [Matrix.mul_assoc _ β.b, β.bb', Matrix.mul_one]

theorem exists_sumFrame {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    (β : Frame p A (Fin A.rank)) (γ : Frame p S n) : ∃ β₀ : Frame p S (Fin A.rank ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let w : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hw : w ⬝ᵥ ζ = 1 := by
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let M : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (vecB o ζ))
  let N : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (w ᵥ* o.qB))
  have hNM : N * M = 1 := by
    rw [fromRows_mul_fromCols, o.qA_iA, ← replicateCol_mulVec, vecB, mulVec_mulVec, o.qA_iB, zero_mulVec,
      ← replicateRow_vecMul, vecMul_vecMul, o.qB_iA, vecMul_zero, replicateRow_mul_replicateCol, dotProduct_mulVec,
      vecMul_vecMul, o.qB_iB, vecMul_one, hw, replicateCol_zero, replicateRow_zero, ← fromBlocks_one]
    congr 1
    ext i j
    rw [Subsingleton.elim i j, one_apply_eq, of_apply]
  let X : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have h1 : (X' * N.map f) * (M.map f * X) = (1 : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (N.map f), ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, fromBlocks_multiply]
    simp [β.b'b]
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← o.rank_add, hζ.1])).1 h1
  refine ⟨rebase γ _ _ h2 h1, ?_⟩
  change M.map f * X = _
  rw [fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  rfl

end Frames

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

end GlobalTheory.FinPl.DblInh

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def SplitPt.IsIdele {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (x : kˣ) (a : (AE D)ˣ) : Prop := (a : AE D) = p.sec x + (1 - p.e)

def chrPow (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : ℂ := ((χ a ^ e : Circle) : ℂ)

def LiftExact (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1), ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D),
    CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n),
    ∀ a, p.IsIdele q.unit a → ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f →
    ∀ φ₀, RamAt α P φ₀ → ∀ ε : 𝓀[k]ˣ,
      sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) =
        ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) * chrPow χS a e * chrPow χT a (-e)) •
          liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f

def RamUnitary (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (S : HSp D),
    CoCpt S → ∀ (vS : Vol S) (β : Frame p S n) (P : Pair k n) (φ φ' : GA D S → ℂ), RamAt β P φ → RamAt β P φ' →
      ∫ g in vS.𝓕, sOp β P q (resChar χ hχ q) ε φ g * star (sOp β P q (resChar χ hχ q) ε φ' g) ∂vS.μ =
        (resCard k : ℂ) ^ Fintype.card n * ∫ g in vS.𝓕, φ g * star (φ' g) ∂vS.μ

end GlobalTheory.FinPl

end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def scT {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) : PB.Terms τ Rw I H H₁ :=
  { X with scal := fun _ _ => True }

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def cls1 (t : TauC Y u u) : Set (TauC Y u u) :=
  {t' | t' ∈ (Y.tO u u).genSet ∧ (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t ∧ (Y.tO u u).s0 t t' = 1}

def NOf1 (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.NGData (TauC Y u u) D.host.E D.R.rS (Set (TauC Y u u)) (NuC D) :=
  { NOfG Y u νL νB ng with
    cls := cls1 Y u
    a2 := GlobalTheory.SnFam.a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL }

def GeneratorBoundAt (Γ : ℝ) : Prop := (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).genSet) ≤ Γ * ddC X Y u u

end Conc

def CorankOneIsEquivalenceOnRow : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').s0 t t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t = 1) ∧
    (∀ t ∈ (Y.tO u u').nzSet, ∀ t' ∈ (Y.tO u u').nzSet, ∀ t'' ∈ (Y.tO u u').nzSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' →
      (Y.tO u u').s0 t t' = 1 → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').s0 t t'' = 1)

def StepClass1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
      PN.ClassInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)

def StepNormals1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def FamGen1 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    GlobalTheory.SnFam.FamQ Y u u Not (Y.tO u u).genSet (cls1 Y u)

def StepFam1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

def StepLoc1 : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLeG (genT (scT (Y.tO u u))) (NOf1 Y u (sc s ν) ν (fun _ => 0)) C1 C0n
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)

def RowGen1P : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u → ConcTie X Y → (Y.tO u u).AbsConv →
      GeneratorBoundAt Y u (gamB D large₂ CB)

end GlobalTheory.Core.One
end
end
