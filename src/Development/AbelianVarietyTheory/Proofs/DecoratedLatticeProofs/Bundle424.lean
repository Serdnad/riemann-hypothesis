module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle026
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Divisibility.BrJoint
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle406
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrueBranch

section Gen

open Formalism.L2.DIV _root_.Formalism.L2.Col

variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem cSpan_eq_VV {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

theorem det_ne_zero_of_mem_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hk)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem polOf_fnOf_frOne (G : ι → Matrix (Fin N) (Fin N) ℂ) (sh : ι → ℤ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (P : MvPolynomial (ι × Fin N × Fin N) ℂ) : Formalism.L2.Col.polOf G sh o (fnOf G sh 1 P) = P := by
  have e : (fun τ => (o.1 τ)⁻¹) = (1 : ι → Matrix (Fin N) (Fin N) ℂ) := funext fun τ => by rw [ho τ, inv_one]; rfl
  have h := Formalism.L2.Col.polOf_fnOf G sh o P
  rwa [e] at h

theorem fnOf_actP_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (P : Pol ℂ ι n) (y y' : Frames G) (h : IsTr (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) y y') :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e1 := congrFun (Formalism.L2.Col.fnOf_mul G (shiftOf lam) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) 1 P) y
  have e2 := Formalism.L2.Col.fnOf_tr (G := G) (G' := G) (shiftOf lam) 1 (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P y' y h
  have e3 : (fun τ => (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ := by
    funext τ; simp
  rw [e2, e3, e1]
  have e4 : actP lam g P = (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ.det ^ shiftOf lam τ) •
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P := by
    simp only [actP, detTwK, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose]
    simp [detPow, shiftOf, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [e4]

theorem brEqv_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (o : Frames G)
    (ho : ∀ τ, o.1 τ = 1) :
    BrEqv hN G G' lam sg (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    refine ⟨c • (Br.brStdP hN lam sg P : Pol ℂ ι n), ?_, ?_⟩
    · rw [cSpan_eq_VV]; exact (Formalism.L2.DIV.VV ℂ sg).smul_mem c (Br.brStdP hN lam sg P).2
    · simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
  · rintro k kt hk hb _ ⟨P, hP, rfl⟩ Φ' hΦ' z z' hz
    have hk0 : ∀ τ, (k τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_mem_unitary (hk τ)
    have hkt0 : ∀ τ, (kt τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose, (hb τ).det, mul_one, ← Matrix.det_transpose]; exact hk0 τ
    let g : ι → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hk0 τ)
    let g' : ι → GL (Fin N) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hkt0 τ)
    have hblk : ∀ τ, GlobalTheory.BranchFormula.IsBlock hN ((g' τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) 1 := fun τ => (hb τ).transpose
    have hPV : P ∈ Formalism.L2.DIV.VV ℂ lam := cSpan_eq_VV lam ▸ hP
    have hE := GlobalTheory.BranchFormula.brEquiv_all ℂ hN lam sg hS g g' (fun τ => hblk τ) ⟨P, hPV⟩
    have h2 : (Br.brStdP hN lam sg (actP lam g' P) : Pol ℂ ι n) = actP sg g (Br.brStdP hN lam sg P : Pol ℂ ι n) :=
      congrArg Subtype.val hE
    have hΦe : Φ' = fnOf G (shiftOf lam) 1 (actP lam g' P) := by
      funext y
      have hd : ∀ τ, IsUnit (kt τ * y.1 τ).det := fun τ => by
        rw [Matrix.det_mul]
        refine IsUnit.mul (Ne.isUnit ?_) (y.2 τ)
        rw [← Matrix.det_transpose]; exact hkt0 τ
      let y' : Frames G := ⟨fun τ => kt τ * y.1 τ, hd⟩
      rw [hΦ' y y' (fun τ => rfl), fnOf_actP_tr G lam g' P y y' (fun τ => by
        show kt τ * y.1 τ = ((kt τ)ᵀ)ᵀ * y.1 τ
        rw [Matrix.transpose_transpose])]
    rw [hΦe]
    simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
    rw [h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, fnOf_actP_tr G' sg g _ z z' (fun τ => by
      rw [hz τ]
      show k τ * z.1 τ = ((k τ)ᵀ)ᵀ * z.1 τ
      rw [Matrix.transpose_transpose])]

theorem ne_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (hc : c ≠ 0) (o : Frames G) (ho : ∀ τ, o.1 τ = 1) :
    ∃ Φ ∈ ValC G lam, (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) Φ ≠ 0 := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  have h1 := GlobalTheory.BranchFormula.onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs
  choose f hf hf0 using fun τ => (h1 N n hN (lam τ) (sg τ) (hI τ) (hS τ)).2.2.1
  have hn : ∀ τ, f τ ∈ nablaSq ℂ N (lam τ) := fun τ => by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
  have hmem : Formalism.L2.DIV.ten f ∈ Formalism.L2.DIV.VV ℂ lam := GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn
  have ht := GlobalTheory.BranchFormula.tensor ℂ ι N n hN lam sg hI hS f ⟨_, hmem⟩ hn rfl
  refine ⟨fnOf G (shiftOf lam) 1 (Formalism.L2.DIV.ten f), ⟨_, (cSpan_eq_VV lam).symm ▸ hmem, rfl⟩, fun h => ?_⟩
  simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply] at h
  have h' : (Br.brStdP hN lam sg (Formalism.L2.DIV.ten f) : Pol ℂ ι n) =
      Formalism.L2.DIV.ten fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (lam τ) (sg τ) (f τ) := ht
  rw [h', map_smul] at h
  have h0 := Formalism.L2.Col.fnOf_injective G' (shiftOf sg) 1 (fun _ => by simp) ⟨fun _ => 1, fun _ => by simp⟩
    (((smul_eq_zero.1 h).resolve_left hc).trans (map_zero _).symm)
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ hf0 h0

end Gen

section True

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {M : ℕ} {a b : DomWeight M} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_record (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem sgT_record (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  apply domWeight_ext
  funext i
  show (B.wts.sgW τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (B.wts.sgW τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

end True

section Main

theorem branching_true_columns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  intro B X I _ _ l Z u hN
  have hM := fun τ => GlobalTheory.BranchMembers.members B.fields B.Word B.R B.wts B.wts_isOk u τ
  have hI' : ∀ τ, Formalism.L2.Col.Br.Interlace hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).1
  have hS' : ∀ τ, Formalism.L2.Col.Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).2
  have hc : (∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
      (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero _).2 (l.per u I.mu0).tz_ne)
  have hlow : lowOf I l Z u = fnOf _ (shiftOf (I.perIn u I.mu0).sgT) 1 ∘ₗ
      ((∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
        (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) •
        ((Formalism.L2.DIV.VV ℂ (I.perIn u I.mu0).sgT).subtype ∘ₗ
          Formalism.L2.Col.Br.brStdP hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u I.mu0).sgT)) ∘ₗ
      Formalism.L2.Col.polOf _ (shiftOf (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩ := by
    unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]
    rfl
  refine ⟨?_, ?_, ?_, fun a z c y => ?_⟩
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]; exact hI'
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0, hlow]
    exact brEqv_formula hN _ _ _ _ hS' _ _ (fun _ => rfl)
  · rw [lamT_record I l Z u, hlow]
    exact ne_formula hN _ _ _ _ hI' hS' _ hc _ (fun _ => rfl)
  · unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u a]
    rfl

end Main

end GlobalTheory.TrueBranch
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.GVecAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem comb_zero (c : WO S T →₀ ℂ) : comb ψ S T c 0 = 0 := by
  have := comb_smul (ψ := ψ) c 0 0
  rwa [zero_smul, zero_smul] at this

theorem comb_pureTensorO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {d o e : WO S T →₀ ℂ} {g : WO S T → ℂ} {s : ℂ} (hd : IsFinComb d) (ho : IsFinComb o) (he : IsFinComb e)
    (hg : IsThetaFunO ψ S T g) {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T)
    (h : om (b, b') (comb ψ S T d g) = s • comb ψ S T e (comb ψ S T o (om (b, b') g))) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a * b, a' * b') (comb ψ S T d (pureTensorO ψ θ S T sS sT BS BT g P)) =
      s • comb ψ S T e (comb ψ S T o (om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT g P))) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hfin : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧
      om (b, b') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (b, b') f) P := fun f hf =>
    GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hbg := hW.om_pres (b, b') g hg
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
  have t1 : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P) := (hfin _ hbg).1
  have t2 : IsThetaFunO ψ S T (comb ψ S T o (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P)) := theta_comb hψ ho t1
  rw [e1, map_mul, Module.End.mul_apply, Module.End.mul_apply, comb_pureTensorO hψ hθ sS sT BS BT hd hg,
    (hfin _ (theta_comb hψ hd hg)).2, h, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, (hfin g hg).2,
    ← comb_pureTensorO hψ hθ sS sT BS BT he (theta_comb hψ ho hbg), ← comb_pureTensorO hψ hθ sS sT BS BT ho hbg,
    GlobalTheory.FrComb.om_comb hW ha ha' he t2, GlobalTheory.FrComb.om_comb hW ha ha' ho t1]

theorem pureTensorO_zero (sS sT BS BT) (P) : pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) P = 0 := by
  have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
  rwa [zero_smul, zero_smul] at this

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end Gen

end GlobalTheory.GVecAt

namespace GlobalTheory.GVecAt

theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := GlobalTheory.T.latticeVacuumCombinations_differ_by_scalar

section Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

end Fam

end GlobalTheory.GVecAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)

theorem _root_.GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  first | exact @GlobalTheory.FinPl.ExtZero.ext_zero | exact GlobalTheory.FinPl.ExtZero.ext_zero | (intros; apply GlobalTheory.FinPl.ExtZero.ext_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) d ∧ f = comb ψ S T d f₀ := by
  first | exact @GlobalTheory.StepComb.exists_comb_of_isStepVecOf | exact GlobalTheory.StepComb.exists_comb_of_isStepVecOf | (intros; apply GlobalTheory.StepComb.exists_comb_of_isStepVecOf <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineLatModel

variable {D : D7} {S T : HSp D}

theorem sbHalf_of_nsmul {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {M₁ M₂ : ℕ} (p₁ : 0 < M₁) (p₂ : 0 < M₂)
    (h1 : ∀ u ∈ Λ', M₁ • u ∈ Λ) (h2 : ∀ u ∈ Λ, M₂ • u ∈ Λ') {Φ : WO S T → ℂ} (h : IsSBHalf e Λ Φ) :
    IsSBHalf e Λ' Φ := by
  obtain ⟨a1, k, hk, a2, a3⟩ := h
  refine ⟨a1, M₁ * M₂ * k, Nat.mul_pos (Nat.mul_pos p₁ p₂) hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have e : (M₁ * M₂ * k) • u = k • (M₂ • (M₁ • u)) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e]
    exact a2 _ (nsmul_mem (h1 u hu) M₂) (GlobalTheory.SplitLinAt.isHalf_nsmul (GlobalTheory.SplitLinAt.isHalf_nsmul hh M₁) M₂) t
  · have e : (M₁ * M₂ * k) • t = M₁ • (M₂ • (k • t)) := by
      rw [smul_smul, smul_smul]
    rw [e]
    exact nsmul_mem (h2 _ (a3 t ht)) M₁

theorem isModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (L S : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∀ (n : Type) [Fintype n] [DecidableEq n] (FL : GlobalTheory.LocMod.Frame k L.rank Unit) (FS : GlobalTheory.LocMod.Frame k S.rank n), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FL FS (T₁ ∘ₗ GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS) := by
  classical
  intro D k _ _ _ _ p ψ hψ _ L S ζ hζ LS hS g₁ T₁ hg₁ hT n _ _ FL FS
  have he : IsSplitIdem D p.e := p.split
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    exact hζ.2 (by simp)
  letI : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) :=
    Submodule.IsLattice.of_fg _ (Submodule.fg_span_singleton ζ)
  letI : Submodule.IsFullLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) :=
    ⟨by
      rw [Submodule.span_span_of_tower]
      exact (finrank_eq_one_iff_of_ne_zero ζ hζ0).1 (by rw [Module.finrank_fin_fun, hζ.1])⟩
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hS
  have hA : ∀ u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _)
      (fun _ => True), IsHalf p.e u →
      u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v) :=
    fun u hu hh => GlobalTheory.SplitLinAt.latHalf D k p L S _ LS u hu (Or.inl hh)
  have hle := GlobalTheory.SplitLinAt.latO_le (S := L) (T := S)
    ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)
  have hT' := (GlobalTheory.SplitLinAt.placeModel_congr hA hle).1 hT
  have dL := GlobalTheory.PlaceModel.isSelfDualC_latFrame L
  have hsb : ∀ Φ, IsSBHalf p.e
      (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v))
      (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS Φ) := fun Φ => by
    have h0 := GlobalTheory.LocMod.Witness.ext_sb (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS dL hS Φ
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ dL
    have hfg : (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L).FG :=
      Submodule.fg_span_singleton ζ
    obtain ⟨M₁, p₁, h₁⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := GlobalTheory.PlaceModel.latFrame L)
      (ΛT' := LS) hfg hS.1.fg inferInstance inferInstance
    obtain ⟨M₂, p₂, h₂⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO
      (ΛS' := Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ}) (ΛT' := LS)
      dL.1.fg hS.1.fg inferInstance inferInstance
    exact (GlobalTheory.SplitLinAt.sbHalf_congr hA hle).2 (sbHalf_of_nsmul p₁ p₂ h₁ h₂ h0)
  refine ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance he.1 he.2.1 (GlobalTheory.PlaceCoord.infPart_split he) hg₁ T₁ hT' _
      ((GlobalTheory.SplitLinAt.sbHalf_congr hA hle).1 (hsb Φ))
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.trans _ (hsb Φ) _ (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x))
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
      GlobalTheory.LocMod.Witness.down_up, h]
    exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x)).symm rfl rfl
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.modul _ (hsb Φ) _ hy)
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, h]
    split_ifs with ht
    · rw [GlobalTheory.LocMod.Witness.up_down (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS ht]
    · rw [mul_zero]

end GlobalTheory.LineLatModel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.lineContraction_splitPlace_localModel : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  first | exact @GlobalTheory.ContrLocProof.contrLoc | exact GlobalTheory.ContrLocProof.contrLoc | (intros; apply GlobalTheory.ContrLocProof.contrLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineModel_kappa_transform_isLocalModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → ∀ TLS, p.IsModel ψ FL FS TLS → ∃ FL'' : Frame k L''.rank Unit, (∀ r, FL''.β r () = z₀ r) ∧ ∃ TL, p.IsModel ψ FS FL'' TL ∧ ∀ (c : SB (Matrix n Unit k)) (Φ : SB (Matrix Unit n k)), (∀ η, Φ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) → ∀ w, TL Φ w = TLS c (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)) := by
  first | exact @GlobalTheory.KappaModel.kappa_model | exact GlobalTheory.KappaModel.kappa_model | (intros; apply GlobalTheory.KappaModel.kappa_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_line_similitude_maps_selfDual_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  first | exact @GlobalTheory.SplitLineSim.line_sim_maps | exact GlobalTheory.SplitLineSim.line_sim_maps | (intros; apply GlobalTheory.SplitLineSim.line_sim_maps <;> assumption)
end
