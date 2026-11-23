module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.FockCauchySchwarz

variable {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m)

theorem pairK_one (x y : VV ℂ w) :
    pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y = pairBK w (GlobalTheory.BranchNorm.cV w x) y := by
  have h := GlobalTheory.BranchNorm.pairK_eq w (1 : ι → GL (Fin m) ℂ) x y
  rw [map_one] at h
  exact h

theorem pairK_cs (x y : VV ℂ w) :
    ‖pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y‖ ^ 2 ≤
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
        (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  have hG : ∀ _ : ι, (1 : Matrix (Fin m) (Fin m) ℂ).PosDef := fun _ => Matrix.PosDef.one
  rw [← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (GlobalTheory.CoefModel.toHilb w hG x) (GlobalTheory.CoefModel.toHilb w hG y)
  rw [norm_inner_symm (GlobalTheory.CoefModel.toHilb w hG y), ← sq] at h
  exact h

theorem pairBK_sq_le : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  intro ι _ m w x y
  have h := pairK_cs w (GlobalTheory.BranchNorm.cV w x) y
  rw [pairK_one, pairK_one w (GlobalTheory.BranchNorm.cV w x), GlobalTheory.BranchNorm.cV_cV] at h
  rw [pairK_one w x x, pairBK_apply w (GlobalTheory.BranchNorm.cV w x), pairingBSymm_holds, ← pairBK_apply]
  exact h

end GlobalTheory.FockCauchySchwarz
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Topology

namespace GlobalTheory.FinCharInt

theorem tensInt_le {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
    (S₁ : Subring E) (S₂ : Subring R) (K : AddSubgroup (E ⊗[F] R))
    (hK : ∀ b ∈ S₁, ∀ α ∈ S₂, b ⊗ₜ[F] α ∈ K) {x : E ⊗[F] R} (hx : x ∈ Formalism.UG.tensInt R S₁ S₂) : x ∈ K := by
  let C : AddSubgroup (E ⊗[F] R) := AddSubgroup.closure {z | ∃ b ∈ S₁, ∃ α ∈ S₂, z = b ⊗ₜ[F] α}
  have hC : C ≤ K := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, α, hα, rfl⟩
    exact hK b hb α hα
  have hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy =>
      obtain ⟨b, hb, α, hα, rfl⟩ := hx
      obtain ⟨c, hc, β, hβ, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, S₁.mul_mem hb hc, _, S₂.mul_mem hα hβ, rfl⟩
    | zero_left x _ => rw [zero_mul]; exact C.zero_mem
    | zero_right x _ => rw [mul_zero]; exact C.zero_mem
    | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact C.add_mem h1 h2
    | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact C.add_mem h1 h2
    | neg_left x y _ _ h => rw [neg_mul]; exact C.neg_mem h
    | neg_right x y _ _ h => rw [mul_neg]; exact C.neg_mem h
  refine hC ?_
  unfold Formalism.UG.tensInt at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, c.2, _, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, c.2, rfl⟩
  | zero => exact C.zero_mem
  | one => exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, S₂.one_mem, Algebra.TensorProduct.one_def⟩
  | add x y _ _ ihx ihy => exact C.add_mem ihx ihy
  | neg x _ ihx => exact C.neg_mem ihx
  | mul x y _ _ ihx ihy => exact hmul _ ihx _ ihy

theorem exists_nsmul_kill {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Finite ι] (c : ι → AF F) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ α ∈ Formalism.UG.intAd F, ψ (N • (pairA F 0 α * c i)) = 1 := by
  have hU : (⋂ i, {α : Af F | ψ (pairA F 0 (α * (c i).2)) = 1}) ∈ 𝓝 (0 : Af F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : Continuous fun α : Af F => α * (c i).2 := continuous_id.mul continuous_const
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA F 0 a) = 1})
      (by rw [zero_mul]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  refine ⟨N, hN, fun i α hα => ?_⟩
  have h1 : ψ (pairA F 0 ((N • α) * (c i).2)) = 1 := Set.mem_iInter.1 (h α hα) i
  have e : N • (pairA F 0 α * c i) = pairA F 0 ((N • α) * (c i).2) :=
    Prod.ext (show N • ((0 : Ainf F) * (c i).1) = 0 by rw [zero_mul, smul_zero])
      (show N • (α * (c i).2) = (N • α) * (c i).2 from (smul_mul_assoc N α _).symm)
  rw [e, h1]

def kerSub {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) : AddSubgroup A where
  carrier := {a | ψ a = 1}
  zero_mem' := ψ.map_zero_eq_one
  add_mem' {a b} ha hb := by
    have ha' : ψ a = 1 := ha
    have hb' : ψ b = 1 := hb
    show ψ (a + b) = 1
    rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
  neg_mem' {a} ha := by
    have ha' : ψ a = 1 := ha
    show ψ (-a) = 1
    have := AddChar.map_add_eq_mul ψ a (-a)
    rw [add_neg_cancel, ψ.map_zero_eq_one, ha', one_mul] at this
    exact this.symm

variable {D : D7}

noncomputable def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_finPart {a : AE D} (h : infPart D a = 0) : finIncl D (finPart D a) = a := by
  have key : ∀ a : AE D, (1 - GlobalTheory.FinTranslate.eInf D) • a = finIncl D (finPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add (f := _), map_add (f := _)]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : (1 - GlobalTheory.FinTranslate.eInf D) • a =
          LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F a) :=
        Prod.ext (show (1 - 1) * a.1 = 0 by rw [sub_self, zero_mul]) (show (1 - 0) * a.2 = a.2 by rw [sub_zero, one_mul])
      rw [this]
      rfl
  rw [← key, sub_smul, one_smul, GlobalTheory.FinTranslate.smul_eq_zero_of_inf h, sub_zero]

theorem exists_nsmul_kill_forms {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {ι : Type} [Finite ι] (lam : ι → (AE D →ₗ[AF D.host.F] AF D.host.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ a : AE D, infPart D a = 0 → GlobalTheory.BotClassDict.finQ D a ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D →
      ψ (N • lam i a) = 1 := by
  let w := RingOfIntegers.basis D.host.E
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill hc hn
    (fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      lam p.1 ((1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E (w p.2))))
  refine ⟨N, hN, fun i a ha hint => ?_⟩
  let g : D.host.E ⊗[D.host.F] Af D.host.F →+ AF D.host.F :=
    N • ((lam i).toAddMonoidHom.comp ((finIncl D).toAddMonoidHom.comp
      (TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toLinearMap.toAddMonoidHom))
  have hg : ∀ y, g (Lev.swapAE D y) = N • lam i (finIncl D y) := by
    intro y
    have : TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y) = y :=
      (TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply y
    show N • lam i (finIncl D (TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y))) = _
    rw [this]
  have h1 : Lev.swapAE D (finPart D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (GlobalTheory.BotClassDict.toAfE_int_iff _).2 hint
    rwa [GlobalTheory.BotClassDict.toAfE_finQ] at this
  have h2 : Lev.swapAE D (finPart D a) ∈ (kerSub ψ).comap g := by
    refine tensInt_le _ _ _ ?_ h1
    rintro _ ⟨b, rfl⟩ α hα
    let φ : 𝓞 D.host.E →+ D.host.E ⊗[D.host.F] Af D.host.F :=
      ((TensorProduct.mk D.host.F D.host.E (Af D.host.F)).flip α).toAddMonoidHom.comp
        (algebraMap (𝓞 D.host.E) D.host.E).toAddMonoidHom
    have hb : b ∈ (((kerSub ψ).comap g).comap φ).toIntSubmodule := by
      have hsp : b ∈ Submodule.span ℤ (Set.range w) := by rw [w.span_eq]; trivial
      refine Submodule.span_le.2 ?_ hsp
      rintro _ ⟨k, rfl⟩
      have h3 := h (i, k) α hα
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h3
      exact h3
    exact hb
  have h3 : ψ (g (Lev.swapAE D (finPart D a))) = 1 := h2
  rwa [hg, finIncl_finPart ha] at h3

noncomputable def symplR (S T : HSp D) (x : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun := symplOH S T x
  map_add' := GlobalTheory.FinTranslate.symplOH_add_right S T x
  map_smul' c y := GlobalTheory.FinTranslate.symplOH_smul_right S T c x y

theorem char_sympl_nsmul_int : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
    ∀ (S T : HSp D) (A0 : WO S T), ∃ N : ℕ, 0 < N ∧ ∀ v : WO S T, (∀ i j, infPart D (v i j) = 0) →
      (∀ i j, GlobalTheory.BotClassDict.finQ D (v i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) → ψ (symplOH S T A0 (N • v)) = 1 := by
  intro D ψ hc hn S T A0
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill_forms hc hn
    (fun p : Fin T.rank × Fin S.rank => (symplR S T A0).comp (Matrix.singleLinearMap (AF D.host.F) p.1 p.2))
  refine ⟨N, hN, fun v hv hint => ?_⟩
  show symplR S T A0 (N • v) ∈ kerSub ψ

  rw [map_nsmul, Matrix.matrix_eq_sum_single v, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_

  rw [map_sum, Finset.smul_sum]
  exact sum_mem fun j _ => h (i, j) (v i j) (hv i j) (hint i j)

end GlobalTheory.FinCharInt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.BotClassMeas

open GlobalTheory.BotClassDict GlobalTheory.DefiniteClassAvg GlobalTheory.BotFormula

theorem isFrame_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Formalism.L2.Col.stdLat E n) := by
  letI : StarRing E := starRingOfComm
  intro z
  rw [inv_one, Units.val_one, Matrix.one_mulVec]
  exact Formalism.L2.Col.mem_latS_std z

variable {D : D7}

theorem isFinPt_finPart (A : HSp D) (hG : A.gram = 1) (k : Formalism.L2.Theta.GA D A) :
    IsFinPt A (finPart A k) (finStd A hG k) := by
  have h1 : finHom A (realPart A k) = 1 := realPart_mem A k
  have h2 : finHom A (finPart A k) = finHom A k := by
    conv_rhs => rw [← realPart_mul_finPart A k]
    rw [map_mul, h1, one_mul]
  refine ⟨finPart_mem A k, rfl, fun i j => ?_⟩
  rw [h2, ← finAdEquiv_toAfE, ← toAfE_finStd A hG]
  rfl

theorem integral_eq_vol_mul_classSum : ∀ {D : D7} (A : HSp D), A.gram = 1 → ∀ (m : Measure (Formalism.L2.Theta.GA D A)) (fd : Set (Formalism.L2.Theta.GA D A)),
    m.IsHaarMeasure → IsFundamentalDomain (GQ A) fd m →
    ∃ v : ℂ, v ≠ 0 ∧ ∀ (n : ℕ), n = A.rank → ∀ (pt : Formalism.MainNotions.StandardLatticesGL3.GA D n → Formalism.L2.Theta.GA D A),
      (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ Φ : Formalism.L2.Theta.GA D A → ℂ,
      (∀ γ ∈ GQ A, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ GinfC A, ∀ h, Φ (h * k) = Φ h) →
      (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D n) (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ h, Φ (h * k) = Φ h) →
      ∫ g in fd, Φ g ∂m = v * ∑ᶠ x : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n),
        ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out : ℂ))⁻¹ * Φ (pt x.out) := by
  intro D A hA m fd hm hfd
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hA, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (Formalism.L2.Theta.GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  let J : Subgroup (Formalism.L2.Theta.GA D A) :=
    (Formalism.L2.DIV.St (1 : GL (Fin A.rank) (Lev.EAf D))).comap (Lev.finE A)
  have hJ : ∀ g, g ∈ J ↔ finStd A hA g ∈ GlobalTheory.NormSum.intG D A.rank := mem_level_iff A hA (isFrame_one _)
  have hJo : IsOpen (J : Set (Formalism.L2.Theta.GA D A)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A 1 ∅] with κ hh
    exact hh.2.1
  have hJc : IsCompact (J : Set (Formalism.L2.Theta.GA D A)) := by
    obtain ⟨C, hCc, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A 1
    refine (hCc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hJo) ?_
    intro k hk
    refine ⟨finPart A k, hCm _ (finPart_mem A k) ?_, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
    rw [finE_finPart]
    exact hk
  have hJtop : m J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : m J ≠ 0 := (hJo.measure_pos m ⟨1, J.one_mem⟩).ne'
  refine ⟨((m J).toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hJ0 hJtop).ne', ?_⟩
  intro n hn pt hpt Φ hl hinf hlev
  subst hn
  haveI : Finite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank)) := (GlobalTheory.NormSum.cls_finite_card_le D A.rank).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank))
  let z : GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank) → Formalism.L2.Theta.GA D A := fun x => pt x.out
  obtain ⟨hu, hcard⟩ := transport (finStd A hA) (GQ A) J (GlobalTheory.NormSum.ratG D A.rank) (GlobalTheory.NormSum.intG D A.rank)
    hJ (fun γ hγ => finStd_mem_ratG A hA hγ) (fun δ hδ => exists_rat_lift A hA hδ)
    (fun γ hγ γ' hγ' h => finStd_injOn A hA hγ hγ' h) z (fun x => finStd_of_isFinPt A hA (hpt _))
  have hfin : ∀ l, {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l => by
    have him : {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
        Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : Formalism.L2.Theta.GA D A) * z l ∈ J} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact (GlobalTheory.InnerClassSum.finite_stab_of_measure m (GQ A) J hfd hJ0 hJtop (z l)).image _
  have hr : ∀ k ∈ J, ∀ h, Φ (h * k) = Φ h := fun k hk h => by
    rw [← finPart_mul_realPart A k, ← mul_assoc, hinf _ (realPart_mem A k),
      hlev _ _ ((hJ k).1 hk) (isFinPt_finPart A hA k)]
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (Formalism.L2.Theta.GA D A) m (GQ A) J fd hfd hJo
    hJtop _ z hu hfin Φ hl hr
  rw [heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
  rfl

end GlobalTheory.BotClassMeas
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.MidBlock

section Alg

variable {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']

theorem qdet_map (φ : A →ₐ[ℂ] A') {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm

  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add, apply_ite φ, AlgHom.commutes, map_zero]

theorem qdet_mem (S : Subalgebra ℂ A) {n : ℕ} {E : Fin n → Fin n → A} (h : ∀ a b, E a b ∈ S) (u : ℂ) :
    Formalism.REAL.qdet E u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem comm_qdet {n : ℕ} {E : Fin n → Fin n → A} {z : A} (h : ∀ a b, Commute z (E a b)) (u : ℂ) :
    Commute z (Formalism.REAL.qdet E u) := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Formalism.REAL.Tm
  exact Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)

theorem glComm {n : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {a b c d : Fin n} (hbc : b ≠ c)
    (hda : d ≠ a) : Commute (X a b) (X c d) := by
  have h := hX a b c d
  rw [if_neg hbc, if_neg hda, sub_zero] at h
  exact sub_eq_zero.1 h

end Alg

section Stab

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ N, f x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => by simpa [Module.algebraMap_end_apply] using N.smul_mem c hx

theorem mem_stab {N : Submodule ℂ M} {f : Module.End ℂ M} : f ∈ stab N ↔ ∀ x ∈ N, f x ∈ N := Iff.rfl

theorem upperSpan_maps {N K : Submodule ℂ M} {r m : ℕ} (Y : Fin (r + m) → Fin (r + m) → stab N)
    (hY : ∀ p q, ∀ x ∈ N, (Y (Fin.castAdd m p) (Fin.natAdd r q) : Module.End ℂ M) x ∈ K)
    {y : stab N} (hy : y ∈ GlobalTheory.CapHC.upperSpan Y) : ∀ x ∈ N, (y : Module.End ℂ M) x ∈ K := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    intro x hx
    exact hY p q _ (mem_stab.1 w.2 x hx)
  | zero => intro x _; simp
  | add a b _ _ ha hb => intro x hx; simpa using K.add_mem (ha x hx) (hb x hx)
  | smul c a _ ha => intro x hx; simpa using K.smul_mem c (ha x hx)

end Stab

section Main

end Main

end GlobalTheory.LeviHC.MidBlock
end
end

section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  first | exact @GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | exact GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | (intros; apply GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm <;> assumption)
end
