module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat


theorem _root_.GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  first | exact @GlobalTheory.PureGlue.eq_pure_of_slices | exact GlobalTheory.PureGlue.eq_pure_of_slices | (intros; apply GlobalTheory.PureGlue.eq_pure_of_slices <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem globalIntegralMatrix_mem_stdThetaLattice (D : D7) (δ : ℂ) {a d : ℕ} (x : Matrix (Fin d) (Fin a) D.host.E)
    (hx : ∀ i j, ∃ b : 𝓞 D.host.E, x i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun v hv i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, x i j * v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := hx i j
      have h1 := (1 : Submodule (𝓞 D.host.E) D.host.E).smul_mem b (hv j trivial)
      rw [hb]
      simpa [Algebra.smul_def] using h1
    exact this

end GlobalTheory.FunObj.StdDatum.LiftCoset

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem unitBlock_mul_int (D : D7) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = 0 + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D 0 a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

end GlobalTheory.FunObj.StdDatum.LiftCoset

end
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

namespace GlobalTheory.BotFormula

theorem isFinPt_one : ∀ {D : D7} (V : HSp D) {n : ℕ}, V.rank = n → IsFinPt V (1 : GA D V) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  intro D V n hn
  subst hn
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  have hL : (finHom V (1 : GA D V)).val = 1 := by
    rw [map_one]; rfl
  rw [hL, Fin.cast_eq_self, Fin.cast_eq_self]
  show _ = toFinE D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end GlobalTheory.BotFormula
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

namespace GlobalTheory.FinPtMul

theorem isFinPt_mul : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x x' : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x' → IsFinPt V (g * g') (x * x') := by
  intro D V n g g' x x' hx hx'
  obtain ⟨hg, e, h⟩ := hx
  obtain ⟨hg', e', h'⟩ := hx'
  subst e
  refine ⟨mul_mem hg hg', rfl, fun i j => ?_⟩

  simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, Fin.cast_eq_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  have a := h i k
  have b := h' k j
  simp only [Fin.cast_eq_self] at a b
  rw [a, b]

end GlobalTheory.FinPtMul
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

theorem _root_.GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers : ∀ {D : D7} (A' : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A'), r.Is → r.IsStd → ∀ {n : ℕ}, n = A'.rank →
    ∀ gx : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n) → GA D A', (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) →
      (∀ g : GA D A', ∃! x, ∃ γ ∈ GQ A', ∃ k ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A'), g = γ * gx x * k) ∧
      ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧ (gx x)⁻¹ * γ * gx x ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A')}.ncard =
        GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out := by
  first | exact @GlobalTheory.BotClassDict.classes_and_stabilisers | exact GlobalTheory.BotClassDict.classes_and_stabilisers | (intros; apply GlobalTheory.BotClassDict.classes_and_stabilisers <;> assumption)
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

namespace GlobalTheory.FinPtUnique

theorem eq_of_isFinPt : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    IsFinPt V g x → IsFinPt V g' x → g = g' := by
  intro D V n g g' x ⟨hg, e, he⟩ ⟨hg', e', he'⟩
  apply GlobalTheory.FinRealComm.GA_ext_inf_fin V
  · have h1 : infHom V g = 1 := hg
    have h2 : infHom V g' = 1 := hg'
    rw [h1, h2]
  · apply Units.ext
    apply Matrix.ext
    intro i j
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [he i j, he' i j]

end GlobalTheory.FinPtUnique
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SchrLocModel

theorem box_mem : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) :=
  GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger

theorem decomp : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) :=
  GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators

def rhoSB {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) {κ : Type}
    [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) : Module.End ℂ (SB (κ → Fv F v)) where
  toFun φ := ⟨schr ψ w φ, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ w φ φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c φ := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem rhoSB_apply {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ)
    {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : SB (κ → Fv F v)) :
    ((rhoSB v ψ hψ w φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = schr ψ w φ := rfl

theorem schr_mem_span {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (s : (κ → R) → ℂ) (w : (κ → R) × (κ → R)) {f : (κ → R) → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)) :
    schr ψ w f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) := by
  let L : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) :=
    { toFun := schr ψ w
      map_add' := fun a b => by funext x; simp only [schr, Pi.add_apply, mul_add]
      map_smul' := fun c a => by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) ≤
      (Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨w', rfl⟩
    show schr ψ w (schr ψ w' s) ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)
    rw [schr_schr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + w', rfl⟩)
  exact hle hf

theorem schr_fst {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : κ → R) (f : (κ → R) → ℂ) : schr ψ (a, 0) f = fun x => f (x + a) := by
  funext x; simp [schr]

theorem span_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hu : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ) (hs : s ∈ SB (κ → Fv F v)) (hs0 : s ≠ 0) :
    ∀ φ ∈ SB (κ → Fv F v),
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro φ hφ
  obtain ⟨x₀, N₀, hN₀⟩ := box_mem F v ψ hu κ s hs hs0
  obtain ⟨N₁, hN₁⟩ := decomp F v κ φ hφ
  refine Submodule.span_le.mpr ?_ (hN₁ (max N₀ N₁) (le_max_right _ _))
  rintro _ ⟨c, rfl⟩
  have h := schr_mem_span ψ s (x₀ - c, 0) (hN₀ (max N₀ N₁) (le_max_left _ _))
  rw [schr_fst] at h
  rw [SetLike.mem_coe]
  convert h using 1
  funext x
  have e : ∀ i, x i + (x₀ i - c i) - x₀ i = x i - c i := fun i => by ring
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply, Pi.sub_apply, e, Pi.one_apply]

end GlobalTheory.SchrLocModel

namespace GlobalTheory.SchrLocModel

theorem locCo_onto {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm]
    {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ) {Y : Type} [AddCommGroup Y] (Xm : Y →+ Wm)
    (hX : ∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ x, GlobalTheory.LatVac.locCo co v (Xm x) = w := by
  set p : (κ → AF F) × (κ → AF F) := (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) with hp
  have hzat : At (evFin F v) (co.e.symm p) := by
    intro u hu
    have hp0 : u • p = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  obtain ⟨x, hx⟩ := (hX _).1 hzat
  refine ⟨x, ?_⟩
  rw [hx]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show evFin F v ((co.e (co.e.symm p)).1 k) = w.1 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
  · show evFin F v ((co.e (co.e.symm p)).2 k) = w.2 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)

theorem exists_locRho : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F _ _ v ψ hstd hunr Wm _ _ Bf κ _ co Y _ Xm χ hX hχ
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    have h : Continuous (GlobalTheory.LatVac.liftV v) := by
      change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
      exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
    exact hstd.1.comp h
  have evFin_invOf_two : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  have hat : ∀ x, At (evFin F v) (Xm x) := fun x => (hX (Xm x)).2 ⟨x, rfl⟩
  refine ⟨fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc (GlobalTheory.LatVac.locCo co v (Xm x)), ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro φ
    apply Subtype.ext; funext z
    simp [rhoSB, schr]
  · intro x y
    apply LinearMap.ext; intro φ
    apply Subtype.ext
    show schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm x))
        (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm y)) φ) =
      χ x y • schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm (x + y))) φ
    rw [schr_schr, map_add Xm, map_add (GlobalTheory.LatVac.locCo co v), ← hχ]
    congr 1
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.VacIndic.at_mul_left (GlobalTheory.LatVac.DualLoc.at_form co v (hat x) (Xm y))),
      map_mul (evFin F v), evFin_invOf_two, GlobalTheory.LatVac.DualLoc.evFin_form co v]
    rfl
  · intro x φ
    exact GlobalTheory.VacBridge.rho_acts_locCo co ψ v (Xm x) (hat x) φ
  · intro s hs
    rw [eq_top_iff]
    rintro t -
    have key := span_schr F v (GlobalTheory.LatVac.psiAt ψ v) (fun z => hunr z) κ s s.2
      (fun h => hs (Subtype.ext h)) t t.2
    have hmap : Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) =>
        schr (GlobalTheory.LatVac.psiAt ψ v) w (s : (κ → Fv F v) → ℂ)) =
        (Submodule.span ℂ (Set.range fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc
          (GlobalTheory.LatVac.locCo co v (Xm x)) s)).map (SB (κ → Fv F v)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨x, hx⟩ := locCo_onto v co Xm hX w
        exact ⟨x, by simp only [Function.comp_apply, Submodule.subtype_apply, rhoSB_apply, hx]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    rw [hmap] at key
    obtain ⟨u, hu, hut⟩ := key
    rwa [show u = t from Subtype.ext hut] at hu

end GlobalTheory.SchrLocModel
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schwartz_bruhat_restricted_product_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  first | exact @GlobalTheory.WeylTwist.pure_mul_psi | exact GlobalTheory.WeylTwist.pure_mul_psi | (intros; apply GlobalTheory.WeylTwist.pure_mul_psi <;> assumption)
end
