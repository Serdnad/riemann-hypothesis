module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle342
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle207
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.AdForm.level_col_sub_one_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  set_option maxHeartbeats 10000000 in
    next =>
      intro B X I hI hP l Z u a Ch A hA j hj b κ hκ v hv s
      obtain ⟨-, κ', hκ'⟩ := (hA.U j hj b κ).1 hκ
      have hgram : gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
      haveI : NeZero ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) := ⟨by
        have := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_add_three_le_k
        simp only [Ranks.N]; omega⟩
      obtain ⟨At, -, hpi, -⟩ := GlobalTheory.Mem.AtLevel.exists_atTTied I hI hP l Z u
      let sg : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E := RingOfIntegers.mapRingHom (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)
      have hsc : ∀ x, (sg x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.conj (x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
      have hpq : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) * (sg At.piU : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hsc]; exact At.piU_norm
      have hTp := ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T_prime
      have hp0 : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
      have hL : (A.K j hj b).lev.Lb = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) (((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)⁻¹) := by
        refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ At.piU hp0 _ ?_
        rw [hpi]; exact (hA.reads j hj).lb b
      have hx := (((A.K j hj b).lev.U_eq κ'.1).1 κ'.2).2 v
      have hT := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.fixed x).1 hx)
          (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.cmUnram.2.2 hgram (A.K j hj b).lev At.piU (sg At.piU) rfl hpq hTp hL v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u At v hv) _).1 hx
      have hsp : Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb) = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) ((sg At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hL, hgram]; exact GlobalTheory.uLocDual_eq (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (fun x => star_star x) _ At.piU (sg At.piU) hp0 rfl
      have hy : (fun r => Formalism.UG.inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((Pi.single s 1 : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) r)) ∈ Formalism.UG.latS (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (intV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E v) (Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb)) := by
        simp only [hsp]
        refine Submodule.subset_span ⟨Pi.single s 1, ?_, rfl⟩
        rw [SetLike.mem_coe, Formalism.L2.Col.rll_mem_dLat]
        refine ⟨fun i _ => ?_, ?_⟩
        · by_cases h : i = s
          · subst h; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _
        · by_cases h : Formalism.L2.Col.lastIdx ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) = s
          · rw [h, Pi.single_eq_same, mul_one]; exact ⟨sg At.piU, rfl⟩
          · rw [Pi.single_eq_of_ne h, mul_zero]; exact zero_mem _
      have key := hT.2 _ hy
      convert key using 1
      funext r
      have hm : ((Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) κ'.1 : GL _ _) : Matrix _ _ _) = (κ'.1.1).map (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) := rfl
      rw [Pi.sub_apply, hm, hκ']
      congr 1
      · simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]
      · simp [Pi.single_apply, Matrix.one_apply]

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem rapidVal_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, RapidVal D := by
  intro hP D θ hθ V S M J χ G hG v
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hG)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    have h1 := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ (hM.aut w) (hM.cusp w)
    have h2 : G (r • PiTensorProduct.tprod ℂ w) = r • PiTensorProduct.lift.symm G w := by
      simp [PiTensorProduct.lift_symm]
    rw [h2]
    exact GlobalTheory.Grow.RapidDec.smul r h1
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem chOf_dil : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ j, j ≤ B.R.m → ∀ (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) (c : (I.chain l u a).cls j),
    A.chOf j ((I.fm l u a).dil j v s c) = A.chOf j c := by
  intro B X I hI hP l Z u a Ch A hA j hj v s c
  exact ((hA.reads j hj).key _ _).2 ⟨rfl, GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v s c⟩

end GlobalTheory.AdForm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwDat

theorem int_eq_sub_half (R : Ranks) (j : ℕ) (s z : ℤ) (h : (s : ℚ) = z - (R.N j : ℚ) / 2) : s = z - (R.N j : ℤ) / 2 := by
  obtain ⟨b, hb⟩ := N_even R j
  have e : (s : ℚ) = ((z - b : ℤ) : ℚ) := by rw [h, hb]; push_cast; ring
  have e' : s = z - b := by exact_mod_cast e
  rw [e', hb]
  omega



theorem chr_exp_shifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  intro B X I hI _ l Z u a Ch A hA i hi
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  obtain ⟨n, hn, hord⟩ := htw.1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hinf := Formalism.L2.Host.HChar.HasInfQ.mul_triv (I.C.isMu0 ⟨i, hi⟩).inf
    (Formalism.L2.Host.HChar.inf_eq_one_of_order hn hord)
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ (hA.chr ⟨i, hi⟩)).2 hinf
  refine ⟨fun τ => -e τ, fun τ => ?_, fun τ => ?_⟩
  · have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
    exact e1 ▸ hexp τ
  · have hw : (B.hcW u τ).e ⟨i, hi⟩ = e τ := by
      have h : (B.hcW u τ).e = (B.hc τ).e := (I.rec7 l Z).hcW_e u τ
      rw [h, he τ]
    have h1 : (I.chain l u a).sSharp i τ = e τ - (B.R.N (i + 1) : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sSharp_eq i hi τ, ← hw]
      rfl
    have h2 : (I.chain l u a).sDiv i τ = e τ - (B.R.N i : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sDiv_eq i hi τ, ← hw]
      rfl
    have r1 : ((I.rec7 l Z).sp.X (i + 1)).rank = B.R.N (i + 1) := rankN (I.rec7 l Z) (i + 1) hi
    have r0 : ((I.rec7 l Z).sp.X i).rank = B.R.N i := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
    refine ⟨?_, ?_, ?_⟩
    · rw [r1, h1, neg_neg]
    · rw [r0, h2]; ring
    · obtain ⟨k, -, hk, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u a) i hi
      exact (Int.natCast_nonneg (k τ)).trans_eq (hk τ).symm

end GlobalTheory.AdForm.TwDat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ValPart

theorem lift_compMultilinearMap {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : (Π i, Mi i) →ₘₗ[ℂ] E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s =>
    ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B →
      ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
          partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  intro hCRD D hMet hLev c hc j hj s hs u w B hw hB
  obtain ⟨-, hsphc, hsplit, -, hunif⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  obtain ⟨-, hopc, hconjH⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  obtain ⟨-, -, -, -, hmul, -⟩ := hLev c hc j hj s hs
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := (hlat _ B).1 hB
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsphc B
  have heig : ∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R ((hopc P d R).1 hR)
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap, hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero D hMet c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [sub_apply, smul_apply, zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.ChainOnto.ValPart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parIndep : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      have h1 := (hpar i.1).2 v i.2
      unfold ParFun at h1
      exact (hlat _ _).1 h1
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]

    · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
      exact Finset.sum_congr rfl (fun i _ => (map_mul (starRingEnd ℂ) _ _).symm)
    · intro i _ hne h0
      apply hne
      simp [h0]

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.ChainOnto.PetCoef.petco | exact GlobalTheory.ChainOnto.PetCoef.petco | (intros; apply GlobalTheory.ChainOnto.PetCoef.petco <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ), GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ = GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  first | exact @GlobalTheory.ChainOnto.chainPar_twist_chT | exact GlobalTheory.ChainOnto.chainPar_twist_chT | (intros; apply GlobalTheory.ChainOnto.chainPar_twist_chT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extS_slice :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  classical
  have hinj : Function.Injective (fun a : WO A T => (o.resS T).symm (a, 0)) := fun a b h => by
    simpa using h
  unfold comb extS
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, Pi.smul_apply, Pi.smul_apply, heisO_resS_symm]

end GlobalTheory.FinPl.ExtZero
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extT_resT_symm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  have h1 : ∀ (X Y : HSp D) (d : WO X Y →₀ ℂ) (g : WO X Y → ℂ) (x : WO X Y),
      comb ψ X Y d g x = d.sum fun u a => a * heisO ψ X Y u g x := by
    intro X Y d g x
    simp only [comb, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h1, extT, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun u _ => by rw [heisO_resT_symm]

end GlobalTheory.FinPl.ExtZero
end

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow : ∀ (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ), 0 < c → (∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) → ContMod T e → ContMod T e' := by
  first | exact @GlobalTheory.EisCont.Shift.contMod_shift | exact GlobalTheory.EisCont.Shift.contMod_shift | (intros; apply GlobalTheory.EisCont.Shift.contMod_shift <;> assumption)
end
