module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BaseGoodPlace

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ¬ differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af D.host.F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af D.host.F, (∀ w, β w ∈ w.adicCompletionIntegers D.host.F) → ψ (pairA D.host.F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem trInf_eq_trace (D : D7) (x : Ainf D.host.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x = Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace D.host.F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem isStd_of_isStdChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by
  refine ⟨hψ.1.1, hψ.1.2.2.1, fun a ha => ?_⟩
  have h2 : a.2 = 0 := by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (pairA D.host.F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
      exact map_zero _
    have := congrArg Prod.snd (ha (pairA D.host.F 0 1) h0)
    rw [smul_eq_mul] at this
    have e : (1 : Af D.host.F) * a.2 = 0 := this
    simpa using e
  have ha' : a = pairA D.host.F a.1 0 := Prod.ext rfl h2
  obtain ⟨θ, hθ⟩ := hψ.2.1
  have h := hψ.2.2 θ hθ a.1
  rw [GlobalTheory.DualPairCompare.sum_infFam θ hθ, trInf_eq_trace] at h
  rw [ha']
  change psiInf D.host.F ψ a.1 = _
  rw [h]
  congr 1
  push_cast
  change _ = -(2 * ↑Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F a.1) : ℝ) : ℂ)
  ring

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem exists_ram_prime_of_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hle : differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p ∣ D.host.QS * D.host.q * D.host.d ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  obtain ⟨p, -, h1, h2⟩ := UpperTheory.Ram.Fun.exists_prime_of_different_le D.host v hle
  exact ⟨p, h1, h2⟩

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.FunObj

theorem base_isGood_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  intro D T L sc G μ₀ _hL W t hS B hB hP
  have hψ : IsStdChar D B.ψ (-1) := hB ▸ W.ψ_std
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := ?_ }
  · intro v w hw
    have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
      rintro ⟨w1, w2, hne, h1, h2⟩
      apply hne
      have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
        have hle : w.asIdeal ≤ u.asIdeal := by
          rw [← hw]
          exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
        exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
      rw [key w1 h1, key w2 h2]
    obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
    exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hP v hv
    refine GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ _ fun hle => ?_
    obtain ⟨p, hp, hpv⟩ := GlobalTheory.BaseGoodPlace.exists_ram_prime_of_le D _ hle
    have hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h := hpv
      change (p : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) at h
      rwa [Ideal.mem_comap, map_natCast] at h
    apply hS.2 w hw
    obtain ⟨c, hc⟩ := hp
    rw [hc]
    push_cast
    exact w.asIdeal.mul_mem_right _ (w.asIdeal.mul_mem_right _ hpw)

end GlobalTheory.FunObj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ContSymp

theorem continuous_psi_symp_atPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  intro F E _ _ _ _ _ σ ψ hψ n d JA JB o v M _ g
  set B := GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) with hB
  have hadd1 : ∀ x x' y, B (x + x') y = B x y + B x' y := by
    intro x x' y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, ← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib, Matrix.add_apply, add_mul]
  have hadd2 : ∀ x y y', B x (y + y') = B x y + B x y' := by
    intro x y y'
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hsm1 : ∀ (r : AF F) x y, B (r • x) y = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm,
      LinearMap.map_smul, smul_eq_mul]
  have hsm2 : ∀ (r : AF F) x y, B x (r • y) = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum,
      smul_eq_mul]
  let Bl : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] AF F :=
    LinearMap.mk₂ (AF F) B hadd1 (fun r x y => by rw [hsm1, smul_eq_mul]) hadd2 (fun r x y => by rw [hsm2, smul_eq_mul])
  have hexp : ∀ a : M → v.adicCompletionIntegers F,
      B (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * ∑ m', GlobalTheory.EmbChart.atPlace v (a m' : Fv F v) *
        B (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    change Bl _ _ = _

    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rfl
  simp_rw [hexp]
  have hc : ∀ m, Continuous fun a : M → v.adicCompletionIntegers F => GlobalTheory.EmbChart.atPlace v (a m : Fv F v) :=
    fun m => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_subtype_val.comp (continuous_apply m))
  refine hψ.comp (continuous_const.mul (continuous_finsetSum _ fun m _ => (hc m).mul (continuous_finsetSum _ fun m' _ =>
    (hc m').mul continuous_const)))

end GlobalTheory.ContSymp
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem subsingleton_spectrum_dualNumber (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ (p : PrimeSpectrum (DualNumber K)) (x : DualNumber K), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h
      have hsq : x * x = 0 := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h]
      exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [key p x, key q x])⟩

private theorem spMap_comp_of_eq {R₁ R₂ R₂' R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₂'] [CommRing R₃]
    {f : R₁ →+* R₂} {g : R₂ →+* R₃} {f' : R₁ →+* R₂'} {g' : R₂' →+* R₃} (h : g.comp f = g'.comp f') :
    spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tanLift_of_fieldChart : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [LocallyOfFiniteType U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → FieldChart A M →
      TanLift A M := by
  intro S A _ hA U _ M hM hInj hFC k _ s N hN u₀ h₀
  obtain ⟨hpull, -, -, hcomp, hev⟩ := GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A
  obtain ⟨ψ, hψ₁, hψ₂, hflat, hsurj⟩ :=
    GlobalTheory.T.dualNumber_fieldHom_flat_surjective k (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k))

  let T : Over S := Over.mk (spMap (dnInl k) ≫ s)
  haveI : IsNoetherianRing (DualNumber k) := inferInstance
  haveI : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  obtain ⟨G, π, hmono, -, hG⟩ := GlobalTheory.T.exists_mono_finiteType_agreement_locus_injective_family S A hA T U N M hN hM hInj
  haveI : Mono π.left := hmono

  let Y : Over S := Over.mk (spMap ψ ≫ spMap (dnInl k) ≫ s)
  let y : Y ⟶ T := Over.homMk (spMap ψ)
  have hq : spMap ψ ≫ spMap (dnInl k) =
      spMap (dnInl (AlgebraicClosure k)) ≫ spMap (algebraMap k (AlgebraicClosure k)) :=
    spMap_comp_of_eq hψ₁
  let q : Y ⟶ Over.mk (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) :=
    Over.homMk (spMap (dnInl (AlgebraicClosure k))) ((reassoc_of% hq) s).symm
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := hpull T Y N y hN
  obtain ⟨W, hW⟩ := hFC (AlgebraicClosure k) (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) Y q _ hN'

  let Z : Over S := Over.mk (spMap (dnFst (AlgebraicClosure k)) ≫ Y.hom)
  let z : Z ⟶ Y := Over.homMk (spMap (dnFst (AlgebraicClosure k)))
  have hr : spMap (dnFst (AlgebraicClosure k)) ≫ spMap ψ =
      spMap (algebraMap k (AlgebraicClosure k)) ≫ spMap (dnFst k) :=
    spMap_comp_of_eq hψ₂
  let e : Z ⟶ Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) :=
    Over.homMk (spMap (algebraMap k (AlgebraicClosure k))) ((reassoc_of% hr) (spMap (dnInl k) ≫ s)).symm
  have hez : e ≫ ptMap _ (dnFst k) = z ≫ y := by
    ext
    exact hr.symm
  have h₁ : Same A N M (z ≫ y) (e ≫ u₀) := by
    rw [← hez]
    exact hcomp T U _ Z N M (ptMap _ (dnFst k)) u₀ e hN.isLB hM.isLB h₀
  have h₂ : Same A (ev N (fst A Y) (snd A Y ≫ y)) M z (e ≫ u₀) :=
    (hev T U Y Z N M y z _ hN.isLB hM.isLB).2 h₁
  have hx : ∀ x, z.left x ∈ W := (hW Z z).1 ⟨_, h₂⟩

  haveI : Subsingleton Y.left := subsingleton_spectrum_dualNumber (AlgebraicClosure k)
  have x₀ : Z.left := IsLocalRing.closedPoint (AlgebraicClosure k)
  have hall : ∀ x : Y.left, x ∈ W := fun x => by
    rw [Subsingleton.elim x (z.left x₀)]
    exact hx x₀
  obtain ⟨u', hu'⟩ := (hW Y (𝟙 Y)).2 (fun x => hall _)
  have h₃ : Same A N M y u' := by
    have := (hev T U Y Y N M y (𝟙 Y) u' hN.isLB hM.isLB).1 hu'
    rwa [Category.id_comp] at this

  obtain ⟨z', hz'⟩ := (hG Y y).1 ⟨u', h₃⟩
  haveI : Flat (spMap ψ) := hflat
  haveI : Surjective (spMap ψ) := hsurj
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lift_mono_of_fpqc_cover_lift G.left T.left Y.left T.left π.left (𝟙 _) (spMap ψ) z'
    (by rw [Category.comp_id]; exact hz')
  exact (hG T (𝟙 T)).2 ⟨w, hw⟩

end GlobalTheory.DualOpen
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem linesLE_zero_of_sub_lie : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → LinesLE g 0 := by
  intro k K _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s g hV₀ hs hg hloc
  intro E _ _ _ _ _ ρ hρ w hw
  simp only [zero_mul]
  by_contra hpos
  push_neg at hpos
  have hpos' : 0 < degLine (pullAd ρ g) w := by exact_mod_cast hpos
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  letI : Algebra ℚ E := DivisionRing.toRatAlgebra

  have hne : Nonempty (Place k E) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [degLine, finsum_of_isEmpty] at hpos'
  obtain ⟨p₀⟩ := hne
  obtain ⟨b₀, V, t, V', h₀, h₁, hxV, M, -, -, -, -, -⟩ := hloc (ρ p₀)
  set b : Sp E ⟶ C := spMap (algebraMap K E) ≫ x with hb
  have hbV : ⊤ ≤ b ⁻¹ᵁ V₀ := by
    intro z _
    have hz := h₀ (hxV (show (spMap (algebraMap K E)).base z ∈ (⊤ : (Sp K).Opens) from trivial))
    show b.base z ∈ V₀
    simpa [hb] using hz
  haveI : QuasiSeparated G.hom := inferInstance
  obtain ⟨ξ, hξ, htan⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G E hG.smooth inferInstance b r V₀ (fun j => i.app V₀ (s j)) w hbV

  have hvec : ∀ p : Place k E, (pullAd ρ g p).mulVec w ≠ 0 := by
    intro p h
    have hdet : (pullAd ρ g p).det ≠ 0 := by
      simp only [pullAd]
      have e := RingHom.map_det (algebraMap K E) (g (ρ p))
      rw [RingHom.mapMatrix_apply] at e
      rw [← e]
      exact (map_ne_zero _).mpr (hg.1 (ρ p))
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
  have hu : ∀ p : Place k E, ∃ u : E, u ≠ 0 ∧ p.1 u = nrm p ((pullAd ρ g p).mulVec w) ∧
      ordVec p ((pullAd ρ g p).mulVec w) = ord p u := by
    intro p
    obtain ⟨j, hj0, hj1, hj2, -⟩ := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k E p).2.2.2.2.2.2.1) r _ (hvec p)
    exact ⟨_, hj0, hj1.symm, hj2⟩
  choose u hu0 hu1 hu2 using hu
  have hsum : ∑ᶠ p, ord p (u p) = degLine (pullAd ρ g) w := by
    unfold degLine; exact finsum_congr fun p => (hu2 p).symm
  have hfin : {p | ord p (u p) ≠ 0}.Finite := by
    by_contra hinf
    have : ∑ᶠ p, ord p (u p) = 0 := finsum_of_infinite_support (by simpa [Function.support] using hinf)
    omega
  have hint := fun p => GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath k K E C x hx G hG W r i V₀ s ρ hρ p (g (ρ p)) (hloc (ρ p)) w (u p) (hu0 p) (hu1 p) ξ hξ htan
  have hrat := GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces k K E C x hx G ξ u hu0 hfin (by omega) hint
  have htriv : ξ = triv G b := GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian C G hG E b ξ hξ hrat
  rw [htriv] at htan
  exact hw (GlobalTheory.T.tangent_constantPath_eq_zero k K E C x hx G hG W r i hi V₀ s hV₀ hs w htan)

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSectionCount_log_twist_continuity_above : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop, P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.lc_add_div_sub_le | exact GlobalTheory.HSNef.lc_add_div_sub_le | (intros; apply GlobalTheory.HSNef.lc_add_div_sub_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  first | exact @GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | exact GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam | (intros; apply GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam <;> assumption)
end
