module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toAfE_inc (D : D7) (x : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
  have h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])
  have h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])
  show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _
  rw [h2, ← h1, RingEquiv.symm_apply_apply]

theorem adSwap_inc (D : D7) (x : D.host.E) : adSwap D (StandardLatticesGL3.inc D x) = inclEAf D x := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _
  rw [toAfE_inc]
  rfl

theorem finE_val_of_isRat {D : D7} {V : HSp D} {g : GA D V} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : GlobalTheory.RatAut.IsRat V g a) :
    (Lev.finE V g).val = a.map (inclEAf D) := by
  have e : (Lev.finE V g).val =
      (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y)) := rfl
  rw [e, show Formalism.L2.Theta.mt V g = _ from h]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rfl

theorem frConj_ratG : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E),
    Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 →
    ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  intro D V fr hfr
  let S : Subgroup (StandardLatticesGL3.GA D V.rank) :=
    ((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
  suffices hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by
    intro γ hγ
    obtain ⟨q, hq, e⟩ := hS hγ
    exact ⟨q, hq, e⟩
  rw [GlobalTheory.NormSum.ratG, Subgroup.closure_le]
  rintro g ⟨γ₀, hγ₀⟩

  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := g.2
  have hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose := by
    ext i j
    simp [StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]
  have hu : (γ₀.map D.host.conj).transpose * γ₀ = 1 := by
    apply Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
    exact hg.trans h1.symm
  have hu' : γ₀ᴴ * γ₀ = 1 := by
    have : γ₀ᴴ = (γ₀.map D.host.conj).transpose := Matrix.ext fun i j => by
      show star (γ₀ j i) = D.host.conj (γ₀ j i)
      exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)
    rw [this, hu]

  set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF
  set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi
  have hFFi : F * Fi = 1 := by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Fᴴ * V.gram * F = 1 := hfr
  have hJ : V.gram = Fiᴴ * Fi := by
    have := congrArg (fun M => Fiᴴ * M * Fi) hfr'
    simp only [Matrix.mul_one] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
  set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha
  have hau : aᴴ * V.gram * a = V.gram := by
    have e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi := by
      rw [ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]
  obtain ⟨g', hg'Q, hg'⟩ := GlobalTheory.RatAut.exists_of_unitary V hau
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')
  have hkC : k ∈ GfC V := MonoidHom.mem_ker.2 k1
  have hfin : finG V ⟨k, hkC⟩ = Lev.finE V g' := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')
    rw [k2]
  refine ⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩
  show finG V ⟨k, hkC⟩ = frConj fr g.1
  rw [hfin, frConj_apply]
  apply Units.ext
  rw [finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]
  have eb : ∀ (M : GL (Fin V.rank) D.host.E),
      (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D) := fun M => rfl
  have eg : (Formalism.UG.bc (adSwap D) g.1).val =
      γ₀.map (inclEAf D) := by
    show g.1.val.map (adSwap D) = _
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, Matrix.map_map]
    exact Matrix.ext fun i j => adSwap_inc D (γ₀ i j)
  rw [eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]

end GlobalTheory.FrameTransport
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameTransport.IntSwap

theorem toFinE_mem_intAd {D : D7} {x : StandardLatticesGL3.AE D} (hx : x ∈ StandardLatticesGL3.OhE D) :
    GlobalTheory.BotFormula.toFinE D x ∈ Formalism.UG.intAd D.host.E := by
  have key : ∀ y : StandardLatticesGL3.AE D,
      (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)) y ∈
        AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ℚ ⊗[ℚ] D.host.E |
          ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf ℚ, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[ℚ] (o : D.host.E)} →
      GlobalTheory.BotFormula.toFinE D y ∈ Formalism.UG.intAd D.host.E := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).1 hy
  have hle : StandardLatticesGL3.OhE D ≤ (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      refine key _ (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, rfl⟩)
      exact (one_mem (v.adicCompletionIntegers ℚ) : _)
    · refine key _ (AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, ?_⟩)
      rfl
  exact hle hx

theorem swapAE_mem_intAf {D : D7} {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)}) :
    Lev.swapAE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hle : AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup.comap (Lev.swapAE D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, o, rfl⟩
    have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) *
          ((1 : D.host.E) ⊗ₜ[D.host.F] (a : Formalism.L2.Herm.Af D.host.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    show Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
    rw [e]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(o : D.host.E), o, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  exact hle hy

end GlobalTheory.FrameTransport.IntSwap

theorem GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D →
    GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D x hx
  have h1 := GlobalTheory.FrameTransport.IntSwap.toFinE_mem_intAd hx
  have h2 : GlobalTheory.BotFormula.toAfE D x ∈ AddSubgroup.closure
      {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
        ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} := by
    refine (GlobalTheory.LFun.mem_int_iff _).2 fun P => ?_
    have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.BotFormula.toAfE D x) = GlobalTheory.BotFormula.toFinE D x :=
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _
    rw [e]
    exact h1 P
  exact GlobalTheory.FrameTransport.IntSwap.swapAE_mem_intAf h2
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain Topology

theorem toFinE_symm_mem_OhE {D : D7} (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (ht : ∀ w : HeightOneSpectrum (𝓞 D.host.E), t w ∈ w.adicCompletionIntegers D.host.E) :
    (GlobalTheory.BotFormula.toFinE D).symm t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := fun x a => by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  refine GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (GlobalTheory.BotFormula.toFinE D).toRingHom) hι ?_
  change (GlobalTheory.BotFormula.toFinE D) ((GlobalTheory.BotFormula.toFinE D).symm t) ∈ _
  rw [RingEquiv.apply_symm_apply]
  exact ht

theorem continuous_finChar {D : D7} {N : ℕ} (c : HeckeU D N) : Continuous (finChar c) := by
  refine continuous_of_continuousAt_one (finChar c) ?_
  obtain ⟨m, hm, hc⟩ := c.cont
  have hcont : Continuous (finIdl D) :=
    Continuous.units_map _ (GlobalTheory.DefU.ClassFin.continuous_finAdEquiv.comp (GlobalTheory.Member.continuous_finPart D))
  set W : Set (FiniteAdeleRing (𝓞 D.host.E) D.host.E) :=
    {z | ∀ w : HeightOneSpectrum (𝓞 D.host.E), z w ∈ w.adicCompletionIntegers D.host.E} with hW
  have hWo : IsOpen W := RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  set k : FiniteAdeleRing (𝓞 D.host.E) D.host.E := algebraMap D.host.E _ (m : D.host.E)⁻¹ with hk
  have h1 : Continuous fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_val.comp hcont
  have h2 : Continuous fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_coe_inv.comp hcont
  have h3 : Continuous fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k := (h1.sub continuous_const).mul continuous_const
  set V : Set (AE D)ˣ := ((fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k) ⁻¹' W) with hVdef
  have hV : IsOpen V :=
    ((hWo.preimage h1).inter (hWo.preimage h2)).inter (hWo.preimage h3)
  have hzero : (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => zero_mem _
  have hone : (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => one_mem _
  have h1V : (1 : (AE D)ˣ) ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, Units.val_one]; exact hone
    · show (((finIdl D 1)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, inv_one, Units.val_one]; exact hone
    · show (((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k ∈ W
      rw [map_one, Units.val_one, sub_self, zero_mul]; exact hzero
  have hmE : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ x ∈ V, finChar c x = 1 := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    set u := finIdl D x with hu
    have hy : Formalism.MainNotions.StandardLatticesGL3.IntU D (finY D x) := by
      refine ⟨?_, ?_⟩
      · rw [coe_finY, ← coe_finIdl]
        exact toFinE_symm_mem_OhE _ hx1
      · rw [← map_inv, coe_finY, ← coe_finIdl, map_inv]
        exact toFinE_symm_mem_OhE _ hx2
    have hs : ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 =
        (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
      refine ⟨(GlobalTheory.BotFormula.toFinE D).symm ((((u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
        FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k), toFinE_symm_mem_OhE _ hx3, ?_⟩
      rw [coe_finY, ← coe_finIdl, ← hu, ← map_natCast (GlobalTheory.BotFormula.toFinE D).symm m, ← map_mul, ← map_one
        (GlobalTheory.BotFormula.toFinE D).symm, ← map_sub]
      congr 1
      have hmk : (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * k = 1 := by
        rw [hk, ← map_natCast (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) m, ← map_mul,
          mul_inv_cancel₀ hmE, map_one]
      rw [mul_comm, mul_assoc, mul_comm k, hmk, mul_one]
    have hf := hc _ hy hs
    exact Circle.ext (by rw [coe_finChar, hf, Units.val_one, Circle.coe_one])
  show Filter.Tendsto (finChar c) (𝓝 1) (𝓝 (finChar c 1))
  rw [map_one]
  exact tendsto_nhds_of_eventually_eq (Filter.eventually_of_mem (hV.mem_nhds h1V) key)

end GlobalTheory.HeckeUChar
end
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

def frameTorMat {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (X Y : Matrix (Fin n) (Fin r) A) (d : Fin r → Aˣ) : Matrix (Fin n) (Fin n) A :=
  1 + X * diagonal (fun i => (d i : A) - 1) * (cT s Y * J) +
    Y * diagonal (fun i => s ((d i)⁻¹ : Aˣ) - 1) * (cT s X * J)

section Alg

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem diagonal_sub_one' (a : Fin r → A) : diagonal (fun i => a i - 1) = diagonal a - 1 := by
  rw [← diagonal_one, diagonal_sub]

theorem frameTorMat_mul_X (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * X = X * diagonal fun i => (d i : A) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mul_Y (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * Y = Y * diagonal fun i => s ((d i)⁻¹ : Aˣ) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mulVec {z : Fin n → A} (hx : (cT s X * J) *ᵥ z = 0) (hy : (cT s Y * J) *ᵥ z = 0)
    (d : Fin r → Aˣ) : frameTorMat s J X Y d *ᵥ z = z := by
  rw [frameTorMat, add_mulVec, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, ← mulVec_mulVec, hx, mulVec_zero]
  simp

theorem frameTorMat_mul_inv (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1)
    (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) : frameTorMat s J X Y d * frameTorMat s J X Y d⁻¹ = 1 := by
  conv_lhs => rw [show frameTorMat s J X Y d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [← Matrix.mul_assoc (frameTorMat s J X Y d), frameTorMat_mul_X xx yx, frameTorMat_mul_Y yy xy,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h1 : ∀ i, (d i : A) * (((d⁻¹) i : Aˣ) - 1) = 1 - d i := fun i => by
    rw [Pi.inv_apply, mul_sub, Units.mul_inv, mul_one]
  have h2 : ∀ i, s ((d i)⁻¹ : Aˣ) * (s (((d⁻¹) i)⁻¹ : Aˣ) - 1) = 1 - s ((d i)⁻¹ : Aˣ) := fun i => by
    rw [Pi.inv_apply, inv_inv, mul_sub, ← map_mul, Units.inv_mul, map_one, mul_one]
  simp only [h1, h2, frameTorMat, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem frameTorMat_unitary (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (xx : cT s X * J * X = 0)
    (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    cT s (frameTorMat s J X Y d) * J * frameTorMat s J X Y d = J := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have cd : ∀ a : Fin r → A, cT s (diagonal a) = diagonal fun i => s (a i) := fun a => by
    ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (frameTorMat s J X Y d) * J = J * frameTorMat s J X Y d⁻¹ := by
    simp only [frameTorMat, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd, map_sub, map_one, hs, Pi.inv_apply, inv_inv,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : frameTorMat s J X Y d⁻¹ * frameTorMat s J X Y d = 1 := by
    simpa only [inv_inv] using frameTorMat_mul_inv xx yy xy yx d⁻¹
  rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one]

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem continuous_frameTorMat {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {s : B →+* B}
    (hs : Continuous s) {n r : ℕ} (J : Matrix (Fin n) (Fin n) B) (X Y : Matrix (Fin n) (Fin r) B) :
    Continuous (frameTorMat s J X Y) := by
  have h1 : Continuous fun d : Fin r → Bˣ => diagonal fun i => (d i : B) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i => (Units.continuous_val.comp (continuous_apply i)).sub continuous_const)
  have h2 : Continuous fun d : Fin r → Bˣ => diagonal fun i => s ((d i)⁻¹ : Bˣ) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i =>
      (hs.comp (Units.continuous_coe_inv.comp (continuous_apply i))).sub continuous_const)
  exact (continuous_const.add ((continuous_const.matrix_mul h1).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul h2).matrix_mul continuous_const)

theorem exists_continuous_isIdTorusElt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  set s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT s (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ {a : ℕ} (Z : Matrix (Fin n) (Fin a) E),
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin a) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) :=
    fun Z => by rw [c1]; simp only [adMat, JR, Matrix.map_mul] <;> rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E,
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
        adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hJ' : cT s (JR (AF F) J) = JR (AF F) J :=
    (c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j))
  have xx : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 0 := by
    rw [c2, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have yy : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 0 := by
    rw [c2, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have xy : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 1 := by
    rw [c2, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have yx : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 1 := by
    rw [c2, GlobalTheory.StdPar.yx h hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let M := frameTorMat s (JR (AF F) J) (adMat F X) (adMat F Y)
  have hinv : ∀ d, M d * M d⁻¹ = 1 := frameTorMat_mul_inv xx yy xy yx
  have hinv' : ∀ d, M d⁻¹ * M d = 1 := fun d => by simpa only [inv_inv] using hinv d⁻¹
  let t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J := fun l =>
    ⟨⟨M l, M l⁻¹, hinv l, hinv' l⟩, frameTorMat_unitary hs hJ' xx yy xy yx l⟩
  have hc : Continuous M := continuous_frameTorMat (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) _ _ _
  refine ⟨t, ?_, fun l => ⟨frameTorMat_mul_X xx yx l, ?_, fun z hz => ?_⟩⟩
  · refine Continuous.subtype_mk ((Units.continuous_iff (f := fun l => (⟨M l, M l⁻¹, hinv l, hinv' l⟩ : GL (Fin n) (AF F ⊗[F] E)))).2 ⟨hc, hc.comp continuous_inv⟩) _
  · refine (frameTorMat_mul_Y yy xy l).trans (congrArg (fun D => adMat F Y * diagonal D) (funext fun k => ?_))
    rw [← map_inv]; rfl
  · have key : ∀ C : Matrix (Fin n) (Fin r) E, z ∈ colPerp σ J C Set.univ →
        (cT s (adMat F C) * JR (AF F) J) *ᵥ z = 0 := fun C hC => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 hC i
      simpa using this
    exact frameTorMat_mulVec (key X hz.1) (key Y hz.2) l

end Main

end GlobalTheory.IdTorus
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.stepVariablesCount_gridLocalFlipGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  first | exact @GlobalTheory.UnfoldLoss.varCount_locGrid_le | exact GlobalTheory.UnfoldLoss.varCount_locGrid_le | (intros; apply GlobalTheory.UnfoldLoss.varCount_locGrid_le <;> assumption)
end
