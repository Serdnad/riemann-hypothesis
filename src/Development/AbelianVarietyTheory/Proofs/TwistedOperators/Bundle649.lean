module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle644
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle560
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  first | exact @GlobalTheory.CommVac.heisO_offPart_vac | exact GlobalTheory.CommVac.heisO_offPart_vac | (intros; apply GlobalTheory.CommVac.heisO_offPart_vac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

theorem level_datum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Irow := GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iint := GlobalTheory.T.latticeVector_adjointRow_integral D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iker := GlobalTheory.T.adjointFrameRowReduction_eq_zero_iff_mem D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Isurj := GlobalTheory.T.rowReduction_surjective_latticeVectors_places D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Ilin := GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers D T βT a e
  set R := GlobalTheory.LiftDat.rowRed T βT a e with hR
  have hz : ∀ PP, R PP 0 = 0 := by
    intro PP
    have hi := Iint 0 (zero_mem _)
    have h := (Ilin PP 0 0 hi hi 1).2
    simp only [smul_zero, add_zero, map_one, one_mul] at h
    funext j
    have h' := congrFun h j
    simp only [Pi.zero_apply]
    linear_combination -h'
  have hsum : ∀ PP (s : Finset (Fin T.rank)) (c : Fin T.rank → 𝓞 D.host.E)
      (u : Fin T.rank → Fin T.rank → D.host.E) (v : Fin T.rank → D.host.E), (∀ j, u j ∈ C.X.Λ) → v ∈ C.X.Λ →
      R PP (∑ j ∈ s, c j • u j + v) = fun l => ∑ j ∈ s, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c j)) *
        R PP (u j) l + R PP v l := by
    intro PP s c u v hu hv
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hm : ∑ j ∈ s, c j • u j + v ∈ C.X.Λ := add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hu j)) hv
      rw [Finset.sum_insert hj, add_assoc]
      rw [show c j • u j = ((c j : D.host.E)) • u j from rfl]
      rw [(Ilin PP (u j) _ (Iint _ (hu j)) (Iint _ hm) (c j)).2, ih]
      funext l
      rw [Finset.sum_insert hj]
      ring
  choose β hβΛ hβred using fun j : Fin T.rank => Isurj (fun PP => Pi.single j 1)
  have hexp : ∀ PP ∈ Pg ∪ Q, ∀ (c : Fin T.rank → 𝓞 D.host.E) (w : Fin T.rank → D.host.E), w ∈ C.X.Λ →
      ∀ l, R PP (∑ j, c j • β j + w) l = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c l)) + R PP w l := by
    intro PP hPP c w hw l
    rw [hsum PP Finset.univ c β w hβΛ hw]
    simp only [hβred _ PP hPP, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
    intro v hv
    choose c hc using fun j => GlobalTheory.T.exists_integer_conj_prescribed_residues_places D (Pg ∪ Q) (fun PP => R PP v j)
    have hw : v - ∑ j, c j • β j ∈ C.X.Λ := sub_mem hv (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have hw0 : v - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      refine (Iker _ hw).1 fun PP hPP => ?_
      funext l
      have h := hexp PP hPP c _ hw l
      rw [add_sub_cancel, hc l PP hPP] at h
      simp only [Pi.zero_apply]
      linear_combination -h
    have e1 : v = ∑ j, c j • β j + (v - ∑ j, c j • β j) := by abel
    rw [e1]
    exact Submodule.add_mem_sup (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) hw0
  obtain ⟨Lv0, hw⟩ := GlobalTheory.Ker.Base.exists_level C.X
  have hle : ∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftLevel.liftI Pg Q ≤ conjI PP.asIdeal := fun PP h => GlobalTheory.LiftDat.liftI_le h
  have hnot : ∀ PP ∈ Pg ∪ Q, ∀ s : 𝓞 D.host.E, IsCoprime (Ideal.span {s}) (GlobalTheory.LiftLevel.liftI Pg Q) →
      GlobalTheory.SW.Lev.bar s ∉ PP.asIdeal := by
    intro PP hPP s hs hmem
    obtain ⟨x, m, hm, hxm⟩ := GlobalTheory.SW.Lev.cop_iff.1 hs
    have h1m : (1 : 𝓞 D.host.E) ∈ conjI PP.asIdeal := by
      rw [← hxm]
      exact add_mem (Ideal.mul_mem_left _ _ (GlobalTheory.SW.Lev.mem_conjI.2 hmem)) (hle PP hPP hm)
    have := GlobalTheory.SW.Lev.mem_conjI.1 h1m
    rw [map_one] at this
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hind : ∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 →
      ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
    intro d ⟨s, hs, hsm⟩ j
    rw [sub_zero, Finset.smul_sum] at hsm
    have e2 : ∑ j, s • d j • β j = ∑ j, (s * d j) • β j + 0 := by
      rw [add_zero]; exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm
    rw [e2] at hsm
    refine GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place D Pg Q _ fun PP hPP => ?_
    have h0 := hexp PP hPP (fun j => s * d j) 0 (zero_mem _) j
    have hmemΛ : ∑ j, (s * d j) • β j + 0 ∈ C.X.Λ :=
      add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j)) (zero_mem _)
    rw [(Iker _ hmemΛ).2 hsm PP hPP, hz] at h0
    simp only [Pi.zero_apply, add_zero, map_mul] at h0
    have h0' : GlobalTheory.SW.Lev.bar s * GlobalTheory.SW.Lev.bar (d j) ∈ PP.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_mul]; exact h0.symm)
    rcases PP.isPrime.mem_or_mem h0' with h | h
    · exact absurd h (hnot PP hPP s hs)
    · exact GlobalTheory.SW.Lev.mem_conjI.2 h
  refine ⟨GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0, rfl, hw, ?_, ?_⟩
  · intro κ hκ κ' hκ' PP hPP i j
    have hm := GlobalTheory.LiftDat.mem_Jgrp.1 hκ PP hPP
    have hij := congrArg (fun g : GL (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal) => g.val i j) hm
    have hk := congrFun (congrFun hκ' i) j
    change (GlobalTheory.LiftDat.toConj Pg Q PP (Finset.mem_union_left _ hPP)) (κ.val i j) =
      (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j at hij
    simp only [Matrix.map_apply] at hk
    rw [← hk] at hij
    have hij2 : Ideal.Quotient.mk (conjI PP.asIdeal) (κ' i j) =
        (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j := hij
    rw [← Ideal.Quotient.eq, hij2]
    by_cases hij' : i = j
    · subst hij'; simp
    · simp [Matrix.one_apply_ne hij']
  · intro y hy
    have hrow : ∀ i, y i ∈ C.X.Λ := by
      intro i
      have key : ∀ z ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI (GlobalTheory.LiftLevel.liftI Pg Q)) • C.X.Λ),
          z i ∈ C.X.Λ := by
        intro z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨v, hv, u, hu, rfl⟩ := hz
          have hvi : IsIntegral ℤ (v i) := (GlobalTheory.SW.Base.mem_stdL _).1 hv i
          have : vecMulVec v u i = (⟨v i, hvi⟩ : 𝓞 D.host.E) • u := by
            funext k; rw [vecMulVec_apply, Pi.smul_apply, Algebra.smul_def]; rfl
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.smul_le_right hu)
        | zero => exact zero_mem _
        | add x y _ _ hx hy => exact add_mem hx hy
        | neg x _ hx => exact neg_mem hx
      exact key y hy
    have hdec : ∀ i, ∃ c : Fin T.rank → 𝓞 D.host.E, y i - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      intro i
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hsp (hrow i))
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hp
      refine ⟨c, ?_⟩
      rw [hc, ← hpq, add_sub_cancel_left]
      exact hq
    choose c hc using hdec
    refine GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters D S T C hn Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0 hind y c hc _ ?_
    intro PP hPP i j
    rw [Irow]
    have hw : y i - ∑ j, c i j • β j ∈ C.X.Λ := sub_mem (hrow i) (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have h := hexp PP hPP (c i) _ hw j
    rw [add_sub_cancel, (Iker _ hw).2 (hc i) PP hPP, Pi.zero_apply, add_zero] at h
    exact h

end GlobalTheory.LiftDat

end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem tprod_ne_zero_of_ne {κ : Type} [Fintype κ] {V : κ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {v : ∀ j, V j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem tmul_ne_zero_of_ne {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} {y : Q}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h0
  have := congrArg ((TensorProduct.rid ℂ P).toLinearMap ∘ₗ LinearMap.lTensor P l) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero, hl,
    one_smul] at this
  exact hx this

theorem pure_neg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (-f) φ = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, neg_mul]

theorem exists_not_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  classical
  haveI := hM.real.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, hfP, hfy⟩ : ∃ f ∈ G.M.Pol Bs.ψ Bs.emb, R.p f = y := by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  have hloc : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v φ ≠ 0 := fun v => by
    haveI := hM.fin.nontriv v
    obtain ⟨z, hz⟩ := exists_ne (0 : Rf.Pi v)
    have : z ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := (hM.fin.onto v) ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 this
    exact ⟨φ, hφ, hz⟩
  choose ψ0 hψ0 hψ0ne using hloc
  have hvac := hM.triple.geo.hM.vac
  let φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun v => if v ∈ Xc.T then ψ0 v else G.M.vac v
  have hφSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0 v
    · simp only [φ, h, if_false]; exact (hvac v).1
  have hφout : ∀ v ∉ Xc.T, φ v = G.M.vac v := fun v h => by simp [φ, h]
  have hφne : ∀ v, Rf.p v (φ v) ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0ne v
    · simp only [φ, h, if_false]; exact (hM.fin.sph v h).2
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, ?_, ?_⟩
  · have := sum_pure_mem_algD G.M Bs.ψ Bs.emb Xc.T (m := 1) (fun _ => f) (fun _ => φ) (fun _ => ⟨hfP, hφSB, hφout⟩)
    simpa using this
  · rintro ⟨T, hT, m, f', φ', hf', hΦ, hsum⟩
    let g : Fin (m + 1) → SInf F (Fin a × Fin (a + a')) := Fin.cons (-f) f'
    let χ : Fin (m + 1) → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := Fin.cons φ φ'
    have h0 : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (χ i) = 0 := by
      simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, pure_neg, ← hΦ, neg_add_cancel]
    have hout : ∀ i, ∀ v ∉ T, χ i v = G.M.vac v := by
      intro i v hv
      induction i using Fin.cases with
      | zero => exact hφout v (fun h => hv (hT h))
      | succ j => exact (hf' j).2.2 v hv
    have key := GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M.vac (fun v => (hvac v).2.1) hM.triple.geo.hM.std R.p Rf.Pi Rf.p T (m + 1) g χ hout h0
    simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, map_neg, TensorProduct.neg_tmul, hsum, add_zero,
      neg_eq_zero] at key
    exact tmul_ne_zero_of_ne (hfy ▸ hy) (tprod_ne_zero_of_ne fun v : T => hφne v.1) key

end GlobalTheory.PolKer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

end GlobalTheory.PairIt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
theorem stepFn_congr_red (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) {w : Pl D.host.E}
    (hw : w ∈ topPl L t) {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hP : w ∈ L.Pg
  · have hr : D.R.r ≤ a := ha ▸ Nat.le_add_right _ _
    rw [stepFn_of_mem_Pg t w hP]
    by_cases H : LowZero a (N.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N.map (resS D.host.F w)) g
    · obtain ⟨h0, g, hg⟩ := H
      have h0' : LowZero a (N'.map (resS D.host.F w)) := by rw [← h]; exact h0
      have hg' : TopCond D.R.t hr (N'.map (resS D.host.F w)) g := by rw [← h]; exact hg
      have e1 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N h0 hg
      have e2 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N' h0' hg'
      exact e1.trans e2.symm
    · have H' : ¬ (LowZero a (N'.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N'.map (resS D.host.F w)) g) := by rw [← h]; exact H
      have e1 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N).1 H)
      have e2 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N').1 H')
      exact e1.trans e2.symm
  · have hQ : w ∈ L.Q t := by
      unfold topPl at hw
      exact (Finset.mem_union.1 hw).resolve_left hP
    have e1 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N
    have e2 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N'
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact congrArg (fun y => if H : LowZero D.R.r y ∧ IsUnit (topL D.R.r y).det then (L.xiR t w H.2.unit : ℂ) else 0) h



theorem isSBHalf_topFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  intro D T L sc G B μ₀ hL t e he j hj
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he

  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ topPl L t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (topPl L t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ topPl L t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold GlobalTheory.FlipTop.topFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red G hL t hj hw _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this

end GlobalTheory.FlipTop

end
end
