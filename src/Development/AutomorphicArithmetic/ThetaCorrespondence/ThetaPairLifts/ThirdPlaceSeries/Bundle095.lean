module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle391
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Formalism.LocalRingCardinality.Bundle009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle427
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle392
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle558
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.WeilTup
variable {D : D7}
theorem weilOK_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t
  have hmE : ¬ Odd D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hX := hP.bot.hyp.2.2.2.1.chain.ωX t
  simp only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX
  have hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta ∧ ResEta D (_root_.GlobalTheory.Fam.pk_z W).eta 1 := by
    intro j' h'
    have e : j' + 1 + 1 = D.R.m := by omega
    have hk := hC.kom t (j' + 1) (by omega)
    have hμH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) := by
      have h1 : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) := hk.hecS
      rw [e] at h1; exact h1
    have hμR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1) := by
      have h1 : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank := hk.resT
      have h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank := (f.c.oT (j' + 1 + 1) e).rank_add
      rw [← h2, (hτ j' h').1, e] at h1
      exact h1
    have hH : IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta := by
      have h1 := hecke_mul (hecke_inv hX.hecT) hμH
      rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    exact ⟨hH, resEta_of_diff hμR hX.resT⟩
  refine ⟨?_, ?_, hτ⟩
  · intro j σ h
    obtain ⟨hHη, hRη⟩ := hη (j + 2 * σ + 2) (by omega)
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j (σ + 1) h
    obtain ⟨-, -, fV, fW⟩ := (hR.row t).sFB j σ h
    have hL := (f.c.bes j (σ + 1) h).line.1
    have hL' := (f.c.bes (j + 1 + 1) σ (idx_step h)).line.1
    obtain ⟨omz, homz⟩ := hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omz', homz'⟩ := hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [fV]; exact hk1
    · rw [fV]; exact homz'
  · intro j h
    have e : j + 1 + 1 = D.R.m := by omega
    obtain ⟨hHη, hRη⟩ := hη j h
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j 0 h
    have hL := (f.c.bes j 0 h).line.1
    have hXH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) := by rw [e]; exact hX.hecT
    have hXR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) D.sp.X'.rank := by rw [e]; exact hX.resT
    obtain ⟨omz, homz⟩ := hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omT', homT⟩ := hE (D.sp.X (j + 1)) D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR
    obtain ⟨omz'', homz''⟩ := hE (D.sp.X (j + 1)) f.c.Lz (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1)) (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹
      hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)
    have hμ1 : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) := by
      rw [inv_inv, inv_mul_cancel_right]
    have key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
        ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e') := by
      intro n e'
      subst e'
      rw [e]
      exact hX
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1),
      (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [hμ1]; exact hk1
end GlobalTheory.Fam.WeilTup
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in

theorem GlobalTheory.Fam.chi_compat_pk_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  intro D L hT Gi Gl Kc Yd cX ex W hW k _ _ _ _ q PP hP hI π' hπ hR j hj1 hj2 μ hμ hC
  have hL := hW.bot.hyp.2.2.2.1.lev
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) =
      Formalism.IndefR.Datum.toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hUnr : UnramEverywhere D (_root_.GlobalTheory.Fam.pk_z W).eta :=
    GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta (Formalism.L2.Host.CharFrame.isEta _).unr
  have hη : (_root_.GlobalTheory.Fam.pk_z W).eta y = 1 := hUnr y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 y = (_root_.GlobalTheory.Fam.pk_z W).mu0 j y := by
    unfold Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hH1 := hL.mu0 ⟨j - 1, by omega⟩
  have hH2 := hL.chi ⟨j - 1, by omega⟩
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.CommIs
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi
end GlobalTheory.Fam.CommIs
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in
theorem GlobalTheory.Fam.commOf_is_of_geoMeas_of_coords_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (_root_.GlobalTheory.Fam.pk_z W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (_root_.GlobalTheory.Fam.pk_z W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (_root_.GlobalTheory.Fam.pk_z W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (_root_.GlobalTheory.Fam.pk_z W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n))
        (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevPin

theorem exists_levelData_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ (l : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), _root_.GlobalTheory.Fam.SymReadAlt W l S → (∀ PP, LocY (l PP) y v.N (_root_.GlobalTheory.Fam.pk_z W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, _root_.GlobalTheory.Fam.LocalGroupReading (⟨mkGeo m b, j, row, col⟩ : _root_.GlobalTheory.Fam.FamilyCharacter W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hc.std
  choose ν hν using fun PP : (_root_.GlobalTheory.Fam.pk_z W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (_root_.GlobalTheory.Fam.pk_z W).Pg
  let pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg := (Fintype.equivFin _).symm
  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT
  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩
  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i
end GlobalTheory.LevPin
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem levS_datYt_base_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) = levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  have e : Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
    refine Subgroup.ext fun x => ?_
    show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
    unfold LevCh.datYt LevCh.dat0
    rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B x]
    rfl
  unfold levS Lev.levG
  rw [e]
theorem levChi_datYt_zero_eq_dat0 (W : _root_.GlobalTheory.MiS.RealPackAlt ex) :
    Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) =
      Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) := by
  funext k
  unfold Lev.levChi LevCh.datYt LevCh.dat0
  rw [levFn_datY_noQ ((_root_.GlobalTheory.Fam.pk_z W).βY 0) Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (_root_.GlobalTheory.Fam.pk_z W).Pg
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B]
theorem initial_tuples_mem_stageY_zero_CC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ∈ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W 0).CC (_root_.GlobalTheory.BaseChain.com_z W) := by
  intro D L hT Gi Gl Kc Yd cX ex W _ T hT0
  show T ∈ MultT (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (levS (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
    (Lev.levChi (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 0 (_root_.GlobalTheory.Fam.complexLevelStructure W)))
  rw [_root_.GlobalTheory.BaseChain.levS_datYt_base_alt W, _root_.GlobalTheory.BaseChain.levChi_datYt_zero_eq_dat0 W]
  exact hT0
end GlobalTheory.BaseChain
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
variable {D : D7}
theorem stepY_thetaFun_isItW_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j hj
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have hj' : j < D.R.m := by omega
  have dS : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY j hj')
  have dT : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βY (j + 1) hj)
  have hP' := (hR.row W.P.A3.A.μ0).vP j hj
  have hY := hC.chain.vY W.P.A3.A.μ0 j hj
  have hω := hC.chain.ωY W.P.A3.A.μ0 j hj
  have hθ := hC.models.inf
  obtain ⟨vth, vne, -⟩ := GlobalTheory.InnerSteps.stepVec_vac dS dT (rank_Yc_le_succ j) hP'
  refine ⟨fun φ => GlobalTheory.FockTheta.ptStable D _ _ hP'.1.1 hθ _ _ _ _ _ _ _ φ vth, ?_⟩
  have h0 := GlobalTheory.Grid.isItW_of_mem_span hω hθ hP'.1.2.theta (GlobalTheory.Grid.stepVec_mem_span dS dT hY)
    (hC.chain.ItY W.P.A3.A.μ0 j hj)
  exact GlobalTheory.Grid.isItW_of_mem_span hω hθ vth (GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hP'.1 dS dT (GlobalTheory.Grid.stepVec_mem_span dS dT hP') vne) h0
end GlobalTheory.BaseChain
end
end
end

section

alias GlobalTheory.T.hecke_expansion_local_of_levelC :=
  GlobalTheory.HeightCounting.Fin3.hecke_expansion_datL_of_levelC
end

end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_datum_of_rank_one_gram' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  first | exact @_root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt | exact _root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt | (intros; apply _root_.GlobalTheory.Fam.WeilTup.weilOK_fam_alt <;> assumption)
end

end
end
