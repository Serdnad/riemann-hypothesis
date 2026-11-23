module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle078
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem stepY_weil_vec_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hC := hW.bot.hyp.2.2.2.1
  have hQ : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun PP => _root_.GlobalTheory.MiTop.not_mem_Q_base' W PP
  refine ⟨hC.chain.ωY W.P.A3.A.μ0 j hj, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, (_root_.GlobalTheory.Fam.pk_z W).vac j, ?_⟩
  have h := (hf.row W.P.A3.A.μ0).vP j hj
  rw [hQ] at h
  exact h
end GlobalTheory.BaseChain
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem stepX_weil_vec_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1 + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1 + 1)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1 + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hm : j + 1 + 1 = D.R.m := by omega
  have hC := hP.bot.hyp.2.2.2.1
  have hQ : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    exact _root_.GlobalTheory.MiTop.not_mem_Q_base' W PP
  refine ⟨?_, ?_⟩
  · have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
      rintro n rfl
      exact hC.chain.ωX W.P.A3.A.μ0
    have := key _ (idx_top h)
    simp only [_root_.GlobalTheory.BaseChain.com_z, _root_.GlobalTheory.BaseChain.stageOfSpaceY, _root_.GlobalTheory.BaseChain.stageOfSpaceX, _root_.GlobalTheory.BaseChain.transitionToSpaceX, GlobalTheory.ChainOnto.Com.chS, GlobalTheory.ChainOnto.Com.chT]
    rw [hm]
    exact this
  · refine ⟨(_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, vacT (_root_.GlobalTheory.Fam.pk_z W) j h, ?_⟩
    have hv := (hf.row W.P.A3.A.μ0).vT j h
    rw [hQ] at hv
    simp only [_root_.GlobalTheory.BaseChain.com_z, _root_.GlobalTheory.BaseChain.stageOfSpaceY, _root_.GlobalTheory.BaseChain.stageOfSpaceX, _root_.GlobalTheory.BaseChain.transitionToSpaceX]
    rw [hm]
    exact hv
end GlobalTheory.BaseChain
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LevelPlaces
end GlobalTheory.LevelPlaces
namespace GlobalTheory.LevelPlaces
theorem split_unit_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hpk hTy PP hPP
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hTy.1 PP hPP
  rw [Nat.cast_mul] at hg
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rw [map_natCast]; exact hk
  obtain ⟨i, hi⟩ := ((GlobalTheory.PlacesOverG.places_over_g_k D k).2.1 PP).1 hk
  have key : ∀ {v v' : HeightOneSpectrum (𝓞 D.host.F)}, v = v' → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v') := by
    rintro v _ rfl h; exact h
  have hτ : Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
    rcases i with w | w
    · have hi' : D.naut.plGw k w = PP := hi
      exact key (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi')
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
    · have hi' : GlobalTheory.IdemSupport.cP (D.naut.plGw k w) = PP := hi
      exact key ((GlobalTheory.IdemSupport.under_cP _).symm.trans (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi'))
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
  obtain ⟨τ⟩ := hτ
  have he := GlobalTheory.AdelicU.Supp.splitAt_splitIdemAd (D := D) τ
  have hε := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have hs := he.2.2.trans (GlobalTheory.AdelicU.Supp.pl_eq D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))
  have hsplit : IsSplitIdem D (GlobalTheory.AdelicU.Supp.splitIdemAd _ τ) := ⟨he.1, he.2.1, _, _, hε, hs⟩
  obtain ⟨p, -, hpv⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D _ _ _ hsplit hε hs
  have hne : ∀ m ∈ D.host.condN.primeFactors, D.host.g k ≠ m := fun m hm e => by
    have := GlobalTheory.RamValCheck.g_coprime D k m hm
    rw [e, Nat.coprime_self] at this
    exact hgp.one_lt.ne' (e ▸ this)
  have hc : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hgp).2 fun ⟨m, hm⟩ => ?_)
    refine hpk.aa PP (Or.inr (Or.inl hPP)) ?_
    rw [hm, Nat.cast_mul]
    exact PP.asIdeal.mul_mem_right _ hk
  have hu := GlobalTheory.FinPl.UnitAt.unitAA_of_prime p hgp (by rw [hpv]; exact hv) (UpperTheory.Ram.g_notMem_small D k)
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.q_prime, D.host.q_dvd_condN, D.host.condN_ne_zero⟩))
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.d_prime, D.host.d_dvd_condN, D.host.condN_ne_zero⟩)) hc
  unfold GlobalTheory.FinPl.SplitPt.UnitAA at hu
  rw [hpv] at hu
  exact ⟨⟨_, _, hsplit, hε, hs⟩, hu.1, hu.2⟩
end GlobalTheory.LevelPlaces
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TupChars
section Loc
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
section Pack
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex}
theorem under_ne_alt (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (t : W.P.T) {PP P' : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hQ : P' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) :
    P'.under (𝓞 D.host.F) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
  intro heq
  have hL := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P' hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := (_root_.GlobalTheory.Fam.pk_z W).C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = (_root_.GlobalTheory.Fam.pk_z W).C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hmemF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    simpa using hmemE
  rw [← heq] at hmemF
  have hmemE' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P'.asIdeal := hmemF
    simpa using h2
  haveI : Finite (kP P') := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : P'.asIdeal.IsPrime := P'.isPrime
  haveI : Nontrivial (kP P') := inferInstance
  haveI : Fintype (kP P') := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP P') = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := P'.asIdeal)).2 hmemE'
    simpa using this
  have h0q : ((q : ℕ) : kP P') = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP P')
  have hd1 : ringChar (kP P') ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP P') ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP P') = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1
theorem charUnramAt_xi_under (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (t : W.P.T) {PP : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
  by_contra hu
  rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
  · exact _root_.GlobalTheory.TupChars.under_ne_alt hP t hPg h hw
  · exact _root_.GlobalTheory.TupChars.under_ne_alt hP t hPg hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
theorem charUnramAt_eta (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (_root_.GlobalTheory.Fam.pk_z W).eta v := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  exact GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr w)
end Pack
theorem gLoc_chars_of_gRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (n : ℕ) (G : Fin n → GLoc v) pl, _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, (G i).Chars (f.t t) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR _ t n G pl hG i
  have hq : (G i).q.v = (pl i).1.under (𝓞 D.host.F) := (hG.idem i).2
  have hxi : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) (G i).q.v := hq ▸ _root_.GlobalTheory.TupChars.charUnramAt_xi_under hP t (pl i).2
  have heta : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (_root_.GlobalTheory.Fam.pk_z W).eta (G i).q.v := _root_.GlobalTheory.TupChars.charUnramAt_eta hP _
  let M : ℕ → (AE D)ˣ →* Circle := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t
  let μ : ℕ → (G i).kˣ →* ℂˣ := fun m =>
    if 1 ≤ m ∧ m ≤ D.R.m then cmp (G i).q ((Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1⁻¹) else (G i).S.μ m
  have hμ : ∀ m, 1 ≤ m → m ≤ D.R.m → μ m = cmp (G i).q ((Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1⁻¹) :=
    fun m h1 h2 => if_pos ⟨h1, h2⟩
  have hunit : ∀ m (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ m x = (G i).S.μ m x := by
    intro m x hx
    by_cases hm : 1 ≤ m ∧ m ≤ D.R.m
    · rw [hμ m hm.1 hm.2]
      apply Units.ext
      rw [cmp_apply, hG.mu i m hm.1 hm.2 x (GlobalTheory.LocChar.unitsHom (ofSplit (G i).q) x) rfl]
      have hx1 := unit_trivial (G i).q hxi x hx
      have e : (Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1 = (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta m).1 * (_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t := by
        simp only [Lift.chrStep, M, LevCh.mu, Lift.tup]
        split_ifs
        · exact mul_right_comm _ _ _
        · rfl
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, e, MonoidHom.mul_apply, hx1, mul_one]
    · simp only [μ, if_neg hm]
  have htame : ∀ m, GlobalTheory.SplitWeil.IsTame (μ m) := by
    intro m x hx
    rw [hunit m x (val_eq_one_of_sub x hx)]
    exact (G i).S.tame m x hx
  have hm2 : Even D.R.m := D.R.m_even
  refine ⟨μ, htame, hunit, fun j ρ h => ?_, fun j σ h => ?_⟩
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sBF j ρ h
    have hV' : ((f.t t).sBF j ρ h).χV = M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := hV
    have hW' : ((f.t t).sBF j ρ h).χW = M (j + 1) := hW
    have hodd : Odd (j + 1) := by
      obtain ⟨r, hr⟩ := hm2
      exact ⟨j / 2, by omega⟩
    have hμj : μ (j + 1) = cmp (G i).q ((M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)⁻¹) := by
      rw [hμ (j + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_pos hodd]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1)), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1) * (M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).eta := by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, unit_trivial (G i).q heta x hx, Circle.coe_one]
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sFB j σ h
    have hV' : ((f.t t).sFB j σ h).χV = M (j + 1 + 1) := hV
    have hW' : ((f.t t).sFB j σ h).χW = M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := hW
    have heven : ¬ Odd (j + 1 + 1) := by
      obtain ⟨r, hr⟩ := hm2
      rw [Nat.not_odd_iff_even]
      exact ⟨j / 2 + 1, by omega⟩
    have hμj : μ (j + 1 + 1) = cmp (G i).q (M (j + 1 + 1))⁻¹ := by
      rw [hμ (j + 1 + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_neg heven]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ * (M (j + 1 + 1))⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := by
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    rw [e, MonoidHom.inv_apply, unit_trivial (G i).q heta x hx, inv_one, Circle.coe_one]
end GlobalTheory.TupChars
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MuUnrOff
theorem mu_charUnramAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (t : W.P.T) (n : ℕ) (x : HeightOneSpectrum (𝓞 D.host.F)), 1 ≤ n → n ≤ D.R.m → (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ x) → (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t n) x := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t n x h1 h2 hPg hQ
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : j < D.R.m := by omega
  show GlobalTheory.LFun.UnrAt ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu0 (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) w
  refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨j, hj⟩) w).2 (((_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.P k w hk with h | ⟨w', h, hc⟩
    · exact hPg w ((hL.Pg w).2 ⟨k, h⟩) hw
    · refine hPg w' ((hL.Pg w').2 ⟨k, h⟩) (Eq.trans ?_ hw)
      ext a
      show algebraMap _ _ a ∈ w'.asIdeal ↔ algebraMap _ _ a ∈ w.asIdeal
      rw [hc, Formalism.L2.Col.mem_conjIdeal]
      have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap _ _ a := by
        apply RingOfIntegers.ext
        exact (D.sp.cm.fixed _).2 ⟨a, rfl⟩
      rw [this]
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hu
    rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
    · exact hQ w h hw
    · exact hQ P' hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
end GlobalTheory.MuUnrOff
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PkPlaces
theorem pk_places_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) ∧ (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) ∧ (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hQQ : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' :=
    fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'
  have hnc : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' := by
    intro t PP h PP' h' hc
    have ha := (GlobalTheory.StepLifts.places_apart _ hl t).1
    rcases Finset.mem_union.1 h with h | h
    · exact ha PP h PP' (Finset.mem_union.1 h') hc
    · rcases Finset.mem_union.1 h' with h' | h'
      · refine ha PP' h' PP (Or.inr h) ?_
        rw [GlobalTheory.GoodPrimes.isConjPl_iff] at hc ⊢
        rw [hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
      · exact hQQ t PP h PP' h' hc
  refine ⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩
  · rw [Finset.union_empty]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' =>
      (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')
    · exact (GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')
  · exact GlobalTheory.CentralShift.exists_idemSum _ (hnc t)
  · rw [Finset.empty_union]
    exact GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)
end GlobalTheory.PkPlaces
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.PlaceInj
theorem under_injective_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → Function.Injective (fun i : {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
  simp only at h
  apply Subtype.ext
  show P = P'
  have key : ∀ A B : Formalism.L2.DIV.Pl D.host.E, A ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → (B ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W B) →
      A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → A = B := by
    intro A B hA hB hAB
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hAB.symm with e | e
    · exact e.symm
    · exfalso
      have hc : Formalism.IndefR.Lev.IsConjPl A B := GlobalTheory.GoodPrimes.isConjPl_iff.2 e
      rcases hB with hB | ⟨t, hB⟩
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev W.P.A3.A.μ0).1 A hA B (Or.inl hB) hc
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev t).1 A hA B (Or.inr hB) hc
  rcases hP with hP | hP
  · exact key P P' hP hP' h
  · rcases hP' with hP' | hP'
    · exact (key P' P hP' (Or.inr hP) h.symm).symm
    · exact hW.sel P P' hP hP' h
end GlobalTheory.Fam.PlaceInj
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
def Mv.autSpec_alt {big} {L : LocAll (lay0 D)} {Sp : NdSpec A.pl M C big L.X L.T} (x : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation (m.sideA_alt A) (m.mt M) (m.tp tp).tup (m.ndSpec_alt Sp).iq (m.loc L).Y (m.loc L).C := @_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (iotaQ := (by with_unfolding_all exact (x.iotaQ :)))
    (iotaQC := (by with_unfolding_all exact (x.iotaQC :)))
    (kFbar := (by with_unfolding_all exact (x.kFbar :)))
    (locW := (by with_unfolding_all exact (x.locW :)))
    (satW := (by with_unfolding_all exact (x.satW :)))
    (wdOf := (by with_unfolding_all exact (x.wdOf :)))
    (muC := (by with_unfolding_all exact (x.muC :)))
    (S := (by with_unfolding_all exact (x.S :)))
    (irr := (by with_unfolding_all exact (x.irr :)))
    (inj := (by with_unfolding_all exact (x.inj :)))
    (surj := (by with_unfolding_all exact (x.surj :)))
    (typeV := (by with_unfolding_all exact (x.typeV :)))
    (ptV := (by with_unfolding_all exact (x.ptV :)))
    (emb := (by with_unfolding_all exact (x.emb :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.emtTheta_of_yRel
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
    {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}
    (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x)
    {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) :
    YRel L Y → EMtTheta Y
      (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
      (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  _root_.GlobalTheory.HeightCounting.Fin3.emtTheta_L_alt L l Y
end
end
