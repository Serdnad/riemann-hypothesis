module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle928
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle067
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
theorem mu_block_mem_alt : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa →
    (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D Rw hL j σ π μ Pa hA hR hB
  have hgood : ∀ᶠ w in Filter.cofinite, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG μ w)) ∧ ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    refine Filter.Eventually.and (Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)) ?_
    · exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
    · exact Filter.eventually_all.2 fun k => (placesOver_finite D k).compl_mem_cofinite
  obtain ⟨w0, hw0, hs0⟩ := GlobalTheory.MuBlock.exists_split_not_mem D.nd hL.an.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG μ w0)) ∧
      ∀ k : Fin 2, w0 ∉ placesOver D.host.E (D.host.g k) := by
    have h := hw0
    simp only [Set.mem_setOf_eq, not_not] at h
    exact h
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := _root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w0 hs0 hg0.2 hg0.1.1 hg0.1.2
  have hall : ∀ w, (((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG μ w)) ∧
      ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) :=
    fun w hw hs => (_root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w hs hw.2 hw.1.1 hw.1.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG μ w) →
      D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.1.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π', d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π' = D.naut.tw μ D.naut.etaTinv := by
    refine hL.one π' _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.1.2)]
  subst hν
  exact hp0
end GlobalTheory.MuBlockLoc
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper.Read
section Record
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
end Record
end GlobalTheory.ThmAUpper.Read
namespace GlobalTheory.ThmAUpper
open Read GlobalTheory.ToricDenom GlobalTheory.FunObj.SqNum in
theorem read_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit _ hF w hw i j s hs1 hs2 T₀ ψc T _ h0 _ hψ hT'
  obtain ⟨_, _, -, hb, -⟩ := hF
  obtain ⟨-, ι, hι, -, hall⟩ := hfit.1.list _ (hfit.1.setting.inW1 hw)
  refine ⟨ι, hι, fun b => ?_⟩
  have hi := i.2
  let a : Fin D.R.m := ⟨D.R.m - i - 1, by omega⟩
  have ha : a.1 + 1 = D.R.m - i := by simp only [a]; omega
  have hsN : s ≤ BlochKatoReduction.Gen.NFun D.R + 1 := by
    have h3 : halfRank D i j ≤ GlobalTheory.ChiGrid.bigN D := by
      have a : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) ≤ GlobalTheory.ChiGrid.bigN D := by
        have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
        have h2 : (i + 1) * GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ i.2
        simp only [GlobalTheory.ChiGrid.rankV, GlobalTheory.ChiGrid.bigN, Ranks.r, mul_add] at *
        omega
      have e : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) = GlobalTheory.ChiGrid.rankV D i j + D.R.t + GlobalTheory.ChiGrid.sLen D := by
        simp only [GlobalTheory.ChiGrid.rankV]; ring
      unfold halfRank; omega
    have h12 : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.ChiGrid.bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
    omega
  obtain ⟨lam, hlam, -, hth⟩ := hall j a s b hs1 hsN
  have e1 : GlobalTheory.LamTie.cond0 D.host (lamOf d.G).w0 = condF d.G.pl := cond0_eq d.G hb
  have e2 : (lamOf d.G).lam0 (D.ntw.l (ex.nch.twI w)) j a =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    rw [lambdaGrid_apply, ha, ex.nch.twI_l, nuH, xiH_base p, mul_one, div_mul_eq_mul_div]
  have e3 : GlobalTheory.LamTie.phi D.host ∘ D.eTau = cmPhi D := rfl
  have e4 : (lamOf d.G).kap j a s ∘ D.eTau = kap D 1 i j s := by
    funext τ
    simp only [Function.comp, GlobalTheory.LamTie.LamDat.kap, lamOf, kap, Formalism.L2.Host.eExp, Equiv.symm_apply_apply, ha]
    have : (GlobalTheory.ChiGrid.num D 1 τ).e (j + 1) = ⌊(D.hc τ).e j⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e (j + 1) = _
      simp [GlobalTheory.SignedHC.GridData.extend]
    rw [this]
  rw [e1, e2] at hth
  obtain ⟨u, -, hth⟩ := hth
  obtain ⟨_, π, t, hπ, ht, hδ⟩ := hth _ (hfit.1.cond w hw)
  obtain ⟨_, π0, t0, -, ht0, hδ0⟩ := hth ∅ ⟨by simp, by simp, by simp⟩
  replace ht := fun q => isClassTerm_reindex D.eTau (ht q)
  replace ht0 := fun q => isClassTerm_reindex D.eTau (ht0 q)
  rw [e3, e4] at ht ht0
  have e5 : condQ (condF d.G.pl) (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = condF d.G.pl := by
    simp [condQ, belowSet]
  have s0 := sum_th_eq ht0 hδ0 (t := T₀) (by rw [e5]; exact h0)
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb D.ntw (ex.nch.twI w) (ex.nch.k' w)
  obtain ⟨e, he, hchar⟩ := exists_pow_char hfit.1.psi hw (hp.ties.psiVal w hw) (atSide D.ntw b ι) J
  have hc : condQ (condF d.G.pl) (belowSet (ex.nch.Q w)) ≠ ⊥ :=
    mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have key : ∀ a : ℤ, J (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (ex.nch.psi' w ^ a)) =
      u * atSide D.ntw b ι (T (ψc ^ (e * a))) := fun a => by
    refine thEval_eq_twisted hJ (fun q => ?_) ht hδ (hT' _)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hchar hc π hπ y
    have h2 : ∀ (x : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ), J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ (x ^ a : _ˣ)) =
        J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ x) ^ a := fun x => by
      have := congrArg Units.val (map_zpow (Units.map (J.comp
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _)).toMonoidHom) x a)
      rw [Units.val_zpow_eq_zpow_val] at this
      exact this
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, h2, ← h1, hψ, zpow_mul, Units.val_zpow_eq_zpow_val _ a, map_zpow₀]
  refine ⟨lam, J, if b then e else -e, hlam, by cases b <;> simp [he, he.neg_left], RingHom.ext hJ, fun a => ?_⟩
  rw [hJ, s0, hlam]
  cases b
  · have : BlochKatoReduction.Gen.psiAt false (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ (-a) := by simp [BlochKatoReduction.Gen.psiAt]
    rw [this, key]
    simp only [Bool.false_eq_true, if_false, mul_neg, neg_mul]
    ring
  · have : BlochKatoReduction.Gen.psiAt true (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ a := rfl
    rw [this, key]
    simp only [if_true]
    ring
end GlobalTheory.ThmAUpper
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def datSph_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : LevDat (I.rec7 l Z).host.E ℂ (I.rec7 l Z).sp.X'.rank :=
  { datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0 with Q := ∅ }
def sphericalLevelSubgroup (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)).comap (MulAut.conj x⁻¹).toMonoidHom
def twistedLevelSubgroup (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (t : W.P.T) : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)).comap (MulAut.conj x⁻¹).toMonoidHom
theorem mem_level_sphere_iff_conj_mem_levS {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W x ↔ x⁻¹ * h * x ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := by
  simp [_root_.GlobalTheory.TopVol.sphericalLevelSubgroup, levS]
theorem mem_level_twist_iff_conj_mem_levS_datXP {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} {t : W.P.T} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ _root_.GlobalTheory.TopVol.twistedLevelSubgroup W x t ↔ x⁻¹ * h * x ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) := by
  simp [_root_.GlobalTheory.TopVol.twistedLevelSubgroup, levS]
end GlobalTheory.TopVol
end
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.ShareOn.WhitBase
section SlopeTestRemainingChoices
open Formalism.L2.DIV
variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}
end SlopeTestRemainingChoices
section Comparison₂
open Formalism.L2.DIV Formalism.BasicNotions
variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
end Comparison₂
end GlobalTheory.ShareOn.WhitBase
namespace GlobalTheory.ShareOn
open GlobalTheory.ShareOn.WhitBase
open Formalism.L2.DIV in
theorem isWhit_and_eq_embLL_inv_and_halfUnip : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hR
  obtain ⟨Pg, pl, res, ψ', eC, hL, -⟩ := hR.psi
  rw [p.eGtie] at hL
  unfold HalfUnip
  generalize p.R.eG.trans p.cG = e at hL ⊢
  let ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    D.what₂.embLL.toMonoidHom.compAddChar
      ((ψ' (pl kv).1).compAddMonoidHom ((res kv).symm.toAddMonoidHom.comp (-AddMonoidHom.id _)))
  have hψ : ∀ kv c, ψ kv c = D.what₂.embLL (ψ' (pl kv).1 ((res kv).symm (-c))) := fun _ _ => rfl
  let iso := p.P.P0.equivMapOfInjective e.toMonoidHom e.injective
  have hiso : ∀ g0 : p.P.P0, ((iso g0 : p.P.P0.map e.toMonoidHom) : G0g D.nd) = e g0 := fun _ => rfl
  let lam : (p.P.P0.map e.toMonoidHom) →* ℂˣ :=
    (Units.map D.what₂.embLL.toMonoidHom).comp (p.P.ψ0⁻¹.comp iso.symm.toMonoidHom)
  have hlam : ∀ g, ((lam g : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0 (iso.symm g) : D.what₂.LLˣ) : D.what₂.LL)⁻¹ := by
    intro g
    show D.what₂.embLL (((p.P.ψ0 (iso.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = _
    rw [Units.val_inv_eq_inv_val]
  refine ⟨lam, ψ, ⟨?_, ?_, ?_⟩, ?_, ⟨0, ?_⟩⟩
  · intro kv h1
    apply hL.gen (pl kv).1 (pl kv).2
    ext x
    have h2 : ψ kv (-(res kv x)) = 1 := by rw [h1, AddChar.one_apply]
    rw [hψ, neg_neg, RingEquiv.symm_apply_apply] at h2
    rw [AddChar.one_apply]
    apply D.what₂.embLL.injective
    rw [h2, map_one]
  · intro g
    rw [Subgroup.mem_map_equiv, mem_iff_of_lvlTie hL]
    simp only [MulEquiv.apply_symm_apply]
  · intro g
    have hg0 : e (iso.symm g) = (g : G0g D.nd) := by rw [← hiso, MulEquiv.apply_symm_apply]
    have hg : eC (iso.symm g) ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ').H := (hL.p0 _).1 (iso.symm g).2
    rw [hlam, chi_of_lvlTie hL _ hg, ← Finset.prod_inv_distrib, map_prod]
    rw [← Fintype.prod_equiv pl (fun kv => D.what₂.embLL (ψ' (pl kv).1 (edgeSum supEdge (eC (iso.symm g) (pl kv))))⁻¹)
      _ (fun _ => rfl)]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← hg0, hL.comp _ kv]
    simp only [entN_map]

    rw [← map_sum, ← edgeSum_supEdge_eq, hψ, ← map_neg, RingEquiv.symm_apply_apply, AddChar.map_neg_eq_inv]
  · intro g h
    have : iso.symm ⟨_, h⟩ = g := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hlam, this, ← Units.val_inv_eq_inv_val]
    rfl
  · intro g hg v
    exact (mem_iff_of_lvlTie hL g).1 hg ⟨0, v⟩
end GlobalTheory.ShareOn
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem two_log_card_levels_le_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ PP A hN
  have hq : ∀ k, D.host.g k ≠ 0 := by
    intro k h0
    have h := hN.cop
    fin_cases k <;> simp_all [Nat.Coprime]
  have hcard : Nat.card p.P.Gp =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [Nat.card_congr (p.R.eG.trans p.cG).toEquiv]
    exact Nat.card_pi
  have hleN : Fintype.card p.P.Gp ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), D.host.g kv.1 ^ (D.R.r * D.R.r) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun kv _ => card_GL_zmod_le _ _ (hq kv.1))
  have hpos : (0 : ℝ) < (Fintype.card p.P.Gp : ℝ) := by exact_mod_cast Fintype.card_pos
  have hleR : (Fintype.card p.P.Gp : ℝ) ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r)) := by
    exact_mod_cast hleN
  have hlog : Real.log (Fintype.card p.P.Gp : ℝ) ≤
      (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
    refine (Real.log_le_log hpos hleR).trans ?_
    rw [Real.log_prod (fun kv _ => pow_ne_zero _ (by exact_mod_cast hq kv.1))]
    calc ∑ kv : (Σ k : Fin 2, D.nd.PlG k), Real.log ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r))
        ≤ ∑ _kv : (Σ k : Fin 2, D.nd.PlG k), ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          refine Finset.sum_le_sum fun kv _ => ?_
          rw [Real.log_pow]
          push_cast
          exact mul_le_mul_of_nonneg_left (hN.logg kv.1) (by positivity)
      _ = (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
          simp [D.nd.card_PlG, nsmul_eq_mul]
          ring
  obtain ⟨-, hL10, hLx, -⟩ := hN.big
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  obtain ⟨-, -, hpoly⟩ := hN.poly
  have hroom := hN.room
  have hx0 : 0 < L.sc.x := by linarith
  have hX0 : 0 < L.sc.x ^ A := Real.rpow_pos_of_pos hx0 A
  have h3 : (L.sc.x ^ A) ^ (3 : ℝ) = (L.sc.x ^ A) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at hroom
  have hrn : (D.R.r : ℝ) ≤ D.R.nV := by
    have : D.R.r ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    exact_mod_cast this
  set X := L.sc.x ^ A with hX
  set f : ℝ := (D.R.f : ℝ)
  set r : ℝ := (D.R.r : ℝ)
  set Lr := L.sc.L
  have hr0 : 0 ≤ r := by positivity
  have hY : f * r * r * Lr ≤ X := by
    refine le_trans ?_ hpoly
    have : f * r * r * Lr = (f * r) * Lr * r := by ring
    have : f * r * (D.R.nV : ℝ) * Lr = (f * r) * Lr * D.R.nV := by ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ f) hr0) (by linarith : (0:ℝ) ≤ Lr)]
  have key : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ L.sc.b := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h1
    · have : r = 0 := by simp [r, h0]
      rw [this]; nlinarith [pow_pos hX0 3]
    · have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr h1
      have hY80 : 80 ≤ f * r * r * Lr := by
        have : (1:ℝ) ≤ r * r := by nlinarith
        have : (80:ℝ) ≤ f * Lr := by nlinarith
        nlinarith
      have hX80 : 80 ≤ X := le_trans hY80 hY
      have hA : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ 40 * (f * r * r * Lr) := by
        have : 0 ≤ f * r * r := by positivity
        nlinarith
      have hB : 40 * X ≤ X ^ 3 := by
        have hXX : 40 ≤ X * X := by nlinarith
        calc 40 * X ≤ X * X * X := by nlinarith
          _ = X ^ 3 := by ring
      nlinarith
  nlinarith [hlog]
end GlobalTheory.CovTop
end
end
end

section



section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem norm_sq_blockValue_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h
end GlobalTheory.FrameAut
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix

theorem theta_eV0_eq_iC_Pq_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h
end GlobalTheory.BigTop.Fun
end
end
end
