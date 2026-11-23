module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle654
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle655
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle622
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle565
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle624
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem std_eq_colLat_one' {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem vac_jet_ne_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hX : IsBottomTri W i j X) :
    ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac
      (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one' X.rA.Λ hX.std.2.1, ← std_eq_colLat_one' X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank (even_bot' hX)
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D he0.1.1 he0ne
  refine ⟨α, ?_⟩
  change pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial α 1) 0 ≠ 0
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac hψ hθ α 0, map_ne_zero,
    ← hBA, ← hBW, hc α, GlobalTheory.FockPos.applyAt0_monomial']
  have hprod : (α.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  exact mul_ne_zero c.ne_zero (mul_ne_zero hprod (mul_ne_zero hfac hα))

end GlobalTheory.MovedJetNZ

end

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

end GlobalTheory.MovedJetNZ
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.AscBottom

variable {D : D7}

theorem rapidDec_star {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun γ hγ g => by simp [Pi.star_apply, h1 γ hγ g], h2.star, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  exact ⟨C, fun g => by simpa [Pi.star_apply, norm_star] using hC g⟩

theorem rung0 (hF : FockTot) : Rung0 := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h
  have hm : 0 < D.R.m := by omega
  obtain ⟨hom, homC, -, hev, hdep, hdn, hpart, -, -, -⟩ := GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hq T L μ0 hL sc G W M hM 0 hm
  obtain ⟨hchT, hchS⟩ := hev ⟨0, rfl⟩
  obtain ⟨hrap, hch⟩ := hΨ
  obtain ⟨f, hf, hΨ0⟩ := hch 0 hm
  have hhf := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vT : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hhf.1, hhf.2⟩
  let ρ₀ : G.RealVec := fun _ => 0
  let Φ₀ : G.Datum := fun _ => default
  have hu' : RapidDec (Yc D 0) (star u) := rapidDec_star (hu ρ₀ Φ₀ 0 (Nat.zero_le _))
  have hφ : RapidDec (G.V (.core 1)) (star (Ψ 1)) := rapidDec_star (hrap 1 (by omega))

  set a := G.ch.chi (D.R.m - 0) with ha
  have homR : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta) (omRow W 0) := by
    have := hom
    rwa [hchS, hchT] at this
  have homX : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta * L.eta⁻¹) (omCore W 0) := by
    rw [mul_inv_cancel_right]; exact homC
  have hHeta : IsHeckeChar D L.eta := by
    have := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homR.hecS) homR.hecT
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hReta : ResEta D L.eta (negSp F.Lz).rank := by
    have h1 := Formalism.L2.Theta.resEta_mul (Formalism.L2.Theta.resEta_inv homC.resT) homR.resT
    rw [inv_inv, mul_inv_cancel_left] at h1
    refine Formalism.L2.Theta.resEta_parity h1 ?_
    have hr : (G.V (.grid 0 0)).rank + 1 = (G.V (.core 0)).rank := by
      have := F.oz.rank_add; rw [F.rk] at this; exact this
    show _ = F.Lz.rank % 2
    rw [F.rk]
    omega
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.core 1)) (negSp F.Lz) W.ψ a⁻¹⁻¹ L.eta W.ψ_std
    (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homX.hecS) hHeta (Formalism.L2.Theta.resEta_inv homX.resS) hReta

  have hΞ : VacG W.ψ _ _ (latCore G 0) (star f) := (hdep f).1 hf
  have hlift : liftT (omCore W 0) (v 1).μ (v 1).𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := by
    rw [hΨ0]; exact (hdn v f (Ψ 1)).symm
  have hint : (∫ x in vT.𝓕, liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) (F.oz.emb (x, 1)) *
      star u x ∂vT.μ) ≠ 0 := by
    have e : (fun x : GA D (Yc D 0) => liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f)
        (F.oz.emb (x, 1)) * star u x) = fun x => (starRingEnd ℂ) (Ψ 0 (stabilizerEmbedding G.sp.dec0 x) * u x) := by
      funext x
      have hl : liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := hlift
      rw [hl, hE.bot x, map_mul]; rfl
    rw [e, integral_conj]
    intro h0
    apply hper
    have := congrArg (starRingEnd ℂ) h0
    rw [Complex.conj_conj, map_zero] at this
    exact this
  obtain ⟨Φ', Φz, hΦ', hΦz, hne⟩ := GlobalTheory.T.lastSeesaw_periodNonvanishing D W.ψ (F.jac v 0 h) (G.V (.core 0)) (Yc D 0) F.Lz F.oz (latRow G 0) (ΓL 0)
    (latCore G 0) F.rk (hG.last h) (F.ζ 0) a⁻¹ (a⁻¹ * L.eta) L.eta (omRow W 0) (omCore W 0) omz homR homX homz vT
    (star (Ψ 1)) (star u) hφ hu' (star f) hΞ hint

  let ℓ : (WO (G.V (.grid 1 0)) (G.V (.grid 0 0)) → ℂ) → ℂ := fun Φ =>
    (F.jac v 0 h).per W.ψ (F.ζ 0) omz (star (Ψ 1)) (liftS (omRow W 0) vT.μ vT.𝓕 (star u) Φ) Φz
  have hT : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ (Yc D 0) vT (star u) hu').2 0 (F.jac v 0 h) a⁻¹ (a⁻¹ * L.eta) (omRow W 0) homR (negSp F.Lz)
      (F.ζ 0) a⁻¹⁻¹ L.eta omz homz (star (Ψ 1)) Φz hφ hΦz.1
  have hK : ∃ κ P, ℓ (star (W.fock (.chi 0 0) (W.cosVec 0 κ) P)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hne (hF D hq T L μ0 hL sc G W M hM ⟨0, hm⟩ ℓ hT hno Φ' hΦ')
  obtain ⟨κ, P, hκP⟩ := hK
  let ρ : G.RealVec := Function.update ρ₀ ⟨0, hm⟩ P
  let Φ : G.Datum := Function.update Φ₀ ⟨0, hm⟩ κ
  refine ⟨a⁻¹⁻¹, omz, homz, ρ, Φ, Φz, hΦz, ?_⟩
  have hp := hpart ρ Φ u
  have hd : W.datum ρ Φ ⟨0, hm⟩ = W.fock (.chi 0 0) (W.cosVec 0 κ) P := by
    show W.fock (.chi 0 0) (W.cosVec 0 (Φ ⟨0, hm⟩)) (ρ ⟨0, hm⟩) = _
    simp only [ρ, Φ, Function.update_self]
  rw [hd] at hp
  change ℓ _ ≠ 0 at hκP
  convert hκP using 2
  exact hp

end GlobalTheory.AscBottom
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem lift_level_datum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime D Pg Q e hPg h2 he
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₀, Λ', hmov, hM⟩ := GlobalTheory.T.exists_finite_unitary_mover_standard_lattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a ha
  obtain ⟨Lv, h𝔪, hw, hJ, hD2⟩ := GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ ha hmov hgen hI1 hI2 hI3 hI4
  obtain ⟨m1, hm1, hm1'⟩ := GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨m2, hm2, hm2'⟩ := GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hfin := GlobalTheory.T.finite_levelDatumClasses D S T C Lv
  refine ⟨Lv, k₀, Λ', liftL S T βS βT Pg Q e, hw, ?_, hJ, hmov.1, hM, hfin, fun x hx => hx.1,
    ⟨m1, hm1, hm1'⟩, ⟨m2, hm2, hm2'⟩,
    fun u hu => ⟨GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu, fun t ht => GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu t ht, GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu⟩,
    GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪, GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 hfin hD2⟩
  intro PP hPP
  rw [h𝔪]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hPP))

end GlobalTheory.LiftLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.StdFrames

namespace GlobalTheory.TopLevelInv

section ColCoord




variable {D : D7}

theorem map_mt_cpt_colCoord (w : Pl D.host.E) (V : HSp D) (g : GA D V) :
    Matrix.map (Formalism.L2.Theta.mt V g) ((cpt w).comp (toEAf D)) = (loc w (Lev.finE V g)).val := rfl

theorem frAt_actO_colCoord (w : Pl D.host.E) {S T : HSp D} (β' : GL (Fin T.rank) (Lev.EAf D))
    (β : GL (Fin S.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    GlobalTheory.FunObj.frAt w β' β (actO S T g h x) =
      (loc w (β'⁻¹ * Lev.finE T h * β')).val * GlobalTheory.FunObj.frAt w β' β x *
        (loc w (β⁻¹ * Lev.finE S g * β))⁻¹.val := by
  have e0 : ∀ y : WO S T, GlobalTheory.FunObj.frAt w β' β y =
      (loc w β'⁻¹).val * Matrix.map y ((cpt w).comp (toEAf D)) * (loc w β).val := by
    intro y
    rw [GlobalTheory.FunObj.frAt, GlobalTheory.FunObj.Comparison₂.fr, Matrix.map_mul, Matrix.map_mul]
    rfl
  have e1 : Matrix.map (actO S T g h x) ((cpt w).comp (toEAf D)) =
      (loc w (Lev.finE T h)).val * Matrix.map x ((cpt w).comp (toEAf D)) * (loc w (Lev.finE S g))⁻¹.val := by
    rw [actO, Matrix.map_mul, Matrix.map_mul, map_mt_cpt_colCoord, map_mt_cpt_colCoord, map_inv, map_inv]
  rw [e0, e0, e1]
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hA : ∀ {c : Type} [Fintype c] (Y : Matrix (Fin T.rank) c (Kw w)), (loc w β').val * ((loc w β')⁻¹.val * Y) = Y := by
    intro c _ Y; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hB : (loc w β).val * ((loc w β)⁻¹.val * ((loc w (Lev.finE S g))⁻¹.val * (loc w β).val)) =
      (loc w (Lev.finE S g))⁻¹.val * (loc w β).val := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [hA, hB]

theorem loc_finE_u_colCoord {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {X : Node} (hX : DefNode D.R.m X) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : loc w (Lev.finE (G.V X) (S.N.u X).1) = 1 := by
  classical
  obtain ⟨P', a, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, hoff⟩ := S.N.u_supp X hX
  have hnot : ¬ Off S.N.S w := by
    intro h0
    have h3 := S.N.off w h0
    rcases Finset.mem_union.1 hw with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact h3.1 ((G.pl.under_w hv).symm ▸ hv)
    · exact h3.2.1 t ht w h rfl
  obtain ⟨q, hq, hqw⟩ : ∃ q ∈ S.N.S, ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    unfold Off at hnot; push_neg at hnot; exact hnot
  have hz : cpt w (toEAf D ((∑ PP ∈ P', es PP) + cA D (∑ PP ∈ P', es PP))) = 0 := by
    have hA : ∀ PP ∈ P', cpt w (toEAf D (es PP)) = 0 := fun PP hPP =>
      (cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq (e ▸ hqw)
    have hB : ∀ PP ∈ P', cpt w (sg D (toEAf D (es PP))) = 0 := by
      intro PP hPP
      refine cpt_sg_eq_zero ((cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq ?_)
      rw [← e]; exact (natCast_mem_cP w q).2 hqw

    simp only [map_add (f := _), toEAf_cA, map_sum]
    rw [Finset.sum_eq_zero hA, Finset.sum_eq_zero hB, add_zero]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun z => cpt w (toEAf D z)) (hsupp i j)
  simp only [map_mul, hz, zero_mul] at h1
  have h2 : cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = cpt w (toEAf D ((1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (AE D)) i j)) := by
    have := h1.symm
    rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero] at this
    exact this
  change cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (Kw w)) i j
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem submatrix_cast_mul_colCoord {K : Type} [CommRing K] {r n n' p r' p' : ℕ} (M : Matrix (Fin r) (Fin n) K)
    (N : Matrix (Fin n) (Fin p) K) (f : Fin r' → Fin r) (h : n' = n) (g : Fin p' → Fin p) :
    M.submatrix f (Fin.cast h) * N.submatrix (Fin.cast h) g = (M * N).submatrix f g :=
  Matrix.submatrix_mul_equiv M N f (finCongr h) g

end ColCoord

end GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem conj_inv_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : (b⁻¹ * f⁻¹ * b)⁻¹ = b⁻¹ * f * b := by group

theorem conj_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : b⁻¹ * f⁻¹ * b = (b⁻¹ * f * b)⁻¹ := by group




theorem colAt_movedPt_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  intro D T L sc G W U S t ht j hj k w hw x
  have hu := loc_finE_u_colCoord S ht (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) hw
  set k' : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hk'def
  have hk : ∀ β : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D),
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k' : GA D (G.V (.top (j + 1)))) * β) =
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * β) := by
    intro β
    simp only [hk'def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu, inv_one, one_mul, mul_one]
  have hκ : (kapAt S t j hj k w).val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1))).val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := rfl
  have hκi : (kapAt S t j hj k w)⁻¹.val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1)))⁻¹.val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
    have h0 : (kapAt S t j hj k w)⁻¹.val =
        (loc w ((S.βp (j + 1))⁻¹ * (Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))))⁻¹ *
          S.βp (j + 1))).val.submatrix (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
      rw [kapAt, ← map_inv]; rfl
    rw [h0, conj_inv_colCoord, map_inv]
  funext i
  rcases eq_or_ne i (j + 1) with rfl | h1
  · rw [colAt_eq S t w _ hj]
    simp only [movedPt, Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove, Function.update_self]
    rw [colAt_eq S t w x hj, hκ, inv_one, map_one, mul_one, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      map_inv (Lev.finE (G.V (.top (j + 1)))), ← map_inv (loc w), conj_inv_inv_colCoord, hk, submatrix_cast_mul_colCoord]
  rcases eq_or_ne i j with rfl | h2
  · rw [colAt_eq S t w _ (show i < D.R.m by omega)]
    rw [movedPt, Function.update_of_ne (show (⟨i, by omega⟩ : Fin D.R.m) ≠ ⟨i + 1, hj⟩ by simp [Fin.ext_iff]),
      Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_self, colAt_eq S t w x (show i < D.R.m by omega), hκi, inv_one,
      map_one, mul_one, inv_mul_cancel, map_one, inv_one, Units.val_one, Matrix.mul_one,
      map_inv (Lev.finE (G.V (.top (i + 1)))), conj_inv_colCoord, map_inv (loc w), hk, submatrix_cast_mul_colCoord]
  by_cases hi : i < D.R.m
  · have hm : movedPt t j hj k' x ⟨i, hi⟩ = x ⟨i, hi⟩ := by
      rw [movedPt, Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ by simp [Fin.ext_iff, h1]),
        Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ by simp [Fin.ext_iff, h2])]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, colAt_eq S t w _ hi, colAt_eq S t w x hi, hm]
  · simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.colAt, dif_neg hi]

end GlobalTheory.TopLevelInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes : ∀ (D : D7) (θ : InfFam D) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ), IsInfFam θ →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod) := by
  first | exact @GlobalTheory.KapXLineDec.line_dec | exact GlobalTheory.KapXLineDec.line_dec | (intros; apply GlobalTheory.KapXLineDec.line_dec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  first | exact @GlobalTheory.SquareDict.ExactBig.kerBig_eq | exact GlobalTheory.SquareDict.ExactBig.kerBig_eq | (intros; apply GlobalTheory.SquareDict.ExactBig.kerBig_eq <;> assumption)
end
