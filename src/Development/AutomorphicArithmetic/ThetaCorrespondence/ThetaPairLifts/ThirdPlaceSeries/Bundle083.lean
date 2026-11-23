module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle076
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.row_inner_product_invariant_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  first | exact @_root_.GlobalTheory.CovTop.geoUnitary_tied_alt | exact _root_.GlobalTheory.CovTop.geoUnitary_tied_alt | (intros; apply _root_.GlobalTheory.CovTop.geoUnitary_tied_alt <;> assumption)
end
end

section



section
open NumberField

theorem _root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.PointConditions' → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @_root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | exact _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | (intros; apply _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt <;> assumption)
end
end

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.row_norm_has_gram_of_conditions : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m, HasGram (nrmR p.R.toRealDat i) := by
  first | exact @_root_.GlobalTheory.CovTop.GramPt.hasGram_at_alt | exact _root_.GlobalTheory.CovTop.GramPt.hasGram_at_alt | (intros; apply _root_.GlobalTheory.CovTop.GramPt.hasGram_at_alt <;> assumption)
end
end

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.row_good_lattice_ne_bot_of_conditions : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m, latGood p.R.toRealDat p.F.lv2 i ≠ ⊥ := by
  first | exact @_root_.GlobalTheory.CovTop.good_lattice_ne_bot_at_point | exact _root_.GlobalTheory.CovTop.good_lattice_ne_bot_at_point | (intros; apply _root_.GlobalTheory.CovTop.good_lattice_ne_bot_at_point <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.group_idempotent_coefficients_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  first | exact @_root_.GlobalTheory.TieIdem.tied_good_idem_alt | exact _root_.GlobalTheory.TieIdem.tied_good_idem_alt | (intros; apply _root_.GlobalTheory.TieIdem.tied_good_idem_alt <;> assumption)
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sets
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
end Sets
section Hyp
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Hyp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
namespace Fit
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} (h : Fit p w j hρ ν)
include h
end Fit
end Point
def TwistConditions (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
    (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j
section AtTw
variable {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
  (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop}
theorem TwistConditions.and (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (h' : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q') : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => Q Fm x hx i p w j ∧ Q' Fm x hx i p w j :=
  Closed.imp (Closed.and h h') fun _ _ _ H =>
    let ⟨x0, K⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and H.1 H.2
    ⟨x0, fun x hx h0 i p r m w hw j => ⟨(K x hx h0 i p r).1 m w hw j, (K x hx h0 i p r).2 m w hw j⟩⟩
theorem TwistConditions.imp (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j → Q' Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q' :=
  Closed.imp h fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m w hw j => f Fm x hx i p r m w hw j (K x hx h0 i p r m w hw j)⟩
theorem TwistConditions.of_forall (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p => f Fm x hx i p⟩⟩⟩
end AtTw
def CanonicalExists : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧
  ∃ (n : ℕ) (β : Module.Basis (Fin n) (Fm.D x i).what₂.LL (Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL)),
    LinearIndependent (FractionRing ((Fm.ex x hx i).nch.Oe w)) fun a => rd (β a)
def CanonicalProjection₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ rd : Can p w j, IsCan p rd → ∀ y,
  rd ((((R2 p).FW j).eOp fun g => (idemOf p.P.A3.A.X).coeff g) y) = eExt (Fm.D x i).nexp _ _ _ _ (rd y)
def TwAdmAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ =>
  IntegralHeckeForms.TwOK ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
                     (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) ∧
    IntegralHeckeForms.ClsQ (D := Fm.D x i) ((Fm.ex x hx i).nch.Q w) ∧ (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w)
def LowerBoundAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ => ∀ P : Pl (Fm.D x i).host.E,
  (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 * (Fm.D x i).host.pde *
    (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 ((Fm.ex x hx i).nch.twI w)
def ConditionAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good), RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
def RationalityHypothesis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j =>
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' ((Fm.ex x hx i).nch.twI w) j hV' ∧
      (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ ((Fm.ex x hx i).nch.twI w) j b →
        RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j b
theorem twist_at_statement_of_ratHypAt (h : _root_.GlobalTheory.BigOn.Exp.RationalityHypothesis) (hR : RatStep) : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp h fun Fm x hx i _ _ _ _ _ j ⟨T', _, Rl', cG', S', YS', F', κ', v₀', O', hV', h1, h2, h3⟩ ρ hρ hp hL =>
    h3 ρ hρ _ (hR _ _ _ _ _ _ T' Rl' cG' S' YS' F' κ' v₀' O' ρ hρ _ j _ hV' (h2 ρ hp) hL
      ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩ h1)
def CompatibilityRational : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀,
  IsNorm p.R p.v₀ (Z.ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧ RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def RecursiveSide : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀, RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) →
  Submodule.span ((Fm.ex x hx i).nch.Oe w) ((fun a => (1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ (Fm.D x i).nexp.th _ _ _ a) ''
      IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) = baseLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧
  Submodule.span ((Fm.ex x hx i).nch.Oe w) (incl (Fm.D x i).nexp _ _ _ ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) ''
      ⋃ a ∈ IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) = twLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def AdaptedExistence₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w _ => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ∃ ρ' : Setup (Fm.D x i).ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ'
def ConjugateBase : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → baseLat p w j hρ ν = baseLat p w j hρ' ν'
def ConjugateTwist : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → twLat p w j hρ ν = twLat p w j hρ' ν'
def TwistCharacter : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → Adapted p w ρ →
  ChrEq (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
      (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi (p.Tp.psi w) ∧
    p.R.xi (p.R.mu ((Fm.D x i).plEq w)) = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi *
      (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi
def CanonicalFits (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (w : (Fm.D x i).what₂.places.Pl)
    (j : Fin (Fm.D x i).R.m) (ρ : Setup (Fm.D x i).ntw), ρ.Good → ℂ → Can p w j → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ) (rd : Can p w j), Fit p w j hρ ν → IsCan p rd →
    Q Fm x hx i p w j ρ hρ ν rd
def BaseUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realBase p rd ≤ baseLat p w j hρ ν
def BaseLowerBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => baseLat p w j hρ ν ≤ realBase p rd
def TwistUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realTw p rd ≤ twLat p w j hρ ν
def TwistLowerBound : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => twLat p w j hρ ν ≤ realTw p rd
def InductionConditions : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalExists ∧ _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwAdmAlt ∧ _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace ∧ _root_.GlobalTheory.BigOn.Exp.CompatibilityRational ∧ _root_.GlobalTheory.BigOn.Exp.RecursiveSide ∧ _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateBase ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateTwist ∧ _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
theorem exists_exportTie_fit_at_tw (h1 : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) (h3 : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => Nonempty (ExportTie p.nexp p.v₀) ∧
    ∀ Z : ExportTie p.nexp p.v₀, ∃ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), SameBut Z.ρ ρ ∧ Fit p w j hρ ν :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 h3)) fun _ _ _ _ _ _ hm _ _ _ ⟨a1, a2, a3⟩ => ⟨hm.2.2.series, fun Z =>
    let ⟨ρ, hρ, hs, ha⟩ := a3 Z.ρ Z.good Z.pin
    have hL := levelOf_of_sameBut hm.2.2 Z.good hρ Z.pin ha.1 hs (levelOf_exportTie Z)
    let ⟨ν, hn, hr⟩ := a2 ρ hρ ha.1 hL
    ⟨ρ, hρ, ν, hs, ha, hn, ⟨hr.1, hr.2.1 _ _ _ a1.1 a1.2.1⟩, hL⟩⟩
theorem InductionConditions.exportSt (h : _root_.GlobalTheory.BigOn.Exp.InductionConditions) : _root_.GlobalTheory.BigOn.ExportedStatement := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine Closed.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.exists_exportTie_fit_at_tw h3 h4 h7) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h5 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h6 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h8 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h9
    (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h10 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h11 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h12 h13)))))))))) fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m v hv j => ?_⟩
  obtain ⟨⟨⟨Z⟩, a0⟩, ⟨rd, hc, hβ⟩, a2, a5, a6, a8, a9, a10, a11, a12, a13⟩ :=
    K x hx h0 i p r m ((Fm.D x i).plEq.symm v) (by rwa [Equiv.apply_symm_apply]) j
  obtain ⟨ρ, hρ, ν, hs, hf⟩ := a0 Z
  obtain ⟨hN, hR⟩ := a5 Z
  obtain ⟨r1, r2⟩ := a6 Z hR
  have b1 := le_antisymm (a10 ρ hρ ν rd hf hc) (a11 ρ hρ ν rd hf hc)
  have b2 := le_antisymm (a12 ρ hρ ν rd hf hc) (a13 ρ hρ ν rd hf hc)
  simp only [realBase, realTw, Equiv.apply_symm_apply] at b1 b2
  exact ⟨rd, hβ, a2 rd hc, (b1.trans (a8 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r1.symm,
    (b2.trans (a9 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r2.symm⟩
end GlobalTheory.BigOn.Exp
end
end
end

section



section
set_option genSizeOfSpec false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
structure QLevAlt {v : VCom f.c} {t : W.P.T} (F : GlobalTheory.QPl.QFam v (f.t t)) : Prop where
  places : ∃ pl : Fin F.r ≃ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ i, Formalism.L2.NTheta.IsIdemAt (F.Q i).q.e (pl i).1 ∧ (F.Q i).q.v = (pl i).1.under (𝓞 D.host.F)
  mid : ∀ i j d hd, j < D.R.m → ∀ x ∈ KO (F.Q i).k _,
    ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ ((F.Q i).T.lev j d hd).J) ∧
    ∀ hx : x ∈ ((F.Q i).T.lev j d hd).J, levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))
      ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j) = (((F.Q i).T.lev j d hd).lam ⟨x, hx⟩ : ℂ)
  top : ∀ i, ∀ x ∈ KO (F.Q i).k _, ∀ g, (ofSplit (F.Q i).q).IsLoc (F.Q i).FT g x →
    (f.g.bT⁻¹ * g * f.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ (F.Q i).T.levTop.J)
def VectorFunctionCondition (v : VCom f.c) {t : W.P.T} (w : VTup (f.t t)) (sc : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (f.t t).om j (a * v.b j, a' * v.b (j + 1)) ((f.t t).pt j P) =
    sc j • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ (w.eQ j) (v.Ψ j P a a'))) ∧
  ∀ j h P, (f.t t).omT j h (v.b (j + 1), v.bT) ((f.t t).ptT j h P) =
    sc (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ (w.eQT j h) (v.ΨT j h P))
def GVectorCondition (v : VCom f.c) (s : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∀ P, ∀ a ∈ GinfC _,
    ∀ a' ∈ GinfC _, (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j)
      (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)) =
      s j • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a')) ∧
  ∀ j h d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∀ P,
    omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)) =
      s (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P)
end GlobalTheory.Fam
end
end
end

section



section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word)

structure GeometricFamily where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  ι : Type
  v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)
  o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι
  n : ℕ
  G : Fin n → GLoc v
  pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg
  Q : ∀ PP, _root_.GlobalTheory.Fam.QAllAlt W PP → GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g) PP
  d : _root_.GlobalTheory.MiTop.BottomData W u
  c₀ : ℕ → ℂ
attribute [instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
variable {W u} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
abbrev GeometricFamily.fam (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))) : _root_.GlobalTheory.Fam.FamilyCharacter W u :=
  ⟨a.g, a.j, row, col⟩
structure GeometricFamily.Is : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) a.g
  last : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).VolLast
  x : ∀ j, j ≤ D.R.m → (a.g.x j).Is
  vis : a.v.Is
  shape : ShapeOff a.v a.o
  gpin : GPin a.G
  tie : ∀ row col, _root_.GlobalTheory.Fam.CommutingVectorTie (a.fam row col) a.v ∧ _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl
  top : _root_.GlobalTheory.Fam.LeadingReadAt W u a.j a.g.bT
  norm : star a.o.ζ₀ ⬝ᵥ a.g.Lz.gram *ᵥ a.o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) ∧
    ∀ j h, a.v.τ j h *ᵥ a.o.ζ₀ = (-D.host.xi0 ^ (D.R.m / 2)) • (a.g.bes j 0 h).ζ
  stdG : ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.G i).FT ∧
    (a.G i).z₀ = fun r => (ofSplit (a.G i).q).pr (a.o.ζ₀ r)
  stdQ : ∀ PP h, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.Q PP h).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.Q PP h).FT ∧
    (a.Q PP h).z₀ = fun r => (ofSplit (a.Q PP h).q).pr (a.o.ζ₀ r)
  bot : (∀ h0, a.d.B.lev = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 D.R.rS h0) ∧ a.d.b = a.g.b 0 ∧ a.d.B.Adapted (W.S.tr u).wt ∧
    ∀ r, (a.d.B.d.i₀ *ᵥ vecB a.d.B.o a.d.B.ζ) r = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) r))
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
structure GeometricFamily.True (a : _root_.GlobalTheory.Fam.GeometricFamily W u) : Prop where
  pinX : GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.g.x a.g.vac a.c₀
  std : @GlobalTheory.AdForm.StdT B X I l Z u a.k a.fld a.val a.top a.loc a.ι (@TDat.p _ _ _ a.fld a.val a.top a.loc _ a.o)
    (@TDat.β _ _ _ a.fld a.val a.top a.loc _ a.o) (@TDat.Q _ _ _ a.fld a.val a.top a.loc _ a.o) fun j => (a.g.x j).L
  emb : GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  z0 : ∀ r, vecB (a.g.oT B.R.m rfl) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r =
    (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)
structure GeometricFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  xi : ∀ t, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) (I.xi (W.P.I.tup t))
  Q : ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t ↔ PP ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)
  top1 : ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j 1
end True
end GlobalTheory.Fam
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}
variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def ValEqvAlt (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
    GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = (_root_.GlobalTheory.Fam.pk_z W).cX.ρ γ.1 (c v)
def packageAtPoint (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : (_root_.GlobalTheory.Fam.pk_z W).cX.W :=
  ((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h)
def PackageValuation (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
    ∀ h y, HasMat h y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x h = c (val φ (latOf I (W.P.I.tup t) y))
def ValuationCompatible (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) : Prop :=
  ∀ w v, (_root_.GlobalTheory.Fam.pk_z W).prX (c w) v = pairVal B (j v) w
end GlobalTheory.TopVal
end
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}
variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)

theorem reads_of_pairVal (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a)
    (G : (I.rec7 l Z).what₂.Amb a) (hG : RecVal u a φ G)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → ℂ))
    (hf : ∀ h y (p : XPt (B.primes X) B.R I.sel (I.tup a)) v, HasMat h y → TC.PtOf y p →
      f v h = pairVal B (j v) (val φ (toRow I.sel (I.tup a) p))) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 a G f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    intro c v g hg
    have s := hC u
    rw [mul_one, hf g _ _ v hg (s.what₂.pt c)]
    have e := fun c' y => (s.eW ((W.R.T.cols.forms u).valP.eW.symm (Pi.single c (j v))) c' y y rfl).symm
    simp only [LinearEquiv.apply_symm_apply] at e
    refine (period_single l u I.mu0 φ _ (hG.1 rfl) c (j v) _ (funext fun y => (e c y).trans ?_)
      fun c' hc => funext fun y => (e c' y).trans ?_).symm
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
      rfl
  · obtain ⟨l0, t, he, ht, -, -, s⟩ := hW
    have key : ∀ (Tw : TwForms (I.rec7 l Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols Tw), Tw = I.tw l l0 Z → HEq t' t →
        ReadsG (t'.pt.cls u a h) (t'.pt.val u a h).eW j 1 (((I.rec7 l Z).eMtTw u a).symm G) f := by
      rintro _ t' rfl rfl
      intro c v g hg
      rw [mul_one, hf g _ _ v hg ((s.what₂ u a h).pt c)]
      have e := fun c' y => (s.eW u a h ((t'.pt.val u a h).eW.symm (Pi.single c (j v))) c' y y rfl).symm
      simp only [LinearEquiv.apply_symm_apply] at e
      refine (period_single l u a φ _ hG.2 c (j v) _ (funext fun y => (e c y).trans ?_)
        fun c' hc => funext fun y => (e c' y).trans ?_).symm
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
        rfl
    exact key _ _ he ht
end GlobalTheory.TopVal
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

theorem _root_.GlobalTheory.T.exactAt_of_oneMeasure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D → ∀ i : Fin D.R.m, ExactAt p i := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.exactAt_of_rows_alt | exact _root_.GlobalTheory.CovTop.MeasRd.exactAt_of_rows_alt | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.exactAt_of_rows_alt <;> assumption)
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

theorem _root_.GlobalTheory.T.small_place_finite_set_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite := by
  first | exact @_root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt | exact _root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt | (intros; apply _root_.GlobalTheory.FrameAutCof.cofinite_labels_at_alt <;> assumption)
end
end
