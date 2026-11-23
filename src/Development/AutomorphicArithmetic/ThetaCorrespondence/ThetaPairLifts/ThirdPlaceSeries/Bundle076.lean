module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle569
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
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
import Mathlib.RingTheory.Etale.Weakly
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

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.TieIdem
end GlobalTheory.TieIdem
namespace GlobalTheory.TieIdem
theorem tied_good_idem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hr _
  exact idemOf_props p.P.A3.A.X hr.ok.ok2.irr
end GlobalTheory.TieIdem
end
end
end

section



section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.CovTop.good_lattice_ne_bot_at_point : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz), p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m, latGood p.R.toRealDat p.F.lv2 i ≠ ⊥ := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  exact GlobalTheory.CovTop.ne_bot_of_isLattice_coords (latGood p.R.toRealDat p.F.lv2 i)
    (show 0 < (p.S false).dW i from hD.symm ▸ hpos) (p.R.toRealDat.bL p.F.lv2 false i) hli (hp.prim.mLat i)
end
end

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.GramPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem hasGram_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m, HasGram (nrmR p.R.toRealDat i) :=
  fun p hp _ i => hasGram_of_unif p.R.toRealDat hp.prim.unif i
end GlobalTheory.CovTop.GramPt
end
end
end

section



section
open NumberField
noncomputable section
namespace GlobalTheory.CovTop
open Formalism.L2.DIV
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem chi_mul_psi_inv_mem_core_alt (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m) : p.PointConditions' → RecTied D L →
    ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈
      Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  intro _ _ u
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hN : ∀ PP : p.R.Pg, (p.T.Q.l.M' : kP PP.1) = 0 := by
    intro PP
    obtain ⟨k, hk⟩ := (hL.Pg PP.1).1 PP.2
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.1.under (𝓞 D.host.K)).asIdeal := by
      rw [hk]; exact p.R.C.P.pb_over k
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
      change _ ∈ Ideal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) PP.1.asIdeal at h2
      rwa [Ideal.mem_comap, map_natCast] at h2
    have h3 : ((D.host.g k : ℕ) : kP PP.1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.1.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h1
    have hk' : D.host.g k ∣ p.T.Q.l.M' := by
      refine dvd_trans ?_ (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
      rw [hM]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    obtain ⟨c, hc⟩ := hk'
    rw [hc, Nat.cast_mul, h3, zero_mul]
  have hu : p.R.eG u ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG u) ∈ (p.F.lv2.lvl false).P
    simp
  have key : ∀ X : LevelP p.R.Pg D.R.r ℂ, X = P0 p.R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
      (∀ PP, g PP ∈ unip (kP PP.1) D.R.r) ∧ X.chi ⟨g, hg⟩ ^ p.T.Q.l.M' = 1 := by
    rintro X rfl g hg
    exact ⟨fun PP => (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _), unipotentTypeLevel_char_pow_eq_one _ _ ψ0 _ hN _⟩
  obtain ⟨hun, hpow⟩ := key _ hlev _ hu
  have e1 : (p.R.levR p.F.lv2 false).chi ⟨p.R.eG u, hu⟩ =
      Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((p.F.lv2.lvl false).ψ u) := by
    show Units.map _ ((p.F.lv2.lvl false).ψ _) = _
    congr 2
    exact Subtype.ext (by show p.R.eG.symm (p.R.eG u) = u; exact p.R.eG.symm_apply_apply _)
  have h5 : (((p.F.lv2.lvl false).ψ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    apply D.what₂.embLL.injective
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (e1 ▸ hpow)
    simpa using this
  have hchi : (p.R.toRealDat.FW i).chi u = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hB.grp.chiW i u, Finset.prod_eq_one (fun PP _ => by rw [det_of_mem_unip (hun PP), map_one, Units.val_one]),
      Units.val_one, map_one]
  rw [hchi, one_mul]
  have hy : (((p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, h5, inv_one]
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  have hz' := hz.map_of_injective (f := algebraMap p.T.Q.c.F D.what₂.LL) (algebraMap p.T.Q.c.F D.what₂.LL).injective
  haveI : NeZero p.T.Q.l.M' := ⟨hN0⟩
  obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hy
  exact ⟨_ ^ k, by rw [map_pow, hk]⟩
end GlobalTheory.CovTop
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
theorem iC_base_factor_of_rows_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have h2 := (hCx.what₂ false).1
  have hr := hCx.ratMu false
  refine ⟨h2.1, fun t y => ?_⟩
  have hspec := relMat_spec ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0)
    ((p.R.toCx3 p.F).iC p.F.cr false t)
    (fun k => by rw [← (h2.2.1 t).2]; exact LinearMap.mem_range_self _ _)
  show (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
      (cpt p.P.A3.fam3.base3.v0.embedding ((kMat p.P.A3.fam3.base3.v0.embedding ((p.R.toCx3 p.F).rowMatC p.F.cr false t)).mulVec y)) = _
  rw [cpt_mulVec, kMat_map _ (hr t)]
  exact hspec _
end GlobalTheory.BigTop.Fun
end
end
end

section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.CovTop.MeasRd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.CovTop.MeasRd
namespace GlobalTheory.CovTop.MeasRd
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem exactAt_of_rows_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.PointConditions') (hM : OneMeasure D) (i : Fin D.R.m) : ExactAt p i := by
  intro σ f
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hk : p.κ = kapTop D := KapIs.eq (κ := p.κ) p.fw.kap hTau
  have ha : wtA (p.κ i) = wtA (kapTop D i) := by rw [hk]
  have hn : (p.κ i).n = (kapTop D i).n := by rw [hk]
  have hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i := by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]
  obtain ⟨-, hd, h2⟩ := hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv
  have hmod := p.charW.base.models
  obtain ⟨h0, ht, he, -⟩ := h2 _ _ (hmod.νW i)
  obtain ⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ) := ⟨_, rfl⟩
  have hs := sgAt_mk_eq D.what₂.embLL σ
  rw [← hs_def] at hs
  show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _
  rw [← hs_def]
  have hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ) := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; exact GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)
  have hgood := goodEmb_goodOf p.T.Q.c (res p.T s)
  have hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgood
  obtain ⟨-, hrange, hip⟩ := hmod.HW i s
  by_cases hf0 : f = 0
  · subst hf0
    have hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0 := by
      rw [map_zero]; rfl
    have hz := petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
      (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0
    rw [map_zero, norm_zero, zero_mul, zero_smul] at hz
    rw [hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]
  set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    with hy
  have hy0 : y ≠ 0 := fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))
  set x := (p.R.toRealDat.FW i).j s y with hx_def
  have hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s := hrange ▸ LinearMap.mem_range_self _ x
  set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def
  have hf' : f' ∈ scalarForms p.T i (gd p.T s) := by
    have := ((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood
    show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))
    rw [modelWt_wtZ, ← ha, ← hn]
    exact this
  have hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f' := by
    by_cases hgs : GoodEmb p.T.Q.c (res p.T s)
    · have hgd' : gd p.T s = res p.T s := by show goodOf _ _ = _; rw [goodOf, if_pos hgs]
      have hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgs
      have hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H,
          ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
            ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) :
              Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) =
              hV' ▸ p.T.phiJ ((i : ℕ) + 1) (res p.T s) (wtA (p.κ i)) (g : p.T.R ((i : ℕ) + 1)) := by
        by_contra hne
        have hj0 := p.fw.ev0 i s hgs hV' hne
        have hli := (hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)
        rw [hj0] at hli
        exact hli.ne_zero 0 (LinearMap.zero_apply _)
      refine Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (p.fw.ev i s hgs hV' hpre f).trans ?_
      show phiC p.T hV' (wtA (p.κ i)) _ = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha]
      exact phiC_congr hgd'.symm _ _ _ _
    · have hgd' : gd p.T s = resC p.T s := by show goodOf _ _ = _; rw [goodOf, if_neg hgs]
      have hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)
      obtain ⟨v, hv, hvf⟩ := (p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)
      refine Or.inr ⟨hgs, v, hv, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (hvf f).trans (funext fun g => ?_)
      show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha, phiC_congr hgd' hV hVc]
  have e := (he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2
  rw [← hip, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f' := by
    have : (((‖x‖ ^ 2 : ℝ)) : ℂ) = _ := (Complex.ofReal_pow _ _).trans e
    exact_mod_cast this
  rw [hf'_def, probSq_rdU] at e'
  unfold petW
  rw [← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]
  rfl
end GlobalTheory.CovTop.MeasRd
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
namespace GlobalTheory.FrameAutCof
theorem cofinite_labels_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite :=
  fun p _ _ j _ _ _ _ w _ _ hs => cofinite_labels p j (p.R.mu w) hs.1.ne_zero
end GlobalTheory.FrameAutCof
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
namespace GlobalTheory.FrameLab
variable {D : D7}
theorem labels_ok_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ Q
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam (p.R.mu w) Q.1 Q.2
  refine ⟨⟨plOf p j (p.R.mu w) Q, fun e => h2 e.symm, (under_conjPl _).symm⟩, under_conjPl _,
    (absNorm_conjPl _).trans h3.symm, mem_conjPl_of_fixed _ (map_natCast _ _)⟩
end GlobalTheory.FrameLab
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end
theorem ompins_onto_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' →
    BarTie (fw2 p) ∧ (∀ i, OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i) ∧
      ∀ i, PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i :=
  fun _ _ _ _ _ _ _ _ _ _ p what₂ => ⟨conjugateReadingsVanishing_splitPart p, thetaRowData_pins_splitPart p, phaseCompatible_splitPart_of_liftUniformisation p what₂.prim.unif⟩
end GlobalTheory.BigOn
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
namespace GlobalTheory.FamTraceChi
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev reductionYZero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (h : GA D (D.sp.Y 0)) : Formalism.L2.DIV.G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r :=
  Formalism.L2.DIV.rTup ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) (finE (Yc D 0) h)
theorem rChi_eq_lvP_chi_of_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {h : GA D (D.sp.Y 0)} (hh : h ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    ∃ hg : _root_.GlobalTheory.FamTraceChi.reductionYZero_alt W h ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H, _root_.GlobalTheory.MiTop.realCharacter W h = (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hg⟩ : ℂˣ) : ℂ) := by
  have h2 := hh.2
  have h3 := (Formalism.L2.DIV.mem_lev.1 h2).2
  refine ⟨h3, ?_⟩
  simp only [_root_.GlobalTheory.MiTop.realCharacter, Formalism.IndefR.Lev.levChi, Formalism.L2.DIV.levFn]
  rw [Formalism.L2.DIV.extendOne_of_mem _ h3]
  simp [Formalism.IndefR.Links.LevCh.dat0, Formalism.IndefR.Lev.datY]
  rfl
end GlobalTheory.FamTraceChi
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.Model
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem AtMem.at_member_imp {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem AtMem.and_z {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
end GlobalTheory.HeightCounting.Up.Model
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
namespace GlobalTheory.ResThree
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro PP hPP
  obtain ⟨plg, iso, -, -, -, -⟩ := t.r.z.pins.keep.grp
  obtain ⟨h0, h1⟩ := two_ne_zero_one _ (GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients.three_le_g (w.st Z).toD7 (plg.symm ⟨PP, hPP⟩).1)
  have e := iso (plg.symm ⟨PP, hPP⟩)
  rw [Equiv.apply_symm_apply] at e
  exact ⟨e 2, fun h => h0 (e.injective (by rw [h, map_zero])),
    fun h => h1 (e.injective (by rw [h, map_one]))⟩
end GlobalTheory.ResThree
end
end
