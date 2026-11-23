module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033

@[expose] public section

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevelUnip
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end Res
variable {D : D7}
end GlobalTheory.LevelUnip
open GlobalTheory.LevelUnip in
theorem GlobalTheory.LevelUnip.unip_mod_half_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ (g : (p.F.lv2.lvl false).P) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La), z ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) → (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) z ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g z hz
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hu : p.R.eG g ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG g) ∈ (p.F.lv2.lvl false).P
    simp
  have hun : ∀ PP, p.R.eG g PP ∈ unip (kP PP.1) D.R.r := by
    rw [hlev] at hu
    exact fun PP => (Subgroup.mem_pi _).1 hu PP (Set.mem_univ _)
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P ∈ p.R.Pg, (((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) - 1) ^ D.R.r = 0 := by
    intro P hP
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    have hU := hun ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hp' : (∏ P ∈ p.R.Pg, P.asIdeal) * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [← hhalf]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hcong := fun b (hb : b ∈ Mfr p.T.Q.l) => exists_pow_cong hβ p.R.Pg hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) hf D.R.r
  have h0 : ∀ a ∈ Mfr p.T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem wtBig_run_alt : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    WtBig (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) := by
  obtain ⟨ε1, hε1, H⟩ := GlobalTheory.T.runSizes_quotientGaps_large
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨0, le_rfl, x0, fun x hx hxx ι p _ i hi => ?_⟩
  obtain ⟨hD1, hDT, hG⟩ := hx0 x hx hxx ι
  obtain ⟨hr, hdim, hgap⟩ := GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi
  have hlen : lenT p i (Fm.parT x hx ι).PP = ⌈(Fm.parT x hx ι).PP ^ 2 *
      (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) / ((Fm.D x ι).R.m : ℝ)⌉₊ := by
    rw [lenT, GlobalTheory.CompHS.dimFlag_eq, hdim]
  obtain ⟨hG1, hG2⟩ := hG _ _ rfl hlen
  have hc0 : ((cZero (Fm.D x ι) ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 := by
    exact_mod_cast (cZero_spec (Fm.D x ι) ((i : ℕ) + 1)).2.2
  clear H hK hx0 hG
  refine ⟨fun τ k hk => ?_, ?_, ?_⟩
  · rw [WtPar.gap_u₁ _ τ hk, WtPar.gap_uMinus_sub_kap _ τ hk]
    simp only [WtPar.T₁]
    rw [hdim]
    have hGeq : ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * ((dat p i).p + (dat p i).q) +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) =
        ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) := by rw [hr]
    rw [hGeq]
    have hr2 : (((dat p i).p + (dat p i).q : ℕ) : ℤ) = (Fm.D x ι).R.r := by exact_mod_cast hr
    generalize ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = G at hG1 hG2 ⊢
    generalize lenT p i (Fm.parT x hx ι).PP = T at hG1 hG2 ⊢
    generalize (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 = Dd at hG1 hG2 ⊢
    have hT : (0 : ℤ) < (T : ℤ) + (Dd : ℤ) + 1 := by positivity
    refine Int.le_ediv_of_mul_le hT ?_
    obtain ⟨g1, g2⟩ := hgap τ k hk
    by_cases hb : k + 1 = (dat p i).p
    · rw [if_pos hb, hr2]
      have e := g2 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤
          ((gap (uW p i τ) k + (-(cZero (Fm.D x ι) ((i : ℕ) + 1)) - (2 * ((Fm.D x ι).R.r : ℤ) - 2)) : ℤ) : ℝ) := by
        push_cast at hG2 e ⊢
        linarith
      exact_mod_cast this
    · rw [if_neg hb]
      have e := g1 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + 2 : ℤ) : ℝ) := by
        push_cast at hG1 e ⊢
        linarith
      exact_mod_cast this
  · show GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i (Fm.parT x hx ι).PP
    rw [hdim, hlen]; exact hDT
  · show 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i)
    rw [hdim]; exact hD1
end GlobalTheory.HSApp
end
end
end

section



section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.CovTop GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem recAt_of_gramAt_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (hg : GramAt p i) : RecAt p i := by
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  obtain ⟨hU, hN⟩ := GlobalTheory.T.liftForms_frames_majorantNorm_eq_petersson p.R p.F false i (RealDat3.kForm_of hp.prim.unif false)
  have hn1 : (1 : ℝ) ≤ RealDat.nP p.F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hs0 : 0 < (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  have hs1 : (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hn1)
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  have hsp : ∀ x ∈ latGood p.R.toRealDat p.F.lv2 i,
      x ∈ Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) := by
    intro x hx
    have hxW : x ∈ p.R.toRealDat.WL p.F.lv2 false i := ⟨hx.1.2, hx.2⟩
    have e : Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) = p.R.toRealDat.WL p.F.lv2 false i := by
      have := (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).span_eq
      have h2 := congrArg (Submodule.map (p.R.toRealDat.WL p.F.lv2 false i).subtype) this
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h2
      exact h2
    rw [e]; exact hxW
  have key := GlobalTheory.T.covolumePerRank_le_neg_slope_scaled D.what₂.LL _ (nrmR p.R.toRealDat i) hg.1 (latGood p.R.toRealDat p.F.lv2 i) _ (show 0 < (p.S false).dW i from hD.symm ▸ hpos)
    (p.R.toRealDat.bL p.F.lv2 false i) hli hsp ((p.S false).XW i) _ hs0 hs1 hU hN (by first | exact hp.prim.mLat i | exact (hp.prim.mLat i).toIsLattice)
  unfold RecAt
  rw [← hD]
  exact key
theorem liftRecursive_of_gram : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := fun h =>
  Closed.imp h fun _ _ _ ⟨C, hC, x0, h⟩ =>
    ⟨C, hC, x0, fun x hx hle ι p hp i => _root_.GlobalTheory.CovTop.recAt_of_gramAt_alt p i hp.1 (h x hx hle ι p hp i)⟩
end GlobalTheory.CovTop
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SetFromSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem setting_of_size_alt (p : PtAt ex Csz) (hp : p.PointConditions') (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (he : GlobalTheory.GLq.ESerTie D) :
    HidaSetting L p.R.toRealDat p.F.lv2 :=
  { size := hs
    eser := he
    host := p.host
    hF := p.hF
    core := (GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D _ _ _ _ _ _ p.R p.F p.charW hp.exAt).1
    mu_off := p.charW.tup.mu_off
    mu_used := p.charW.tup.mu_used
    mu_ne := p.charW.tup.mu_ne
    mu_conj := p.charW.tup.mu_conj
    mu_on := p.charW.tup.mu_on
    grp := p.charW.base.grp.record
    guard := p.qGuard
    fin := finite_tup p
    fullY := p.charW.fullY
    fullX := p.charW.fullX
    std := p.stdChar
    stdX := p.stdX
    betaX := p.betaStd.2 }
end GlobalTheory.BigTop.Fun.SetFromSize
namespace GlobalTheory.BigTop.Fun
theorem setAt_of_sizeAt_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint :=
  h.imp fun _ _ _ a => _root_.GlobalTheory.BigTop.Fun.evPt_mono a fun _ _ _ p hp b he => _root_.GlobalTheory.BigTop.Fun.SetFromSize.setting_of_size_alt p hp b he
end GlobalTheory.BigTop.Fun
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pt_realised_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.RealisedCondition :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩
theorem pt_T_pb_eq_R_pb {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins
theorem pt_realised_and_pb_eq : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), b.pt.RealisedCondition ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨_root_.GlobalTheory.Fc.Ind.pt_realised_alt b, _root_.GlobalTheory.Fc.Ind.pt_T_pb_eq_R_pb b⟩
end GlobalTheory.Fc.Ind
end
end

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FromComp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem u_low_of_cover_hyps (h1 : _root_.GlobalTheory.CovTop.DeepGoodness) (h2 : _root_.GlobalTheory.CovTop.SizeCondition) (h3 : _root_.GlobalTheory.CovTop.CoverDegree) (h4 : _root_.GlobalTheory.CovTop.ShareCondition) (h5 : _root_.GlobalTheory.CovTop.HeightCondition) (h6 : _root_.GlobalTheory.CovTop.CoverHeightSum) (h7 : _root_.GlobalTheory.CovTop.SumBoundCondition) : _root_.GlobalTheory.CovTop.UniformLowerBound := by
  refine Closed.imp (Closed.and h1 (Closed.and h2 (Closed.and h3 (Closed.and h4 (Closed.and h5 (Closed.and h6 h7)))))) ?_
  rintro _ Fm _ _ ⟨⟨_, -, a1⟩, ⟨A, -, a2⟩, ⟨_, -, a3⟩, ⟨_, -, a4⟩, ⟨C1, hC1, a5⟩, ⟨C2, hC2, a6⟩, ⟨_, -, a7⟩⟩
  refine ⟨2 * (3 * C1 + C2 + 4), by positivity, ?_⟩
  obtain ⟨x0, h⟩ := a1.and (a2.and (a3.and (a4.and (a5.and (a6.and a7)))))
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h x hx hle ι p hp
  exact atPoint p i Y _ A C1 C2 hi (b1 i hi Y hY) (b2 i) (b3 i hi Y hY) (b4 i hi Y hY) (b5 i hi Y hY) (b6 i hi Y hY)
    (b7 i hi Y hY)
end GlobalTheory.CovTop.FromComp
end
end
end

section



section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology
namespace GlobalTheory.CovTop.Assembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covolX_of_lift_bounds_and_coreLe : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith
end GlobalTheory.CovTop.Assembly
end
end
end

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.LowCover
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem low_of_cover_hypotheses : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  intro hS hD hE hG hR hM hK hGm hF hU
  refine Closed.imp (((((((((hS.and hD).and hE).and hG).and hR).and hM).and hK).and hGm).and hF).and hU) ?_
  intro eps Fm CH _ hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨CS, -, aS⟩, CD, -, aD⟩, _, -, aE⟩, _, -, aG⟩, _, -, aR⟩, _, -, aM⟩, _, -, aK⟩, _, -, aGm⟩,
    CF, hCF, aF⟩, CU, hCU, aU⟩ := hh
  refine ⟨max CD (2 * (CF + CU) + 9), le_max_of_le_right (by linarith), ?_⟩
  obtain ⟨x0, h⟩ := ((((((((aS.and aD).and aE).and aG).and aR).and aM).and aK).and aGm).and aF).and aU
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bS, bD⟩, bE⟩, bG⟩, bR⟩, bM⟩, bK⟩, bGm⟩, bF⟩, bU⟩ := h x hx hle ι p hp
  have hS' := bS i
  have hE0 : 0 ≤ unitE p := by obtain ⟨a, b, -⟩ := hS'; linarith
  rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with heq | hlt
  · exact lowAt_mono (bD i heq) (le_max_left _ _) hE0
  · obtain ⟨Y, hY⟩ := bE i hlt
    exact lowAt_mono (lowAt_of_cover p i _ CS CF CU hCF hCU hS' Y (bG i hlt Y hY) (bR i hlt Y hY) (bM i hlt Y hY)
      (bK i hlt Y hY) (bGm i hlt Y hY) (bF i hlt Y hY) (bU i hlt Y hY)) (le_max_right _ _) hE0
end GlobalTheory.CovTop.LowCover
end
end
end

section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CoreSlope
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem coreLe_of_gram_meas_rat_alt : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  intro hg hm hr
  unfold _root_.GlobalTheory.CovTop.GramCondition _root_.GlobalTheory.CovTop.MeasureCondition _root_.GlobalTheory.CovTop.LiftRational _root_.GlobalTheory.CovTop.CoreBound' _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩
end GlobalTheory.CoreSlope
end
end
end

section



section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions
namespace GlobalTheory.CovTop
theorem sumC_of_deepGood_alt : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩
end GlobalTheory.CovTop
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SizeProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sizes
variable {D : D7} {L : SizeData₂ D}
end Sizes
section Main
variable {D : D7} {L : SizeData₂ D}
theorem sizeAt_alt : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt :=
  ⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ =>
    let ⟨x₀, h⟩ := sizeRows_fam he Fm hF
    ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩
end Main
end GlobalTheory.BigTop.Fun.SizeProof
end
end
end
