module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle048
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle512
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle051
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Formalism.LocalToGlobal.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLabelWeightsOfGreenCuspidalParametrisa
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle158
public import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses
public import Formalism.LocalToGlobal.GroupLattices.Bundle001
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.Mem.SRe
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
def SRest.toRealSpectralMatching (Rc : _root_.Formalism.L2.RecTAlt ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P) :
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc where
  toSTies := S.toSTies
  tr := P.tr
  into := P.into
  bij := P.bij
  lev := P.lev
  colPin := fun _ => S.colPin
  inst := P.inst
  G := P.G
  rowTie := fun _ => S.rowTie
  locTied := S.locTied
section
end
end GlobalTheory.Mem.SRe
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
def witDropA_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {A : AtP} {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z O) : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, x.nx.2.1⟩ }
theorem slot_mv_extension_with_at_property {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} (A : AtP)
    (hs : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  intro K B f T w Z O x Nd h O' hO' col n
  obtain ⟨t, hobj, hrx, ⟨c⟩, hsx, hox⟩ := hs K B f T w Z O (_root_.GlobalTheory.Mem.LiteralAutomorphy.witDropA_alt x) Nd h O' hO' col n
  exact ⟨t, hobj, hrx, ⟨⟨c.1, c.2, x.nx.2.2⟩⟩, hsx, hox⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_hecke_match_alt : GlobalTheory.TwSys.Cheb → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ GlobalTheory.SplitCoef.OSplit D' ∧ ∀ i, ZDecomp D'.nd i) → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll := by
  first | exact @_root_.GlobalTheory.CoefDuty.TakenLarge.evO_takenAll_alt | exact _root_.GlobalTheory.CoefDuty.TakenLarge.evO_takenAll_alt | (intros; apply _root_.GlobalTheory.CoefDuty.TakenLarge.evO_takenAll_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_bdRec_of_eq_alt {D D' : D7} {O : Obj D} {O' : Obj D'} (h : (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨D', O'⟩)
    (R : _root_.Formalism.L2.RecTAlt O'.ex) (c : ℝ) :
    ∃ b : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c, (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨D', O', R⟩ := by
  cases h
  exact ⟨R, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end

section



section
noncomputable section
namespace GlobalTheory.Svd.LinkStd
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
theorem stdTie_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex)
    (h : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') {D : D7} {O : Obj D} {c : ℝ} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (e : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) : StdTie D O R.T.ker := by
  cases e
  exact StdTie.intro h.std
theorem linkR_stdTie_entry {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) Q (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) fun _ D O _ R => StdTie D O R.T.ker :=
  RowE.of_all fun _ _ _ _ R _ _ hl => by
    obtain ⟨q, R', h, e⟩ := hl
    exact _root_.GlobalTheory.Svd.LinkStd.stdTie_of_eq_alt q R' h R e
end GlobalTheory.Svd.LinkStd
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_core_parameters_agree : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∃ (I : TwIn (q.w.D q.Z)) (n : _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I), I.E = twEOf q.O.ex.xd ∧ DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch I ∧ (⟨n.cf, n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩ ∧ n.gal = q.core_data_of_point.a.all.gal ∧ n.n = q.core_data_of_point.a.all.n ∧ n.exp = q.core_data_of_point.a.all.exp ∧ n.chiD = q.core_data_of_point.a.all.chiD ∧ n.twF = q.core_data_of_point.a.all.twF ∧ HEq n.types q.core_data_of_point.a.all.types ∧ HEq n.cover q.core_data_of_point.a.all.cover ∧ n.plB = q.core_data_of_point.a.all.plB := by
  intro hL p K q
  obtain ⟨I, hE, hG, hC⟩ := q.x.good.tw
  have hch := q.core_data_of_point.a.chr_eq
  have hc : Formalism.L2.NChoiceTied (q.w.D q.Z) q.O.ex.nch I (Formalism.L2.avDesign (q.w.D q.Z)) := by
    have c := q.core_data_of_point.a.all.choice
    first
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              good := fun w hw h => hC w hw h, conj := c.conj }
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              conj := c.conj }
  refine ⟨I, { q.core_data_of_point.a.all with choice := hc }, hE, hG, hch, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.AtSize

theorem eventually_sizeRows_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨max x0 (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), fun K h1 h2 h3 h4 hx β _ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hy0, hy44, hy8⟩ := hx
  have hsc : β.O.L.sc = K.s := β.sc
  have hsx : β.O.L.sc.x = K.s.x := by rw [hsc]
  have hse : β.O.L.sc.eps = eps := by rw [hsc, h4]
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy0.trans hsx.ge) hv (GlobalTheory.Plug.hostArith_bpt β)
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hq : ((GlobalTheory.ChiGrid.q0 β.D : ℕ) : ℝ) < β.O.L.sc.X' := by
    rw [hsc]
    exact leastSplitAuxiliaryPrime_lt_scaleBound β.c.isOver hG
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of N.params N.parT (N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1) N.sizes
    N.win.1.1 N.win.2.1.1 N.win.2.1.2 N.win.2.2.1 N.g_le hq N.ccK_top ?_ (by rw [hsx]; exact hy44)
  rw [hsx, hse]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) hy8 (by positivity)
end GlobalTheory.Mem.AtSize
end
end
end

section



section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.MiTop.CenIsom
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
open Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.DIV
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}

theorem ipC_colDictL_eq_sum_inner_shP (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)
theorem ipC_colDictL_rtr_eq (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u P P').trans (Eq.trans ?_ (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'
end GlobalTheory.MiTop.CenIsom
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE
namespace GlobalTheory.Mem.Top.Bl.WitSK
end GlobalTheory.Mem.Top.Bl.WitSK
open Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC Matrix in

theorem GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∀ (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) (t : Formalism.L2.Ker.KerEntTied q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S → KPin q t → ∃ T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex, T.toTiedDataS = S ∧ T.ker = t ∧ (∀ u i hi, T.crd u i hi = 1) ∧ _root_.Formalism.L2.Rows.RowPinMinAlt T ∧ _root_.Formalism.L2.JointsSAlt S ∧ Nonempty (PLift (Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W)) := by
  intro hL p K q S t hS hKp
  obtain ⟨he, hTw⟩ := hS.tw
  have hK := hKp.std
  have hC : TC.StdC q.w.I q.w.l q.Z S.cols := hS.cols ▸ q.x.col.std
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hD : TC.StdDt q.w.I q.w.l q.Z S.full.1.base.dt := by
    have key : ∀ (C : ColsTiedSym (q.w.D q.Z)) (F : ColsFullS C), C = q.x.col.C → HEq F q.x.col.full →
        TC.StdDt q.w.I q.w.l q.Z F.1.base.dt := by
      intro C F hC' hF
      subst hC'
      cases hF
      exact q.x.col.stdDt
    exact key _ _ hS.cols hS.full
  have hcf : S.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst hS.chr
  have hdiv : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) S.n.cf q.O.ex.nch S.n.tp q.O.X) :=
    ⟨WitSK.of_sigma_eq hS.chr (fun c tp => Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) c q.O.ex.nch tp q.O.X) q.x.div.chr⟩
  have hψ : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) S.theta.W.ψ (-1) :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) A.W.ψ (-1)) q.x.th.std
  have hweq : Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.WeilCompatibleEquivariance A.W) q.x.th.weq
  refine ⟨{ S with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl,
    fun _ _ _ => rfl, ⟨fun u => ?_, fun u μ hμ _ h1 => ?_, q.x.what₂.r.Y.bu⟩,
    _root_.GlobalTheory.Mem.JointsTrue.joints_of_standard_character q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex S hC hD hcf hS.dt hdiv hψ, ⟨⟨hweq⟩⟩⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [GlobalTheory.Mem.Col2.TC.KerSK.sharp_heq hK.X_eq (GlobalTheory.Mem.Col2.TC.KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact q.w.ok.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (q.w.D q.Z)) (Units.val (1 : GL (Fin ((q.w.D q.Z).R.N i)) (q.w.D q.Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [GlobalTheory.Mem.Col2.TC.KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact _root_.GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw_alt q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex _ he hC hTw u μ hμ h1
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {A : AtP}
def builtA_drop_alt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z c) : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2.1⟩ }
def builtExtendByAutomorphy {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z c) (a : A K B f T) : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2, PLift.up a⟩ }
theorem isBuiltE_extensionWithAtProperty_iff (K X f T c) :
    IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K X f T c ↔ IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨b, hb⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtA_drop_alt b, hb⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨b, hb⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtExtendByAutomorphy b a, hb⟩, he⟩
theorem isGoodE_extensionWithAtProperty_iff (K X f T c) :
    IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K X f T c ↔ IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtA_drop_alt b, hb⟩, g⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨⟨_root_.GlobalTheory.Mem.LiteralAutomorphy.builtExtendByAutomorphy b a, hb⟩, g⟩, he⟩
theorem memberE_extensionWithAtProperty_of_memberE : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A →
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  intro hL N S Γ A hA ⟨hB, h1, hE, h2⟩
  refine ⟨hB, ?_, ?_, ?_⟩
  · have h := Step.and (KP := KPx) h1 (Step.of_evLgG (p := fun _ B _ T => T = TwDat.untw B T.pl) hA)
    refine EvG.imp h fun K _ _ _ _ H => H.imp fun B f T _ G k u v => ?_
    obtain ⟨⟨C, W, V, S, N, Gs, c, q⟩, a⟩ := G k u v
    exact ⟨C, W, V, S, N, Gs, c, (_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).2 ⟨q, a⟩⟩
  · exact EvG.imp hE fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q =>
      G k u C W V S N Gs c ((_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1
  · have hR : LargeBaseConditionG KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (fun K X f T _ => A K X.B f T) :=
      EvG.imp hA fun K _ _ _ _ H => H.imp fun B f T _ a _ C W V S N Gs c _ => a
    have h2' := SecondG.sAnd_of_largeBase KPx _ _ _ hB hR h2
    refine EvG.imp h2' fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q e Av S₂ hS₂ => ?_
    obtain ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c', q', tw, g', a⟩ :=
      G k u C W V S N Gs c ((_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1 e Av S₂ hS₂
    exact ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c',
      (_root_.GlobalTheory.Mem.LiteralAutomorphy.isBuiltE_extensionWithAtProperty_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨q', a⟩, tw,
      (_root_.GlobalTheory.Mem.LiteralAutomorphy.isGoodE_extensionWithAtProperty_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨g', a⟩⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end

section



section
noncomputable section
namespace GlobalTheory.Top.Irr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin
end
section
open Formalism.BasicNotions Formalism.MainNotions
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem closed_linkIRR_of_join_count : GlobalTheory.GLq.Green → ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)), Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm := by
  intro hG 𝒜 sel cIc hcI irrC
  have irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.MainNotions.ArithmeticCylinders.admLq (Fm.D x i) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez 6 :=
    closed_of_mem (irrC.imp fun Fm _ _ H hc => by
      obtain ⟨x0, H⟩ := H
      refine ⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩
      have h1 : Fm.x1 < x := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      obtain ⟨A, a, b, c⟩ := H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i
      exact ⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c,
        sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)
  exact (irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ =>
      linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h
end GlobalTheory.Top.Irr
end
end
end

section



section
noncomputable section
namespace Formalism.L2.G.ServT
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2
structure SelectionServed (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : Prop where
  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1
  pdv : Closed 𝒞 fun Fm _ => ∀ (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ((((sel Fm hc).2 x hx h0 i).T.ker.ent.UnUnit ∧ OrbitPlaces.KmapRat ((sel Fm hc).2 x hx h0 i).T.ker.ent ∧
        OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i)
          (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg))
theorem sumOverPrimesService_of_servT {𝒞 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒞) (h : _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel) : SumOverPrimesHypotheses 𝒞 := by
  refine ⟨h.twU, closed_imp_class h.pdv ?_⟩
  intro eps Fm CH hc hp
  refine ⟨(sel Fm hc).1, ?_⟩
  intro x hx0 hx i
  exact ⟨((sel Fm hc).2 x hx hx0 i).T.ker.ent, hp hc x hx hx0 i⟩
theorem closed_servF_of_servT_of_dGamSize {𝒞 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒞) (hD : Closed 𝒞 fun Fm _ => DGamSize Fm) (h : _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel) :
    Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm :=
  sum_over_primes_service 𝒞 hD (_root_.Formalism.L2.G.ServT.sumOverPrimesService_of_servT sel h)
end Formalism.L2.G.ServT
end
end
end
