module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle050
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle049
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Divisibility.Bundle006
public import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBDGam
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3
theorem lower_map_sharp_ambient_tie_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (T : _root_.Formalism.L2.TiedDataSKAlt ex), (∀ u, LowerMapTieS (T.cols.forms u)) → (∀ u μ (hμ : μ ≠ D.what₂.mu0) (_ : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1) → (∃ J, AmbTie D x.A3.A (RowSide.sharp D) ex.amb x.F.P1 x.F.ψ1 x.Y.tup x.Y.jA J) → ((∀ (t : x.T) (c : (x.A3.A.fam.R t).S.Cl), Fintype.card ((x.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧ ∀ (j : Fin D.R.m) (t : x.T) (c : (x.A3.A.fam.L j t).S.Cl), Fintype.card ((x.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) → _root_.Formalism.L2.Rows.RowSideDeterminedAlt T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro D L hT Gi Gl K Yd cX ex x T hL hLt hA hG
  exact
    { lowerMap := hL
      lowerMapTw := hLt
      buDef := x.Y.bu
      ambS := hA
      faces := ⟨x.F.Dc, x.F.Sp, rfl, HEq.rfl⟩
      gamDvd := hG }
end GlobalTheory.Mem.R3
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_integrality_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  first | exact @_root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt | exact _root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt | (intros; apply _root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt <;> assumption)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
namespace Formalism.L2.N.ExtNRows3
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
section Pin
variable (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
include hp hL h in
open Classical in
theorem base_rows_eq_record_rows_alt : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm
include hp hL h in
theorem finrank_Mj_eq_D0 : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := finrank_Mj_eq_dW P ⟨k, by omega⟩
  rw [dW_eq_D P h, _root_.Formalism.L2.N.ExtNRows3.base_rows_eq_record_rows_alt T P hp hL h] at this
  exact this
end Pin
theorem thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact _root_.Formalism.L2.N.ExtNRows3.finrank_Mj_eq_D0 T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2
end Formalism.L2.N.ExtNRows3
end
end
end

section



section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
theorem GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex _ T P K hpin hmu X0 hX0 v F
  have ht : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu P.A3.fam3.base3.μ0 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
    rw [hmu]
    have h : Formalism.L2.DIV.Qprime ((1 : Formalism.L2.DIV.Tup K.X.F K.X.E D.what₂.LL K.c.Sg) : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
      change Formalism.L2.DIV.Qprime (1 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅
      ext w
      simp [Formalism.L2.DIV.Qprime, MonoidHom.ker_one]
    unfold Formalism.L2.Col.QE
    split_ifs with hf
    · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
      rfl
    · rfl
  obtain ⟨hM, hev⟩ := hpin.columnEvaluationOk
  obtain ⟨ι, h1, h2⟩ := hev D.u₀
  obtain ⟨F', hm, hres, hι1⟩ := h1 _ ht hQ ((Formalism.L2.DIV.rV0 D P.A3.A P.Ps P.ψs P.A3.fam3.base3.μ0).mulVec F)
  obtain ⟨hm2, hι2⟩ := h2 _ ht hQ F
  have hz := hι1.symm.trans hι2
  have hF := congrArg Subtype.val (GlobalTheory.ColEvNorm.zOfRow_injective _ _ _ _ _ _ _ _ hz)
  rw [← hF]
  exact GlobalTheory.ColEvNorm.ipAt_le_of_ties (Xf := fieldsLL D K.X K.e) K.c.Pr K.c.Rk K.c.W K.c.Ch K.c.sel K.c.hX K.c.Lv K.c.Xg
    K.v0 K.TU K.xiVal K.trIv P.A3 P.Ps P.ψs P.Zs K.c.mu K.c.hP K.gEq hpin.grpTie
    (congrArg Ranks.m K.kerTie.2.1) K.plEq K.i0Eq K.tEq K.famEq K.muTie K.ok1 hpin.psTie.1 hpin.psTie.2
    X0 hX0 v F F' hm hres
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure RecTAlt (ex : Extra D L hT Gi Gl K Y cX) where
  T : _root_.Formalism.L2.TiedDataSKAlt ex
  pin : _root_.Formalism.L2.Rows.RowPinMinAlt T
  joints : _root_.Formalism.L2.JointsSAlt T.toTiedDataS
  host : _root_.Formalism.L2.HostDatumSelfDual T.toTiedDataS
  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W
def ExtraDataRecursive (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.RecTAlt ex)
theorem ExtraDataRecursive.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : _root_.Formalism.L2.ExtraDataRecursive ex) : _root_.Formalism.L2.ExtraDataSelfDualKernel ex :=
  let ⟨R⟩ := h; ⟨R.T⟩
end
def SecondLayerFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i)) ∧ _root_.Formalism.L2.LinkedFamiliesAligned' Fm
theorem SecondLayerFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.LinkedFamiliesKernelFrame' Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩
theorem SecondLayerFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm := h.c2sk.c2s
theorem group_compatibility_of_second_layer_family {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : G.GroupCompatibilityFamily Fm := _root_.Formalism.L2.gTiedF_of_C2S_alt Fm h.c2s
end Formalism.L2
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions
noncomputable section
namespace Formalism.L2.DIV.Cons
open Formalism.L2.DIV Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem gamma_size_of_sizeData_alt {Tk : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (hR : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Tk P) (hTf : Finite P.T) (hSG : SizeG L)
    (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) :
    DGamSize P.A3.A P.P0 P.ψ0 (ofRecord D L Del h0) Nc hTf 1 (2 + 9 * C) :=
  dGamSize_record_one P.A3.A P.P0 P.ψ0 hTf L hSG hSC Del h0 Nc hNc P.tied.div.grp.card D.u₀ hR.gamDvd.2 C hC hF
end Formalism.L2.DIV.Cons
end
end
end
