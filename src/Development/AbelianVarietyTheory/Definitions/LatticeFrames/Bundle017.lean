module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle002

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (p : ι → SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)) : Prop :=
  (∃ e : ι ≃ (B.primes X).vT u, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (e i).1) ∧
    ∀ j, j ≤ B.R.m → (∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) ∧ ∀ i, (β j i).IsLat (L j) (Q j i).lat ∧
      ∀ z ∈ L j, ∀ r : Fin ((I.rec7 l Z).sp.X j).rank, r.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∃ s : 𝒪[k],
        (s : k) = (p i).pr (incA (I.rec7 l Z) ((show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)) * z r)) ∧
        (Q j i).HasVal ((β j i).b' *ᵥ fun r' => (p i).pr (incA (I.rec7 l Z) (z r'))) (residue 𝒪[k] s)

end GlobalTheory.AdForm

end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder Kronecker
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem jpq_eq_one {A : HSp D} (hp : A.IsPosDef) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 = 1 := by
  have : IsEmpty (Fin (A.sig (tauE D τ)).2) := by rw [hp]; exact Fin.isEmpty'
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
  congr 1
  exact Subsingleton.elim _ _

theorem isCartanInv_one {A : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) (τ : D.what₂.Tau) : IsCartanInv (gramAt D A τ) 1 := by
  obtain ⟨cA, hc⟩ := exists_isCartanFrame A hA
  obtain ⟨s, hs, hs'⟩ := IP.Model.exists_cartan (hA (tauE D τ)).choose
    (J := Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2)
    (by rw [jpq_eq_one hp, Matrix.mul_one]) (by rw [jpq_eq_one hp, Matrix.conjTranspose_one]) (IP.Model.gramAt_unit A τ) (hc τ)
  have h2 : gramAt D A τ * s = gramAt D A τ := by
    conv_lhs => rw [← hc τ, Matrix.mul_assoc, hs']
    rw [← hc τ, jpq_eq_one hp]; simp
  have h3 : s = 1 := by
    have := congrArg ((gramAt D A τ)⁻¹ * ·) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (IP.Model.gramAt_unit A τ), Matrix.one_mul] using this
  exact h3 ▸ hs

theorem exists_defin {θ : InfFam D} (hθ : IsInfFam θ) {A : HSp D} (hA : A.SigOK) (hp : A.IsPosDef) :
    ∃ cA a, Defin θ A cA a := by
  obtain ⟨cA, hc⟩ := exists_isCartanFrame A hA
  obtain ⟨a, ha, -, ha'⟩ := exists_isMaj_frameInv_eq hθ (isCartanInv_one hA hp)
  refine ⟨cA, a, hθ, hA, hp, hc, isCartanInv_one hA hp, fun τ => by rw [jpq_eq_one hp]; simp, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (isMaj_iff hθ).1 ha τ
  conv_lhs => rw [← show frameInv θ A a τ = 1 from ha' τ, frameInv]
  calc _ = ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hε, diagonal_sign_mul_self]

theorem bcParam_rho {q : ℕ} (hq : q ≠ 0) (n : ℕ) : GlobalTheory.LGrp.bcParam n (LFun.Model.rhoU hq n) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have h := GlobalTheory.SphTheta.bcParam_map_mul 1 n (LFun.Model.rhoU hq n)
  simp only [one_mul, Multiset.map_id', LFun.Model.rhoU, ← zpow_neg] at h
  rw [h, Fin.sum_univ_eq_sum_range (fun k : ℕ => ({Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (k : ℤ)),
    Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ)) (n / 2)]
  rcases Nat.even_or_odd' n with ⟨d, rfl | rfl⟩
  · rw [GlobalTheory.SphTheta.str_even _ d _ (by push_cast; rfl), show 2 * d / 2 = d by omega, show 2 * d % 2 = 0 by omega]
    simp
  · rw [GlobalTheory.SphTheta.str_odd _ d _ (by push_cast; rfl), show (2 * d + 1) / 2 = d by omega, show (2 * d + 1) % 2 = 1 by omega]
    simp

theorem seg_eq_str {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : q ≠ 0)
    (h : Ideal.absNorm w.asIdeal = q ^ 2) (n : ℕ) :
    LFun.seg w 1 n = GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have hu : ∀ f : ℕ → ℂˣ, (Finset.range n).val.map f = ∑ i ∈ Finset.range n, ({f i} : Multiset ℂˣ) := fun f => by
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton ((Finset.range n).val.map f), Multiset.map_map]; rfl
  rw [GlobalTheory.SphTheta.str_eq_sum, Int.toNat_natCast, LFun.seg, hu, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  congr 1
  refine Units.ext ?_
  rw [one_mul, LFun.coe_npowU, LFun.npow, h, Units.val_zpow_eq_zpow_val, Units.val_mk0, Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Nat.cast_pow, ← Complex.cpow_intCast, ← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring

theorem lev_prinDat (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) = Formalism.L2.DIV.Kg D.sp.cm A.gram β Z := by
  refine le_antisymm (fun x hx => ⟨hx.1.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => ?_⟩)
    (Formalism.L2.DIV.Kg_le_lev subset_rfl (Finset.empty_subset _))
  have h1 := Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.1.1.2 PP) hP)
  have h2 : Formalism.L2.DIV.upperLeftBlock le_rfl (Formalism.L2.DIV.redFn β PP x) = 1 := congrFun (Subgroup.mem_bot.1 hx.2) ⟨PP, hP⟩
  have h3 := Formalism.L2.DIV.upper_block_val_submatrix le_rfl (Formalism.L2.DIV.blockTri_blkOf_le _ _ h1.2)
  refine Formalism.L2.DIV.mem_princAt.2 ⟨h1.1, Units.ext ?_⟩
  exact h3.symm.trans (congrArg Units.val h2)

end GlobalTheory.Core.Rk.Exh.Model

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem one_lt_norm (PP : Pl D.host.E) : (1 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
  exact_mod_cast GlobalTheory.LFun.one_lt_absNorm PP

theorem zinv_pos (PP : Pl D.host.E) (a b : ℕ) : 0 < zinv PP a b := by
  refine Finset.prod_pos fun n hn => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_norm PP) ?_))
  have := (Finset.mem_Ioc.1 hn).1
  omega

theorem zinv_mul (PP : Pl D.host.E) {a b c : ℕ} (h : a ≤ b) (h' : b ≤ c) : zinv PP a b * zinv PP b c = zinv PP a c :=
  Finset.prod_Ioc_consecutive _ h h'

theorem idx_vol (PP : Pl D.host.E) (k : ℕ) :
    idxQ PP (k + 1) * volOne PP (k + 1) * zinv PP D.R.t ((k + 1) * D.R.t) = zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) := by
  have h1 : D.R.t ≤ (k + 1) * D.R.t := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have e1 := zinv_mul PP (Nat.zero_le D.R.t) h1
  have e2 := zinv_mul PP (Nat.zero_le D.R.t) (h1.trans (Nat.le_add_left _ D.R.r))
  have p0 := (zinv_pos PP 0 D.R.t).ne'
  have p1 := (zinv_pos PP 0 D.R.r).ne'
  have p2 := (zinv_pos PP D.R.t ((k + 1) * D.R.t)).ne'
  have p3 : (Ideal.absNorm PP.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans (one_lt_norm PP)).ne'
  unfold idxQ volOne
  rw [← e1, ← e2]
  field_simp

theorem const_eq {c : Com D} {s s' : PiLocalization₂ D} (w : Twist D) (k : ℕ) (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (mR : Measure (GinfC s.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec) (L H H₀ : ℂ)
    (hH : H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) (h0 : dS w.S₀ s s' ≠ 0)
    (hd : dS (c.S : Set _) s s' = dS w.S₀ s s' * ((∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) : ℝ) : ℂ)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (L * H / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR =
      kapOf w k p m X mR φ v H₀ * L := by
  have e : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) =
      (∏ PP ∈ w.Q, idxQ PP (k + 1)) * (∏ PP ∈ w.Q, volOne PP (k + 1)) * ∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ => (idx_vol PP k).symm
  have n : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) ≠ 0 :=
    (Finset.prod_pos fun PP _ => zinv_pos PP _ _).ne'
  rw [e] at n
  have n1 : ((∏ PP ∈ w.Q, idxQ PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n2 : ((∏ PP ∈ w.Q, volOne PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n3 : ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul n
  have l : locQ c w k = (∏ PP ∈ w.Q, blockL c k PP) * ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) := by
    rw [locQ, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [kapOf, hd, e, l, hH, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

end GlobalTheory.ChainTw.Check

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffInh

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

section Empty

variable {P : Pl D → Prop}

theorem mem_GinfC_of_all (hP : ∀ v, P v) {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) : g ∈ GinfC S := by
  rw [grpOff, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hg
  rw [GinfC, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have e : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1 : Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P :=
    Ideal.Quotient.eq.1 ((hg i j).trans e.symm)
  have h2 := GlobalTheory.SelfDualAt.eq_zero_of_compFin (finPart D _) fun w => (Submodule.mem_iInf _).1 h1 ⟨w, hP w⟩
  rw [RingHom.map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Empty

end GlobalTheory.FinPl.OffInh

end
end

section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass

namespace GlobalTheory.MiS
open _root_.Formalism Formalism.IndefR Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}

def DcPtG {ex : Extra D L hT Gi Gl Kc Yd cX} (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

structure RealPack (ex : Extra D L hT Gi Gl Kc Yd cX) where

  R : Formalism.L2.RecT ex

  S : Formalism.L2.SG.SpectralTiesReal.STiesR R

  P : RowSideFamily ex

  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)

  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)

  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3

  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]

  Q : RealT R P Dcf Spf Zscf S Ks

attribute [instance] RealPack.fKs RealPack.nKs RealPack.aKs

variable {ex : Extra D L hT Gi Gl Kc Yd cX}

def HypAt (W : RealPack ex) : Prop :=
  Nonempty (Formalism.L2.SG.JoinSI.JoinSI W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl

abbrev cxW (W : RealPack ex) := W.Q.Rl.toCx3 W.Q.F

def LevHyp (W : RealPack ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (cxW W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (cxW W).EE, GUnit3 (cxW W) gE ∧ GEquiv3 W.P.A3 (cxW W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs

end GlobalTheory.MiS

end
end
