module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle157
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLedPart
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle149
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.MuTuOfTuSize
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.ConcNP
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoinP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.ConcNWeight
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.normalizedVector_translates_prime_order_integral : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  first | exact @GlobalTheory.MomN.transPrime_int | exact GlobalTheory.MomN.transPrime_int | (intros; apply GlobalTheory.MomN.transPrime_int <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l))
    (l0 : TC.Law0 I l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.tw I l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching I hI l Z l0 u a
           lat_co := GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan I hI l Z l0 u a w z hz, GlobalTheory.T.exists_integralHyperplaneForm_of_localCoords_integral I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField

namespace GlobalTheory.Fc

theorem realTied_setDiv {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (H : Formalism.L2.Theta.RealTied D) : Formalism.L2.Theta.RealTied (setDiv D N h) :=
  ⟨H.cdScale, H.dsig, H.dsig_all, H.vol⟩

theorem built_val (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd) (κ : Par) (D : D7) (O : Obj D) (c : ℝ) (b : Bd D O c)
    (hb : Built Q Lk κ D O c b) :
    Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧ O.L.sc.eps = κ.eps ∧
      (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)} := by
  refine Built.ind (R := fun D O _ _ => Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧
      O.L.sc.eps = κ.eps ∧ (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}) ?_ hb
  intro K β _ _ h0 _ _
  obtain ⟨h1, h2, h3, h4, -⟩ := h0
  rw [← h1, ← h2, ← h3, ← h4]
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact ⟨hv, β.p.pt_canon β.canon, rfl, rfl, congrArg Scale.eps β.sc, β.p.pt.xa.h_eq,
    ⟨realTied_setDiv _ _ β.c.real⟩, ⟨⟨(_, _), hv.Del_eq, hv.eta_eq⟩⟩⟩

end GlobalTheory.Fc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h


open GlobalTheory.EX.DC in
theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb


open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in
theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem tameDistinctF_iff {eps : ℝ} (Fm : FamP eps) : DC.TameDistinctF Fm ↔ Formalism.MainNotions.TameDistinctF Fm := by
  unfold DC.TameDistinctF Formalism.MainNotions.TameDistinctF
  simp only [DQ.tameDistinct_iff]

theorem dGamDvdF_iff {eps : ℝ} (Fm : FamP eps) : DC.DGamDvdF Fm ↔ Formalism.MainNotions.DGamDvdF Fm := Iff.rfl

theorem codeUpF_iff {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : DC.CodeUpF Fm C0 CH ↔ Formalism.MainNotions.CodeUpF Fm C0 CH := Iff.rfl

theorem working_classes_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm) ∧ (Formalism.MainNotions.Des (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9) 3 Fm ↔ W3 𝒜 Fm)) ∧ (∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → DC.DesignChoices (DC.WithTw 𝒜) 3 cT) → Formalism.MainNotions.MinkDiv → Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw 𝒜) 3 cT) := by
  refine ⟨fun 𝒜 eps Fm => ?_, fun 𝒜 cT h hM => ?_⟩
  · have e1 : Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧
        Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm := by
      simp only [Formalism.MainNotions.WithTw, Formalism.MainNotions.WithSm, W1, tameDistinctF_iff, dGamDvdF_iff]
    refine ⟨e1, ?_⟩
    simp only [Formalism.MainNotions.Des, W3, ← e1]
  · obtain ⟨ε0, h0, h⟩ := h hM
    refine ⟨ε0, h0, fun eps he hle K => ?_⟩
    obtain ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h eps he hle K
    exact ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, (tameDistinctF_iff Fm).1 h15, h16,
      (codeUpF_iff Fm 3 CH).1 h17, h18⟩

end GlobalTheory.Fc
end

section

noncomputable section

namespace GlobalTheory.Top.Irr

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin

theorem tieAdmG_holds (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem linkIRR_of_join_ex (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c) (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧ AllJoinA A ∧ admLq (Fm.D x i) ∧
        CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧ SizesRec (Fm.D x i) x Fm.ez Cs) :
    LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  refine linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨max x0 ((3 / 2 : ℝ) ^ (1 / Fm.ez)), fun x hx i => ?_⟩
  obtain ⟨A, hT, hJ, hL, hC, hS⟩ := hx0 x (le_trans (le_max_left _ _) hx) i
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_max_right _ _) hx
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  exact ⟨A, hT, hC, weight_of_join hL (tieAdmG_holds _) (rangeW_of_sizes hS hxe) hJ, hS⟩

end

section
open Formalism.BasicNotions Formalism.MainNotions

theorem sizesRec_at {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x) (i : Fm.Ix x) {Cs : ℝ}
    (hCs : 6 ≤ Cs) : Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez Cs := by
  obtain ⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hε0 : 0 < eps := hLe ▸ (Fm.L x i).sc.eps_pos
  have hε1 : eps < 1 / 52 := hLe ▸ (Fm.L x i).sc.eps_lt
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hLz : (Fm.L x i).sc.ez = Fm.ez := Fm.toFamCore.L_ez x i
  have hz0 : 0 < Fm.ez := div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hzle : Fm.ez ≤ eps := div_le_self hε0.le Fm.toFamCore.one_le_J
  simp only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG

  have hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by simp [Ranks.f]
  have hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.f_le_k
    simpa [Ranks.f, Ranks.n] using this
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    simpa [Ranks.f, Ranks.n] using this
  have hm2 : 2 ≤ (Fm.D x i).R.m := (Fm.D x i).R.two_le_m
  have hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r := by unfold Ranks.r; omega
  have hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k := by unfold Ranks.r; omega

  have h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h56 : x ^ (5 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h6 : x ^ (6 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 hCs
  have h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx4 4
    norm_num at this ⊢; linarith
  have hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have h0 : 0 ≤ x ^ (5 : ℝ) := Real.rpow_nonneg hx0.le _
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0
    linarith
  have hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) := le_trans hK.2 h5
  have hkl : (256 : ℝ) ≤ (Fm.D x i).R.k := le_trans (le_trans hx4p h4) hK.1
  have hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k := by exact_mod_cast hfk
  have hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast hmf
  have hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := by exact_mod_cast hr2k
  have hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r := by exact_mod_cast hrk

  have hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpos6 : 0 < x ^ (Fm.ez / 6) := Real.rpow_pos_of_pos hx0 _
  have hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ) := by
    have hl := hQD.1
    have hq0 : (0 : ℝ) < (Fm.D x i).host.q := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.q) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.q := Real.exp_log hq0
  have hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ) := by
    have hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d := le_trans hεq hQD.2.2.2.1
    have hd0 : (0 : ℝ) < (Fm.D x i).host.d := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.d) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.d := Real.exp_log hd0
  intro j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hg := (hG j j).1
    have hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hb0 : 0 ≤ Real.exp (x ^ eps) := (Real.exp_pos _).le
    have hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps) := by
      have : (1 : ℝ) ≤ (Fm.D x i).R.k := by linarith
      nlinarith
    have hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      rw [show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]
    rw [hsc] at hg
    have hze : x ^ Fm.ez ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 hzle
    refine le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_
    rw [hb]
    exact le_trans (pow_le_pow_left₀ hb0 hkb 8) hg
  ·
    rw [← Real.rpow_two]
    have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
    have hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f := by rw [hf]; linarith
    exact le_trans h2 (le_trans hN.1 hnf)
  · exact le_trans hfkR (le_trans hkx h56)
  · exact le_trans hmfR (le_trans hfkR (le_trans hkx h56))
  ·
    have h256 : 256 ≤ (Fm.D x i).R.k := by exact_mod_cast hkl
    omega
  · have h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ) := mul_le_mul_of_nonneg_left hkx (by norm_num)
    exact le_trans hr2kR (le_trans h2k (le_trans hx65 h6))
  · rw [Nat.cast_min]
    exact le_min hq hd

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

end GlobalTheory.Top.Irr
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

theorem _root_.GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.VecP χ ∧ B.LatAll ∧ ∀ a b, B.ThZeroMem a b := by
  first | exact @GlobalTheory.NatFamily.family | exact GlobalTheory.NatFamily.family | (intros; apply GlobalTheory.NatFamily.family <;> assumption)
end
