module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF

@[expose] public section

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.LiveModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))

section Emb
open GlobalTheory.MixModel
variable {D : D7}

theorem gram_pos {E : Type} [Field E] [NumberField E] [StarRing E] (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n : ℕ) :
    (Examples₂.posSpace hs n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply hs n (fun _ => false) n 0 i j).trans ?_
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact (if_pos rfl).trans (by simp [Examples₂.sgn])
  · rw [Matrix.one_apply_ne h]; exact if_neg h

theorem rk_top (D : D7) : D.sp.X'.rank + 1 = (D.sp.X D.R.m).rank := by
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have h3 : 0 < D.R.N D.R.m := by
    have := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N]; omega
  omega

def topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1) :
    OrthDec (D.sp.X D.R.m) D.sp.X' (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1) where
  iA := Matrix.of fun b a => if (a : ℕ) = b then 1 else 0
  iB := Matrix.of fun b _ => if D.sp.X'.rank = b then 1 else 0
  isoA := by
    have := rk_top D
    rw [hG, hG', Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have : ¬ (i : ℕ) = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  isoB := by
    have := rk_top D
    rw [hG, Matrix.mul_one]
    funext i j
    have h : (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1).gram i j = 1 := by
      rw [gram_pos, Subsingleton.elim (α := Fin 1) i j, Matrix.one_apply_eq]
    rw [h, Matrix.mul_apply, Finset.sum_eq_single (⟨D.sp.X'.rank, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp
    · intro b _ hb
      have : ¬ D.sp.X'.rank = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  orth := by
    rw [hG, Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := j.2
    by_cases hb : D.sp.X'.rank = b
    · have : ¬ (j : ℕ) = b := by omega
      simp [this]
    · simp [hb]
  rank_add := rk_top D

theorem iXm_eq (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
    D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (b a) : iXm D b a = if (a : ℕ) = b then 1 else 0 := by
  have h0 := rk_top D
  have h1 := rankP D
  have ha := a.2
  have e : ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm (Pi.single a 1)) =
      D.sp.X'.frame (Fin.cast h1.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    simp [Finsupp.single_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e, hi _ ⟨a, by omega⟩ rfl]
  simp [Finsupp.single_apply, Fin.ext_iff]

theorem isEmbTop_topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (c : D.host.E) : IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0)
      ((topDec hG hG').emb.comp (MonoidHom.inl _ _)) := by
  intro h
  have h0 := rk_top D
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have eA : (iXm D).map (incA D) = ((topDec hG hG').jA).reindex (finCongr h2) (finCongr h1) := by
    ext b a
    simp [iXm_eq hi, OrthDec.jA, rat, topDec]
  constructor
  · rw [eA]
    have := (topDec hG hG').emb_jA h 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M _ _) this
  · have := (topDec hG hG').emb_jB h 1
    rw [mt_one, Matrix.mul_one] at this
    funext b
    have e := congrFun (congrFun this (Fin.cast h2.symm b)) (0 : Fin 1)
    have ez : (fun a : Fin (D.R.N D.R.m) => incA D (if a.1 + 1 = D.R.N D.R.m then c else 0)) =
        fun a => (topDec hG hG').jB (Fin.cast h2.symm a) (0 : Fin 1) * incA D c := by
      funext a
      have : (a.1 + 1 = D.R.N D.R.m) ↔ D.sp.X'.rank = a := by omega
      show _ = incA D (if D.sp.X'.rank = a then 1 else 0) * incA D c
      rw [← map_mul]
      by_cases ha : D.sp.X'.rank = a
      · rw [if_pos ha, if_pos (this.2 ha), one_mul]
      · rw [if_neg ha, if_neg (fun h => ha (this.1 h)), zero_mul]
    have ez' := congrFun ez b
    rw [ez, ez', ← e]
    refine Eq.trans ?_ (congrArg (· * incA D c) Matrix.mul_apply).symm
    refine Eq.trans ?_ (Finset.sum_mul _ _ _).symm
    refine Fintype.sum_equiv (finCongr h2.symm) _ _ fun x => ?_
    exact (mul_assoc _ _ _).symm
end Emb


end GlobalTheory.AdForm.LiveModel
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

variable {a : XPart D u} {b : YPart a}

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end
end

section

noncomputable section
open Formalism.BasicNotions GlobalTheory.SeeSaw GlobalTheory.QPl
namespace GlobalTheory.QTw
variable {D : D7} {c : Comm D} {t : Tup c}

def resc (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * (s (j + 1) γ)⁻¹) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

def QPinU (v : VCom c) (w : VTup t) : Prop :=
  ∃ (w₀ : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ QPin v w₀ ∧ w = resc w₀ s

end GlobalTheory.QTw
end
end

section

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def PrimTop {c : Comm D} (tP : Finset (GlobalTheory.FinPl.Pl D)) (ζ₀ : Fin c.Lz.rank → D.host.E) : Prop :=
  ∀ p, p ∉ tP → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = p),
    a • ratV (vecB (c.oT D.R.m rfl) ζ₀) ∈ GlobalTheory.FinPl.latV (c.X D.R.m) (c.x D.R.m).L (· = p) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = p)

end GlobalTheory.MiTop

end
end
