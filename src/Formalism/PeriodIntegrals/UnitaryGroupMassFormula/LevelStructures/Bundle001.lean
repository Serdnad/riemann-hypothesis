module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

variable {D : D7}

def idxS (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxHp (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxH (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def HaarIdxLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), muSv X w p = (idxS X hb w p : ℝ) * muSvpp X hb w p

def HaarIdxGlob : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, muHf X w = (idxH X hb w : ℝ) * muHfpp X hb w

def LocLevi : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), idxS X hb w p = idxHp X hb w p

def GlobProd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, idxH X hb w = ∏ p : TypX X, idxHp X hb w p

def ConjugateLevelLeMaximalCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, K2u X hb w ⊆ (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

theorem ratioH_of (h1 : HaarIdxLoc) (h2 : HaarIdxGlob) (h3 : LocLevi) (h4 : GlobProd) : RatioH := by
  intro D X hb hK hM hL w
  rw [h2 X hb hK hM hL w, h4 X hb hK hM hL w]
  simp only [h1 X hb hK hM hL w, h3 X hb hK hM hL w, Finset.prod_mul_distrib]
  push_cast
  ring

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

def CMInst : Prop :=
  ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J

def FrameStd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ T : X.B.I.F,
    (frameOf X w).IsStd X.B.I.cm.sig X.B.I.J T

def LatAdapted : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ ΛX ΛW ΛY : Set (Fin X.B.I.n → X.B.I.E),
    Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) ΛX ΛW ΛY ∧
    Kf X.B.I.cm.sig X.B.I.J (ΛX ∪ ΛW ∪ ΛY) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdNH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word),
    IsProdNH X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (X.measW w).μSf (X.measW w).μNf (X.measW w).μHf

def GlobFromParts : Prop := LevelSAll → CMInst → FrameStd → LatAdapted → ProdNH → GlobLevelS

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

def KSpCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsCompact (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def KSpOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsOpen (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

theorem typedNe_of (h1 : KSpCompact) (h2 : KSpOpen) : TypedNe := by
  intro D X hb _ _ w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have hne : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).Nonempty :=
    ⟨1, (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem⟩
  unfold muSv
  exact (ENNReal.toReal_pos (hH.toIsOpenPosMeasure.open_pos _ (h2 X w p) hne)
    (hH.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (h1 X w p)).ne).ne'

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Proj

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem conjTensor_involutive (hσ : ∀ x, σ (σ x) = x) (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem hermForm_conj_symm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR Formalism.UG.hform

  simp only [map_sum, map_mul, conjTensor_involutive hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hJ' : sigR R σ (JR R J j i) = JR R J i j := by
    simp only [JR, Matrix.map_apply, conjTensor_incl, hJ]
  rw [hJ']
  ring

theorem hR_sum_smul_left' {ι : Type} (s : Finset ι) (d : ι → R ⊗[F] E) (v : ι → Fin n → R ⊗[F] E)
    (y : Fin n → R ⊗[F] E) : hR R σ J (∑ i ∈ s, d i • v i) y = ∑ i ∈ s, sigR R σ (d i) * hR R σ J (v i) y := by
  induction s using Finset.cons_induction with
  | empty => simp [hR_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, hR_add_left, hR_smul_left, ih]

def hl (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' := hermForm_add_right_bis R σ J x
  map_smul' := fun c y => by rw [hermForm_smul_right_alt]; rfl

variable {r : ℕ} (P : Frame E n r) (c : R ⊗[F] E)

def piRest : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  (∑ a, (hl (σ := σ) (J := J) (ratV (F := F) R (P.f a))).smulRight (ratV (F := F) R (P.e a))) +
  (∑ a, (hl (σ := σ) (J := J) (ratV (F := F) R (P.e a))).smulRight (ratV (F := F) R (P.f a))) +
  c • (hl (σ := σ) (J := J) (ratV (F := F) R P.z)).smulRight (ratV (F := F) R P.z)

def piW : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) := LinearMap.id - piRest (σ := σ) (J := J) P c

theorem piRest_apply (v : Fin n → R ⊗[F] E) : piRest (σ := σ) (J := J) P c v =
    (∑ a, hR R σ J (ratV (F := F) R (P.f a)) v • ratV (F := F) R (P.e a)) +
    (∑ a, hR R σ J (ratV (F := F) R (P.e a)) v • ratV (F := F) R (P.f a)) +
    (c * hR R σ J (ratV (F := F) R P.z) v) • ratV (F := F) R P.z := by
  simp [piRest, hl, smul_smul]

theorem piW_add_rest (v : Fin n → R ⊗[F] E) :
    piW (σ := σ) (J := J) P c v + piRest (σ := σ) (J := J) P c v = v := by
  simp [piW]

structure FrameTab (T : F) : Prop where
  ee : ∀ a b, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
  ef : ∀ a b, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
  fe : ∀ a b, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.e b)) = if a = b then 1 else 0
  ff : ∀ a b, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
  ez : ∀ a, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
  fz : ∀ a, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
  ze : ∀ a, hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R (P.e a)) = 0
  zf : ∀ a, hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R (P.f a)) = 0
  zz : c * hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
  hσ : ∀ x, σ (σ x) = x
  hJ : ∀ i j, σ (J j i) = J i j

def InW (v : Fin n → R ⊗[F] E) : Prop :=
  (∀ a, hR R σ J (ratV (F := F) R (P.e a)) v = 0) ∧ (∀ a, hR R σ J (ratV (F := F) R (P.f a)) v = 0) ∧
    hR R σ J (ratV (F := F) R P.z) v = 0

variable {P c} {T : F}

theorem piW_inW (ht : FrameTab (σ := σ) (J := J) P c T) (v : Fin n → R ⊗[F] E) :
    InW (σ := σ) (J := J) P (piW (σ := σ) (J := J) P c v) := by
  have key : (∀ b, hR R σ J (ratV (F := F) R (P.e b)) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R (P.e b)) v) ∧
      (∀ b, hR R σ J (ratV (F := F) R (P.f b)) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R (P.f b)) v) ∧
      hR R σ J (ratV (F := F) R P.z) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R P.z) v := by
    refine ⟨fun b => ?_, fun b => ?_, ?_⟩ <;>
      rw [piRest_apply, hermForm_add_right_bis, hermForm_add_right_bis, hermForm_sum_right_alt, hermForm_sum_right_alt,
        hermForm_smul_right_alt]
    · simp [ht.ee, ht.ef, ht.ez]
    · simp [ht.fe, ht.ff, ht.fz]
    · simp only [ht.ze, ht.zf, mul_zero, Finset.sum_const_zero, zero_add]
      linear_combination (hR R σ J (ratV (F := F) R P.z) v) * ht.zz
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;>
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, hermForm_sub_right, h1, h2, h3, sub_self]

theorem piRest_inW (ht : FrameTab (σ := σ) (J := J) P c T) {v : Fin n → R ⊗[F] E}
    (hv : InW (σ := σ) (J := J) P v) : piRest (σ := σ) (J := J) P c v = 0 := by
  rw [piRest_apply]
  simp [hv.1, hv.2.1, hv.2.2]

theorem piW_inW_eq (ht : FrameTab (σ := σ) (J := J) P c T) {v : Fin n → R ⊗[F] E}
    (hv : InW (σ := σ) (J := J) P v) : piW (σ := σ) (J := J) P c v = v := by
  simp [piW, piRest_inW ht hv]

theorem piRest_e (ht : FrameTab (σ := σ) (J := J) P c T) (b : Fin r) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
  rw [piRest_apply]
  simp [ht.fe, ht.ee, ht.ze]

theorem piRest_f (ht : FrameTab (σ := σ) (J := J) P c T) (b : Fin r) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  rw [piRest_apply]
  simp [ht.ff, ht.ef, ht.zf]

theorem piRest_of_frameTab (ht : FrameTab (σ := σ) (J := J) P c T) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  rw [piRest_apply]
  simp [ht.fz, ht.ez, ht.zz]

theorem piW_X (ht : FrameTab (σ := σ) (J := J) P c T) {x : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) : piW (σ := σ) (J := J) P c x = 0 := by
  have h : spanR (F := F) R P.e Set.univ ≤ LinearMap.ker (piW (σ := σ) (J := J) P c) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simp [piW, piRest_e ht b]
  exact h hx

theorem inW_left (ht : FrameTab (σ := σ) (J := J) P c T) {a : Fin n → R ⊗[F] E}
    (ha : InW (σ := σ) (J := J) P a) (y : Fin n → R ⊗[F] E) :
    hR R σ J a (piRest (σ := σ) (J := J) P c y) = 0 := by
  have h1 : ∀ i, hR R σ J a (ratV (F := F) R (P.e i)) = 0 := fun i => by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.1 i, map_zero]
  have h2 : ∀ i, hR R σ J a (ratV (F := F) R (P.f i)) = 0 := fun i => by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.2.1 i, map_zero]
  have h3 : hR R σ J a (ratV (F := F) R P.z) = 0 := by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.2.2, map_zero]
  rw [piRest_apply, hermForm_add_right_bis, hermForm_add_right_bis, hermForm_sum_right_alt, hermForm_sum_right_alt,
    hermForm_smul_right_alt]
  simp [h1, h2, h3]

theorem inW_right (ht : FrameTab (σ := σ) (J := J) P c T) {a : Fin n → R ⊗[F] E}
    (ha : InW (σ := σ) (J := J) P a) (y : Fin n → R ⊗[F] E) :
    hR R σ J (piRest (σ := σ) (J := J) P c y) a = 0 := by
  rw [piRest_apply, hR_add_left, hR_add_left, hR_sum_smul_left', hR_sum_smul_left', hR_smul_left]
  simp [ha.1, ha.2.1, ha.2.2]

theorem X_left {x : Fin n → R ⊗[F] E} (hx : x ∈ spanR (F := F) R P.e Set.univ) {a : Fin n → R ⊗[F] E}
    (ha : ∀ b, hR R σ J (ratV (F := F) R (P.e b)) a = 0) : hR R σ J x a = 0 := by
  exact hR_span_perp (R := R) (σ := σ) (J := J) P a ha x hx

end Proj

end MassDataLevelSSteps
end
end
