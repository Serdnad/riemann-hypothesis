module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle161
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceLastLevel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle162
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CutBP2
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem op_clm (Φ : E →L[ℂ] E') (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → E}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) {g : Mat k r} (hg : g ∈ GV k r) :
    Formalism.FourierDecayAlt.P.B4.op b X (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.op b X G g) := by
  unfold Formalism.FourierDecayAlt.P.B4.op
  have hd : DifferentiableAt ℝ (fun t : ℝ => G (Formalism.FourierDecayAlt.P.B4.cv b X t g)) 0 :=
    Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 b hG hX hg
  exact ((Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv

theorem ckOn_clm {m : ℕ∞} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CkOn m (GV k r) G) :
    CkOn m (GV k r) (fun h => Φ (G h)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', heq⟩ := hG g₀ hg₀
  refine ⟨U, fun h => Φ (f' h), hU, hg, ?_, fun g hgU hgV => by show Φ (G g) = Φ (f' g); rw [heq g hgU hgV]⟩
  exact (Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf'

theorem W_clm (Φ : E →L[ℂ] E') (w : List (Bool × Mat k r)) (hw : Formalism.FourierDecayAlt.P.B4.AllLie w) {G : Mat k r → E}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) :
    ∀ g ∈ GV k r, Formalism.FourierDecayAlt.P.B4.W w (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.W w G g) := by
  induction w generalizing G with
  | nil =>
    intro g _
    rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hw' : Formalism.FourierDecayAlt.P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hGw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G := Formalism.FourierDecayAlt.P.B4.ckOn_mono (by simp) hG
    have hG1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Formalism.FourierDecayAlt.P.B4.W w G) :=
      Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives w hw' 1 (by simpa [Nat.add_comm] using hG)
    rw [Formalism.FourierDecayAlt.P.B4.W_cons, Formalism.FourierDecayAlt.P.B4.W_cons,
      Formalism.FourierDecayAlt.P.B4.op_congr x.1 hx (fun h hh => ih hw' hGw h hh) g hg]
    exact op_clm Φ x.1 hx hG1 hg

theorem ccle_clm {A c : ℝ} {m : ℕ} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CCle A m G c) :
    CCle A m (fun h => Φ (G h)) (‖Φ‖ * c) := by
  obtain ⟨hk, hb⟩ := hG
  refine ⟨ckOn_clm Φ hk, fun u v hu hv hl g hg => ?_⟩
  have hw : Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr u v) :=
    Formalism.FourierDecayAlt.P.SliceLastLevel.allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1)
  have hlen : (Formalism.FourierDecayAlt.P.B4.lr u v).length = u.length + v.length := by simp [Formalism.FourierDecayAlt.P.B4.lr]
  have hGk : CkOn (((Formalism.FourierDecayAlt.P.B4.lr u v).length : ℕ) : ℕ∞) (GV k r) G :=
    Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) hk
  rw [Formalism.FourierDecayAlt.P.B4.dLR_eq, W_clm Φ _ hw hGk g hg, ← Formalism.FourierDecayAlt.P.B4.dLR_eq]
  have h1 := hb u v hu hv hl g hg
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg).le _
  calc gN g ^ A * ‖Φ (dLR u v G g)‖ ≤ gN g ^ A * (‖Φ‖ * ‖dLR u v G g‖) :=
        mul_le_mul_of_nonneg_left (Φ.le_opNorm _) hgN
    _ = ‖Φ‖ * (gN g ^ A * ‖dLR u v G g‖) := by ring
    _ ≤ ‖Φ‖ * c := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

end clm

section sum

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rw_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [rw_zero_fnE v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dLR_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (B.Mat k r)) :
    ∀ u : List (B.Mat k r), B.dLR u v (0 : B.Mat k r → E) = 0
  | [] => rw_zero_fnE v
  | X :: u => by
    show B.LdV X (B.dLR u v 0) = 0
    rw [dLR_zero_fnE v u]
    funext g
    simp [B.LdV]

theorem inCC_zero_fnE (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → (Wq →L[ℂ] Wp)) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => rfl⟩,
    fun u v _ _ _ g _ => ?_⟩
  rw [dLR_zero_fnE v u]
  simp

theorem inCC_finsum {A : ℝ} {m : ℕ} : ∀ {n : ℕ} (F : Fin n → Mat k r → (Wq →L[ℂ] Wp)),
    (∀ i, InCC A m (F i)) → InCC A m (fun g => ∑ i, F i g) := by
  intro n
  induction n with
  | zero =>
    intro F _
    have e : (fun g => ∑ i : Fin 0, F i g) = (0 : Mat k r → (Wq →L[ℂ] Wp)) := by
      funext g
      exact Fin.sum_univ_zero _
    rw [e]
    exact inCC_zero_fnE A m
  | succ n ih =>
    intro F h
    simp only [Fin.sum_univ_succ]
    obtain ⟨c₁, h₁⟩ := h 0
    obtain ⟨c₂, h₂⟩ := ih (fun i : Fin n => F i.succ) (fun i => h i.succ)
    exact ⟨c₁ + c₂, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h₁ h₂⟩

end sum

theorem shifted_decay : FpmShDecay := by
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' q f A A₀ d p₀ hf hA m
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  set Gp : B.Mat P.k P.r → ℂ := fun g => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ) with hGp
  have e : fpmSh q f A p₀ = fun g => ∑ i, (Gp g * c i g) • (f g).comp (L i) := by
    funext g
    ext v

    simp [fpmSh, hAe g, map_sum, map_smul, Finset.smul_sum, smul_smul, hGp]
  rw [e]
  refine inCC_finsum _ fun i => ?_
  set Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
  have hΦ : ∀ x, Φ x = x.comp (L i) := fun x => rfl
  have hgood : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq' ((2 * P.r + 2) * p₀ + d) (fun g => Gp g * c i g) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_mul le_rfl (Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow q.T.base.z q.T.base.z' p₀)
      (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (hc i))
  obtain ⟨K, -, hK⟩ := hgood.2 (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m
  obtain ⟨b, hb⟩ := hf m
  have hb' := ccle_clm Φ hb
  have hA' : A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) = A₀ := by
    push_cast; ring
  rw [← hA'] at hb'
  exact ⟨K * (‖Φ‖ * b), hK _ _ hb'⟩

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure ShiftAtR {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp (n₀ * (P.r + 1)) Ap
  polyM : PolyOp (n₀ * (P.r + 1)) Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAtR.iNp ShiftAtR.iIp ShiftAtR.iFp ShiftAtR.iNm ShiftAtR.iIm ShiftAtR.iFm

section pieces

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

def SwapTie (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') : Prop :=
  q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧
    q.T.base.μW = p.T.base.μW ∧ q.T.base.μN = p.T.base.μN ∧ q.T.base.μW' = p.T.base.μW' ∧
    q.ν' = p.ν' ∧ q.m₀ = p.m₀


open Classical in
def ptRep (p : KB.Pl P Wp Wq) (γ : C.LPt) : B.Mat P.k P.r :=
  if h : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g then h.choose else 1

end pieces

def WigEquiv {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, A (n * g * n') = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h ∈ UWset k r z, A (h * g) = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h' ∈ UWset k r z', A (g * h') = (π' h'⁻¹).comp ((A g).comp (π'' h')))

def WigUpper {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (n₀ : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, ‖A g‖ ^ 2 ≤ (Gf k r z z' g / Tz k r z') ^ n₀

def WigLower {k r : ℕ} {Wq Wqp Wqm : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (z z' : Fin (2 * r + k + 1) → ℂ) (b : ℝ) (n₀ : ℕ)
    (Ap : B.Mat k r → (Wqp →L[ℂ] Wq)) (Am : B.Mat k r → (Wqm →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ v : Wq,
    ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tz k r z' / Gf k r z z' g) ^ n₀ *
      (‖(ContinuousLinearMap.adjoint (Ap g)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am g)) v‖ ^ 2)

def CellIdSh : Prop :=
  ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq')
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ),
    SwapTie p q → WigEquiv p.T.base.z p.T.base.z' p.T.base.π' q.T.base.π' A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (A (ptRep p γ))

theorem ptRep_spec {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    ptRep p γ ∈ B.GV P.k P.r ∧ Gf P.k P.r p.T.base.z p.T.base.z' (ptRep p γ) = Gp p γ := by
  have hex : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g :=
    Formalism.FourierDecayAlt.P.Dx2.dFrameExists P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ p.hF hγ hG
  have hrep : ptRep p γ = hex.choose := by
    unfold ptRep
    rw [dite_eq_left hex]
  obtain ⟨hmem, hz, _⟩ := hex.choose_spec
  refine ⟨by rw [hrep]; exact hmem, ?_⟩
  rw [hrep, Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ γ hz]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cutoff_exists {H : B.Mat k n → (Wq →L[ℂ] Wp)} (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) {Cs : Set (B.Mat k n)}
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) {c0 : ℂ} (hc0 : c0 ≠ 0) :
    ∃ Ht : B.Mat k n → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k n) Ht ∧ (∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) ∧
      ∀ g ∈ B.GV k n, dist (Dmin k n z z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4 → Ht g = H g := by
  set l : Fin (n + 2) := ⟨i, by omega⟩ with hl
  have hc : 0 < ‖c0‖ := norm_pos_iff.mpr hc0
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc0
  have hDc : Continuous (fun g : B.Mat k n => Dmin k n z z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous
  refine ⟨fun g => χD (Dmin k n z z' g l) • H g, ?_, ?_, ?_⟩
  · intro g0 hg0
    by_cases hmem : Dmin k n z z' g0 l ∈ tsupport χD
    · have hne : Dmin k n z z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hL g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k n z z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l)).contDiffOn).smul hf'
      · show χD (Dmin k n z z' g l) • H g = χD (Dmin k n z z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k n z z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k n z z' g l) • H g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  · intro g hg hgC
    show χD (Dmin k n z z' g l) • H g = 0
    rw [hS g hg hgC, smul_zero]
  · intro g _ hd
    show χD (Dmin k n z z' g l) • H g = H g
    rw [hχ1 _ (le_of_lt hd), one_smul]

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
end
