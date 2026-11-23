module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]


open MeasureTheory NumberField Matrix Finset in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
theorem _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) {γ : _root_.GlobalTheory.FlagMeas.MatInf E j}
    (hγ : γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ) (g : _root_.GlobalTheory.FlagMeas.MatInf E j) :
    _root_.GlobalTheory.FlagBase.latAt E j Λ (γ * g) = _root_.GlobalTheory.FlagBase.latAt E j Λ g := by
  obtain ⟨γ', hγΛ, hγ'⟩ := hγ
  have hγw : ∀ w : InfinitePlace E,
      Matrix.of (γ w) = (γ' : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    ext a b
    simp [hγ' w a b]
  have hinv : ∀ w : InfinitePlace E, (Matrix.of (γ w))⁻¹ =
      ((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    rw [hγw]
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  have key : ∀ (w : InfinitePlace E) (y : Fin j → E),
      (Matrix.of ((γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) =
        (Matrix.of (g w))⁻¹ *ᵥ
          (fun a => w.embedding ((((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a)) := by
    intro w y
    rw [_root_.GlobalTheory.OrbitTerm.of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    congr 1
    funext a
    exact (RingHom.map_mulVec w.embedding _ y a).symm
  unfold _root_.GlobalTheory.FlagBase.latAt
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y, ?_, ?_⟩
    · rw [← hγΛ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
      exact hy
    · funext w
      exact (key w y).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(γ' : Matrix (Fin j) (Fin j) E) *ᵥ z, (hγΛ z).mpr hz, ?_⟩
    funext w
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

end GlobalTheory.FlagBase.Test
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
private theorem inv_mul_conj_mul_cancel {n : Type*} [Fintype n] [DecidableEq n] (A B C D γ a : Matrix n n ℂ)
    (hγ : IsUnit γ.det) (ha : IsUnit a.det) :
    A⁻¹ * (a * B)⁻¹ * γ * (γ⁻¹ * a * γ * C) * D = A⁻¹ * B⁻¹ * γ * C * D := by
  rw [Matrix.mul_inv_rev]
  have h1 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγ
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc A⁻¹ * (B⁻¹ * a⁻¹) * γ * (γ⁻¹ * a * γ * C) * D
      = A⁻¹ * B⁻¹ * (a⁻¹ * ((γ * γ⁻¹) * a)) * γ * C * D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, h2, Matrix.mul_one]


open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.pairMaj_stabAct {k r : ℕ} (γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : IsUnit γ.det)
    (ha : IsUnit a.det) (b : ℝ) (p : _root_.Formalism.MainNotions.S.PairSp k r) : _root_.GlobalTheory.CellAmp.pairMaj γ b (_root_.Formalism.MainNotions.S.stabAct γ a p) = _root_.GlobalTheory.CellAmp.pairMaj γ b p :=
  congrArg (fun M => _root_.Formalism.FourierDecayAlt.B.gN M ^ (-b))
    (inv_mul_conj_mul_cancel (of p.1.1) (of p.1.2) (of p.2.2) (of p.2.1) γ a hγ ha)

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) : _root_.Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold _root_.Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp [_root_.Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [_root_.Formalism.QuantumDeterminants.eI]))


open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.cellData_open {k r : ℕ} (L : _root_.Formalism.MainNotions.S.LocBessel k r) (μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) (hinv : g⁻¹ * g = 1)
    (hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r L.z L.z' g) (hm : _root_.Formalism.FourierDecayAlt.C2.IsMonomial (_root_.Formalism.QuantumDeterminants.Zhat k r L.z L.z' g))
    (hR : _root_.Formalism.MainNotions.S.RStab k r g = {1}) :
    _root_.GlobalTheory.CellAmp.CellData L μG g (Measure.dirac (fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j)) μG (_root_.Formalism.MainNotions.S.pairMeas L) := by
  have hone : (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) = 1 := rfl
  refine ⟨hg, hG, hm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    subst ha
    rw [Matrix.mul_one, hinv]
    unfold _root_.Formalism.QuantumDeterminants.psi
    rw [_root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz.1, _root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz'.1]
  · refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · rw [hR, Measure.dirac_apply]
      simp only [Set.mem_singleton_iff, Set.indicator_apply, Set.mem_setOf_eq]
      rw [hone]
      simp
    · intro s hs
      rw [hR, Set.mem_singleton_iff] at hs
      subst hs
      have hid : _root_.Formalism.QuantumDeterminants.lmulM (k := k) (r := r) 1 = id := funext fun x => by
        unfold _root_.Formalism.QuantumDeterminants.lmulM
        rw [Matrix.one_mul]
        rfl
      rw [hid, Measure.map_id]
  · intro f hf
    have hstab : ∀ x, _root_.Formalism.MainNotions.S.stabAct g (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) x = x := by
      intro x
      unfold _root_.Formalism.MainNotions.S.stabAct
      rw [hone, Matrix.one_mul, Matrix.mul_one, hinv, Matrix.one_mul]
      rfl
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hstab]
  · intro f hf
    rw [Measure.map_congr (ae_eq_dirac _)]
    erw [Measure.map_const]
    rw [measure_univ, one_smul]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hone, Matrix.mul_one, hinv, hone, Matrix.one_mul]
    rfl

end GlobalTheory.CellAmp.Model

end
end

section

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants

noncomputable section

open Classical

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end place

def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ

end

end GlobalTheory.ThA
end

section

noncomputable section

open scoped Classical

namespace GlobalTheory.LoopC

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev Fg (T : D.host.E) : Type := LFlag (hS D) D.R.rS T

abbrev Fb (u : D.what₂.Word) : Type := FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)

abbrev LatW : Type := Submodule (𝓞 D.host.E) (D.sp.X 0).V

def IsBase (u : D.what₂.Word) (F0 : Fb D u) : Prop := F0.e = D.sp.hypE ∧ F0.z = D.zmOf u

def seen {T : D.host.E} (F : Fg D T) (M : LatV D) : LatW D :=
  (M ⊔ toO (hS D) (Xsp F)).comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E))

def sat (L P : LatW D) : LatW D :=
  L ⊓ (Submodule.span D.host.E (P : Set (D.sp.X 0).V)).restrictScalars (𝓞 D.host.E)

def perpE (P : LatW D) : Submodule D.host.E (D.sp.X 0).V := ⨅ p ∈ P, LinearMap.ker ((D.sp.X 0).hT p)

def perpW (L P : LatW D) : LatW D := L ⊓ (perpE D P).restrictScalars (𝓞 D.host.E)

def idxW (A B : LatW D) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def rkW (P : LatW D) : ℕ := finrank D.host.E (Submodule.span D.host.E (P : Set (D.sp.X 0).V))

def detW (P : LatW D) : ℝ := latDetH (D.sp.X 0).hT P

def SubOK (L P : LatW D) (s : ℕ) (Q : ℝ) : Prop :=
  P ≤ L ∧ rkW D P = D.R.k - s ∧ 1 ≤ idxW D (sat D L P) P ∧ (idxW D (sat D L P) P : ℝ) ≤ Q ∧ detW D P ≤ Q

def N1 (Λ : LatV D) {T : D.host.E} (F : Fg D T) : Set ((hS D).V ≃ₗ[D.host.E] (hS D).V) :=
  {n | n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b}

def YS : LatV D :=
  Submodule.span (𝓞 D.host.E)
    {y | ∃ (a : Fin D.R.rS) (x : D.host.E),
      x ∈ (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧
        y = x • D.sp.hypF a}

def IsSplit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) : Prop :=
  Λ = XS D F0 ⊔ (Λ ⊓ toO (hS D) (Wb D)) ⊔ YS D

def FixFr {T : D.host.E} (F : Fg D T) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧ (∀ b, n (frame F b) = frame F b) ∧ ∀ x ∈ orth (hS D) (Xsp F), n x - x ∈ Xsp F

def FrSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsTermF D Λ F F' ∧ ZEquiv (ZhatL F F') Z ∧ P ≤ seen D F (Thp Λ F F')}

def cntFr (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : ℕ∞ :=
  cntCl (FrSet D Λ F T' Z P) (TEqv D Λ F)

def ExSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧ P ≤ seen D F (Thp Λ F F')}

def FixSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D)
    (φ : P →ₗ[𝓞 D.host.E] (hS D).V) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧
    ∀ (p : P) (b : Fin (D.R.rS + 1)), (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0}

def IsWcomp (P : LatW D) (x : (hS D).V) (w : (D.sp.X 0).V) : Prop :=
  w ∈ perpE D P ∧ ∀ σ ∈ perpE D P, (hS D).hT (D.sp.iXY 0 σ) x = (D.sp.X 0).hT σ w

def Gmat (T T' : D.host.E) (Z : GramM D) : D.host.E :=
  leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) -
    T * T' * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))

def rowMinor (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) : D.host.E :=
  ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det

def QOK (u u' : D.what₂.Word) (Z : GramM D) (Q : ℝ) : Prop :=
  1 ≤ Q ∧ D.host.rdE ^ (2 * D.R.f * D.R.rS) ≤ Q ∧
  (∃ b₀, rowMinor D Z b₀ ≠ 0 ∧ ∏ τ, ‖embS D τ (rowMinor D Z b₀)‖ ^ 2 ≤ Q) ∧
  Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z ≠ 0 ∧
  ∏ τ, ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖ ≤ Q

def fixB (s : ℕ) (N De Q : ℝ) : ℝ :=
  9 ^ (s * D.R.f) * (De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) * Q ^ (2 * D.R.rS ^ 2)

def frB (s : ℕ) (N De Q : ℝ) : ℝ := N ^ (2 * D.R.rS) * De ^ D.R.rS * fixB D s N De Q

def glueSet (u : D.what₂.Word) (L' : LatW D) : Set (LatV D) :=
  {L | L.FG ∧ spanE (hS D) L = Wb D ∧ dualIn (hS D) L = L ∧ D.zmOf u ∈ L ∧
    (∀ c : D.host.E, c • D.zmOf u ∈ L → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
    L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) = L'}

end GlobalTheory.LoopC

end
end
