module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.QPl GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw.RescTest
variable {D : D7} {c : Comm D} {t : Tup c}

theorem root_ne {z : ℂ} (h : ∃ n : ℕ, 0 < n ∧ z ^ n = 1) : z ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  rintro rfl
  simp [hn.ne'] at h

theorem comb_lc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e f = Finsupp.linearCombination ℂ (fun x => heisO ψ S T x f) e := rfl

theorem comb_smul_left (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  rw [comb_lc, comb_lc, map_smul]

theorem trc_lc {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc e f = Finsupp.linearCombination ℂ (fun g => rTrans g f) e := rfl

theorem trc_smul_left {V : HSp D} (a : ℂ) (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (a • e) f = a • trc e f := by
  rw [trc_lc, trc_lc, map_smul]

theorem biComb_smul2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u x
  simp only [biComb, comb_smul_left, Pi.smul_apply, smul_eq_mul]
  have : (fun u' => b * comb ψ S A' e' (C u') x) = b • fun u' => comb ψ S A' e' (C u') x := rfl
  rw [this]
  have h2 : ∀ f : WO A S → ℂ, comb ψ A S e (b • f) = b • comb ψ A S e f := fun f => by
    funext y
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h2, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem biLift_move {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS (a • φ) C = a • biLift oma omb vA vS φ C := by
  funext h
  simp only [biLift, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem biLift_smul' {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => by
        rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
        rfl
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem hand_smul_fun {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (a : ℂ)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (a • φ) g h₁ h₂ = a • Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have e : ∀ Ξ, handBF s₁ l (a • φ) Ξ = star a • handBF s₁ l φ Ξ := fun Ξ => by
    funext h w
    simp only [GlobalTheory.Unf.handBF, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, star_mul']
  unfold Chain.hand
  have := GlobalTheory.HandHom.handFB_smul s₂ vL (star a) 1 (handBF s₁ l φ (flatBF s₁ (s₁.om (g, h₁) Φ₁))) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))
  rw [one_smul, star_star, mul_one] at this
  rw [e, this]

theorem sum_supp {G : Type} (a : ℂ) (e : G →₀ ℂ) (F : G → ℂ) :
    ∑ g ∈ (a • e).support, (a • e) g * F g = ∑ g ∈ e.support, e g * (a * F g) := by
  have h : ∀ (e : G →₀ ℂ) (F : G → ℂ), ∑ g ∈ e.support, e g * F g = Finsupp.linearCombination ℂ F e := fun _ _ => rfl
  rw [h, map_smul, ← h, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem contAut_smul {V : HSp D} (a : ℂ) {φ : GA D V → ℂ} (h : IsContAut V φ) : IsContAut V (a • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul a⟩

def free (w : VTup t) : VTup t := { w with FX := fun _ _ => Set.univ }

theorem qpin_free {v : VCom c} {w : VTup t} (h : QPin v w) : QPin v (free w) := by
  obtain ⟨F, h⟩ := h
  exact ⟨F, h.inj, h.places, h.kom, h.mid, h.lastc, h.eQ, h.eQT, h.dQ, h.ε, h.εT, h.FY, h.cQ⟩

theorem inner (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (w : VTup t) (j : ℕ) (β : t.Ch (j + 1 + 1))
    (φ : t.Ch j → GA D (c.X j) → ℂ) (C) :
    (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ ((resc w s).dQ j α γ) ((resc w s).dQ (j + 1) γ β) C)) =
      (s (j + 1 + 1) β)⁻¹ • ∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (s j α • φ α)
        (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) C) := by
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  simp only [resc, biComb_smul2, Comm.bl, biLift_smul', biLift_move, smul_smul]
  congr 1
  have := hs (j + 1) γ
  field_simp

theorem qlast_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLast v (free w)) :
    QLast v (resc w s) := by
  intro j h Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j h Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (this.trans (congrArg _ (Finset.sum_congr rfl fun β _ => Eq.symm ?_)))
  · refine (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    simp only [Comm.bl, biLift_move, Pi.smul_apply, smul_eq_mul, mul_left_comm (f _) (s j α), integral_const_mul]
    rfl
  · congr 1
    funext h'
    have e : trc ((resc w s).εT (j + 1 + 1) h β) f = s (j + 1 + 1) β • trc (w.εT (j + 1 + 1) h β) f := trc_smul_left _ _ _
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, mul_inv_cancel₀ (hs _ _), one_mul]
    rfl

theorem qlaw_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLaw v (free w)) :
    QLaw v (resc w s) := by
  intro j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine cast (congrArg₂ (Iter2 ρ₁ μ₁ ρ₂ μ₂) (Eq.symm ?_) (Eq.symm ?_)) this
  · funext q₁ q₂
    refine Finset.sum_congr rfl fun α _ => (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    congr 1
    have e := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (s j α) 1
      (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁)
            (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)
    rw [one_smul, mul_one, ← hand_smul_fun] at e
    exact e.symm
  · refine congrArg _ (Finset.sum_congr rfl fun β _ => ?_)
    have e : trc ((resc w s).ε (j + 1 + 1) β) f = s (j + 1 + 1) β • trc (w.ε (j + 1 + 1) β) f := trc_smul_left _ _ _
    rw [e]
    refine (GlobalTheory.HandHom.per_smul _ _ _ _ _ _).trans ?_
    rw [inv_mul_cancel₀ (hs _ _), one_mul]
    rfl

theorem qfin_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (H : QFin v w) : QFin v (resc w s) := by
  intro j σ h
  obtain ⟨K, T, a, b, c', d, e, f⟩ := H j σ h
  exact ⟨K, T, a, b, c', d, e, fun Ψ hΨ α g hg => f Ψ hΨ α g (Finsupp.support_smul hg)⟩

theorem laws_of_qpinU (v : VCom c) (H : ∀ w : VTup t, QPin v w → QLaw v w ∧ QLast v w ∧ QFin v w) (w : VTup t)
    (h : QPinU v w) : QLaw v w ∧ QLast v w ∧ QFin v w := by
  obtain ⟨w₀, s, hs, h, rfl⟩ := h
  exact ⟨qlaw_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).1,
    qlast_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).2.1, qfin_resc v _ s (H _ h).2.2⟩

end GlobalTheory.QTw.RescTest
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

structure TwDat.Live {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) : Prop where
  inj : ∀ j, Function.Injective (ι j)
  first : Function.Surjective (ι 0)
  last : Function.Surjective (ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m) γ, γ ∉ Set.range (ι (j + 1)) → ∀ α z, A.xi j hj α γ z = 0

def TwDat.RamL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) (j : ℕ) (φ : ColT I l u a j) : Prop :=
  RamT j φ ∧ ∀ c, A.chOf j c ∉ Set.range (ι j) → φ c = 0

structure PinColL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j)
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  live : A.Live ι
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj (ι j α) (ι (j + 1) γ) z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j (hj : j + 1 ≤ B.R.m) α γ, (∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) →
    cK j = (volLev (x j).vol (A.U j (ι j α)) : ℂ) * w j α γ * c₀ j *
      (A.chr (j + 1) (A.xr j (ι j α)) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) (ι (j + 1) γ)) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ A.RamL ι j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj (ι j β) φ y

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKL (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) {Ch₀ : ℕ → Type}
    (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) : ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = ι j β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := fun j β => A.U j (ι j β)
  chi := fun j β => A.chi j (ι j β)
  h := fun j β => A.h j (ι j β)
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinChL (c₀ : ℕ → ℂ) {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j)
    (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

structure PinTopL (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (ε : ℂ) : Prop where
  emb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  lev : ∀ h, h ∈ UT ↔ g.bT⁻¹ * h * g.bT ∈ levS _ R.βX (datXP R P t)
  eT : ∀ n h β, k.eT n h β = Finsupp.single g.bT ε
  cP : k.cP = ε * (volLev g.volT UT : ℂ)

end GlobalTheory.AdForm
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

def Placed : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
    f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G

def tOf (a₀ a : GA D (D.sp.X 0)) : GA D (D.sp.Y 0) :=
  ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)

end GlobalTheory.MiTop

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) {a : XGeo D}

def LocX.Red {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) (x : S.P.J)
    (g : GL (Fin D.R.r) (kP PP)) : Prop :=
  ∀ (i j : Fin D.R.k ⊕ Fin (l.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ j → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val i j - (ofSplit l.q).pr (z : D.host.E)) < 1

structure SymRead (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k) : Prop where
  char : ∀ PP, (ofSplit (l PP).q).IsChar (pk W).ψ (S PP).ψ
  mu : ∀ PP j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ ((S PP).μ j)
  grp : ∀ g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1), g ∈ (lvP W).H ↔ ∀ PP, ∃ x, (l PP).Red (S PP) x (g PP)
  chr : ∀ (g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1)) (hg : g ∈ (lvP W).H) (x : ∀ PP, (S PP).P.J),
    (∀ PP, (l PP).Red (S PP) (x PP) (g PP)) → (lvP W).chi ⟨g, hg⟩ = ∏ PP, (S PP).P.lam (x PP)

end GlobalTheory.Fam

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

def IsStdFr {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : Frame k N Y) : Prop :=
  ∃ e : Y ≃ Fin N, GlobalTheory.SymBridge.IsOrd pos e ∧ F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word)



structure GeoAll where
  g : Geo D
  j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  ι : Type
  v : VCom (commOf (pk W) u g)
  o : TDat (commOf (pk W) u g) k ι
  n : ℕ
  G : Fin n → GLoc v
  pl : Fin n ≃ (pk W).Pg
  Q : ∀ PP, QAll W PP → GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u g) PP
  d : BotDat W u
  c₀ : ℕ → ℂ

attribute [instance] GeoAll.fld GeoAll.val GeoAll.top GeoAll.loc

variable {W u} (a : GeoAll W u)

abbrev GeoAll.fam (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))) : FamCh W u :=
  ⟨a.g, a.j, row, col⟩

structure GeoAll.Is : Prop where
  meas : GeoMeas (pk W) a.g
  last : (commOf (pk W) u a.g).VolLast
  x : ∀ j, j ≤ D.R.m → (a.g.x j).Is
  vis : a.v.Is
  shape : ShapeOff a.v a.o
  gpin : GPin a.G
  tie : ∀ row col, VTie (a.fam row col) a.v ∧ GRead (a.fam row col) a.G a.pl
  top : TopReadAt W u a.j a.g.bT

  norm : star a.o.ζ₀ ⬝ᵥ a.g.Lz.gram *ᵥ a.o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) ∧
    ∀ j h, a.v.τ j h *ᵥ a.o.ζ₀ = (-D.host.xi0 ^ (D.R.m / 2)) • (a.g.bes j 0 h).ζ

  stdG : ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.G i).FT ∧
    (a.G i).z₀ = fun r => (ofSplit (a.G i).q).pr (a.o.ζ₀ r)
  stdQ : ∀ PP h, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.Q PP h).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.Q PP h).FT ∧
    (a.Q PP h).z₀ = fun r => (ofSplit (a.Q PP h).q).pr (a.o.ζ₀ r)
  bot : (∀ h0, a.d.B.lev = (commOf (pk W) u a.g).B 0 D.R.rS h0) ∧ a.d.b = a.g.b 0 ∧ a.d.B.Adapted (W.S.tr u).wt ∧
    ∀ r, (a.d.B.d.i₀ *ᵥ vecB a.d.B.o a.d.B.ζ) r = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) r))

end Gen

section True

open GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

structure GeoAll.True (a : GeoAll W u) : Prop where
  pinX : GlobalTheory.AdForm.PinX I l Z (pk W).ψ (pk W).θ a.g.x a.g.vac a.c₀
  std : @GlobalTheory.AdForm.StdT B X I l Z u a.k a.fld a.val a.top a.loc a.ι (@TDat.p _ _ _ a.fld a.val a.top a.loc _ a.o)
    (@TDat.β _ _ _ a.fld a.val a.top a.loc _ a.o) (@TDat.Q _ _ _ a.fld a.val a.top a.loc _ a.o) fun j => (a.g.x j).L
  emb : GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  z0 : ∀ r, vecB (a.g.oT B.R.m rfl) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r =
    (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)

end True

end GlobalTheory.Fam

end
end
