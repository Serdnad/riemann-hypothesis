module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystalline
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle734
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem countable_numberField_type (K : Type) [Field K] [NumberField K] : Countable K := by
  let b := Module.finBasis ℚ K
  exact (b.equivFun.toEquiv.injective).countable

theorem lag_countable : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  intro D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  let M := (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)
  haveI : Countable (Submodule D.host.E M) := by
    have hs : Function.Surjective (fun s : Finset M => Submodule.span D.host.E (s : Set M)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  unfold Lag
  infer_instance

end GlobalTheory.RawLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7} (W : HSp D)

theorem exists_gqMat (γ : GQ W) : ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat c = mt W γ :=
  mem_ratMx.1 ((mem_GQ_iff W γ).1 γ.2)

def gqMat (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_gqMat W γ)

theorem rat_gqMat (γ : GQ W) : rat (gqMat W γ) = mt W γ := Classical.choose_spec (exists_gqMat W γ)

theorem gqMat_map (γ : GQ W) : (gqMat W γ).map (incA D) = mt W γ := rat_gqMat W γ

theorem gqMat_mul (γ δ : GQ W) : gqMat W (γ * δ) = gqMat W γ * gqMat W δ :=
  rat_injective (by rw [rat_mul, rat_gqMat, rat_gqMat, rat_gqMat]; rfl)

theorem gqMat_one : gqMat W 1 = 1 := rat_injective (by rw [rat_gqMat, rat_one]; rfl)

theorem gqMat_inv_mul (γ : GQ W) : gqMat W γ⁻¹ * gqMat W γ = 1 := by
  rw [← gqMat_mul, inv_mul_cancel, gqMat_one]

theorem gqMat_mul_inv (γ : GQ W) : gqMat W γ * gqMat W γ⁻¹ = 1 := by
  rw [← gqMat_mul, mul_inv_cancel, gqMat_one]

theorem gqMat_unitary (γ : GQ W) : (gqMat W γ)ᴴ * W.gram * gqMat W γ = W.gram := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_gqMat]
  exact mt_rel W γ

def actEquiv (γ : GQ W) :
    ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E] ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearEquiv.prodCongr
    (LinearEquiv.ofLinear (Matrix.toLin' (gqMat W γ)) (Matrix.toLin' (gqMat W γ⁻¹))
      (by rw [← Matrix.toLin'_mul, gqMat_mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, gqMat_inv_mul, Matrix.toLin'_one]))
    (LinearEquiv.refl _ _)

theorem actEquiv_apply (γ : GQ W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    actEquiv W γ y = (gqMat W γ *ᵥ y.1, y.2) := rfl

theorem isotropic_mulVec (γ : GQ W) (x x' : Fin W.rank → D.host.E) :
    star (gqMat W γ *ᵥ x) ⬝ᵥ W.gram *ᵥ (gqMat W γ *ᵥ x') = star x ⬝ᵥ W.gram *ᵥ x' := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, gqMat_unitary]

def lagAct (γ : GQ W) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _), by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [LinearEquiv.coe_coe, actEquiv_apply]
    rw [isotropic_mulVec]
    exact Y.2.2 y hy y' hy'⟩

theorem mem_lagAct (γ : GQ W) (Y : Lag W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    y ∈ (lagAct W γ Y).1 ↔ (gqMat W γ⁻¹ *ᵥ y.1, y.2) ∈ Y.1 := by
  show y ∈ Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem lagAct_one (Y : Lag W) : lagAct W 1 Y = Y := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, inv_one, gqMat_one, Matrix.one_mulVec]

theorem lagAct_mul (γ δ : GQ W) (Y : Lag W) : lagAct W (γ * δ) Y = lagAct W γ (lagAct W δ Y) := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, mem_lagAct, mem_lagAct, _root_.mul_inv_rev, gqMat_mul]
  simp only [Matrix.mulVec_mulVec]

theorem isLagFrame_lagAct (γ : GQ W) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    IsLagFrame W (lagAct W γ Y) (gqMat W γ * C.1, C.2) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (actEquiv W γ).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

abbrev NGLag (W : HSp D) : Type := {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}

theorem lagAct_ne_bot (γ : GQ W) (Y : Lag W) (h : Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥) :
    (lagAct W γ Y).1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 h
  refine (Submodule.ne_bot_iff _).2 ⟨gqMat W γ *ᵥ x, ?_, ?_⟩
  · rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lagAct, Matrix.mulVec_mulVec, gqMat_inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h0
    apply hx0
    have := congrArg (fun v => gqMat W γ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, gqMat_inv_mul] using this

def ngAct (γ : GQ W) (Y : NGLag W) : NGLag W := ⟨lagAct W γ Y.1, lagAct_ne_bot W γ Y.1 Y.2⟩

theorem ngAct_one (Y : NGLag W) : ngAct W 1 Y = Y := Subtype.ext (lagAct_one W Y.1)

theorem ngAct_mul (γ δ : GQ W) (Y : NGLag W) : ngAct W (γ * δ) Y = ngAct W γ (ngAct W δ Y) :=
  Subtype.ext (lagAct_mul W γ δ Y.1)

end GlobalTheory.RallisCusp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem conjTranspose_gram_mul_apply {D : D7} {n s t : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E)
    (A : Matrix (Fin n) (Fin s) D.host.E) (B : Matrix (Fin n) (Fin t) D.host.E) (a : Fin s) (c : Fin t) :
    (Aᴴ * G * B) a c = star (fun k => A k a) ⬝ᵥ G.mulVec (fun k => B k c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem exists_isoFrame_comap_inl : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
    ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧
      Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  intro D W Y hY
  set I₁ := Y.1.comap (LinearMap.inl D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)) with hI₁
  have hpos : 0 < Module.finrank D.host.E I₁ :=
    Nat.pos_of_ne_zero fun h => hY (Submodule.finrank_eq_zero.mp h)
  let b := Module.finBasisOfFinrankEq D.host.E I₁ rfl
  have hsp : Submodule.span D.host.E (Set.range (I₁.subtype ∘ b)) = I₁ := by
    have h := congrArg (Submodule.map I₁.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  let I : Matrix (Fin W.rank) (Fin (Module.finrank D.host.E I₁)) D.host.E :=
    Matrix.of fun a j => (b j : Fin W.rank → D.host.E) a
  have hT : I.transpose = I₁.subtype ∘ b := by
    funext j a
    rfl
  refine ⟨_, I, ⟨hpos, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact b.linearIndependent.map' I₁.subtype (Submodule.ker_subtype I₁)
  · rw [GlobalTheory.MixModel.cT_sig]
    refine Matrix.ext fun a c => ?_
    rw [conjTranspose_gram_mul_apply, Matrix.zero_apply]
    have ha : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b a : Fin W.rank → D.host.E) ∈ Y.1 := (b a).2
    have hc : LinearMap.inl D.host.E _ (Fin W.rank → D.host.E) (b c : Fin W.rank → D.host.E) ∈ Y.1 := (b c).2
    have h := Y.2.2 _ ha _ hc
    simp only [LinearMap.inl_apply, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h
    exact h
  · rw [hT]
    exact hsp

end GlobalTheory.RawLift
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TameCover

section
variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l)
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

theorem galOA_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (x : OA l O) :
    galOA O (g * h) x = galOA O g (galOA O h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOA_tmul, galOA_tmul, galOA_tmul, GlobalTheory.RingBasics.σA_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def actA (γ : TameGal ↥LL.1 l e a) (f : ZMod a → A ↥(OL LL) ↥LL.1) : ZMod a → A ↥(OL LL) ↥LL.1 :=
  fun τ => ⟨ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) τ, Rot.ringAct_mem rot_A γ (fun σ => (f σ).2) τ⟩

theorem covers_mul {k k' : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hk : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hk' : Covers ↥LL.1 (thetaW a LL) ϖ k' γ') :
    Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ') := by
  intro f f'' hf''
  have h1 := hk' f (actA LL γ' f) (fun τ => rfl)
  have h2 := hk (actA LL γ' f) f'' (fun τ => by
    rw [hf'' τ, map_mul]
    rfl)
  rw [galOA_mul', h1, h2]

theorem covers_of_mem {k : GQ l} (hk : k ∈ ϖ.GfieldInf a) :
    Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) := by
  intro f f' hf'
  have : f' = f := funext fun τ => Subtype.ext (by rw [hf' τ, map_one]; rfl)
  rw [this]
  exact ϖ.galOA_iTot (thetaW a LL) ↥LL.1 hk f

theorem covers_unique {k : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hγ : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hγ' : Covers ↥LL.1 (thetaW a LL) ϖ k γ') : γ = γ' := by
  have key : ∀ f : ZMod a → A ↥(OL LL) ↥LL.1,
      ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) = ringAct γ' (fun σ => (f σ : PowerSeries ↥LL.1)) := by
    intro f
    have h := (hγ f (actA LL γ f) (fun _ => rfl)).symm.trans (hγ' f (actA LL γ' f) (fun _ => rfl))
    have h2 := ϖ.iTot_injective (thetaW a LL) ↥LL.1 h
    funext τ
    exact congrArg Subtype.val (congrFun h2 τ)
  have hs : γ.shift = γ'.shift := by
    by_contra hne
    have h := congrFun (key fun σ => if σ = 0 then 1 else 0) γ.shift
    simp only [ringAct_apply, sub_self] at h
    rw [if_neg (sub_ne_zero.2 hne)] at h
    simp at h
  have hl : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) = ((γ'.left : (↥LL.1)ˣ) : ↥LL.1) := by
    have h := congrArg (fun F => coeff 1 (F 0)) (key fun _ => uIn _)
    have hu : ((uIn (A ↥(OL LL) ↥LL.1) : A ↥(OL LL) ↥LL.1) : PowerSeries ↥LL.1) = X := rfl
    simp only [hu, ringAct_X, coeff_C_mul, coeff_one_X, mul_one] at h
    simpa [TameGal.root] using h
  refine SemidirectProduct.ext (Subtype.ext (Units.ext hl)) ?_
  exact congrArg Multiplicative.ofAdd hs

omit [HasUnr a LL] in
theorem lift_root (a : ℕ) [TameDescentExponentData ↥LL.1 l e a] (ζ : Om l) (hζ : ζ ^ e = 1) :
    ∃ ζK : rootsOfUnity e ↥LL.1, (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) = ζ := by
  obtain ⟨ζ0, h0⟩ := TameDescentExponentData.prim (K := ↥LL.1) l a (e := e)
  have h1 : IsPrimitiveRoot ((ζ0 : ↥LL.1) : Om l) e := h0.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨rootsOfUnity.mkOfPowEq (ζ0 ^ i) (by rw [← pow_mul, mul_comm, pow_mul, h0.pow_eq_one, one_pow]), ?_⟩
  rw [rootsOfUnity.val_mkOfPowEq_coe, ← hi]
  rfl

end

end GlobalTheory.TameCover
end

namespace GlobalTheory.TameCover

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  intro l _ a e _ _ ϖ LL _ _
  have hsucc : e + 1 = l ^ a := TameDescentExponentData.succ_eq (↥LL.1) (l := l) (e := e) (a := a)

  have hroot_mem : ∀ x : Om l, x ^ l ^ a = x → x ∈ (ϖ.field a).1 := fun x hx =>
    ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _ hx)
  have hfix : ∀ h ∈ GK (ϖ.field a), ∀ x ∈ (ϖ.field a).1, h x = x := fun h hh x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
  refine ⟨GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc, ?_, ?_, fun k γ γ' => covers_unique ϖ LL, fun k k' γ γ' => covers_mul ϖ LL,
    fun k => ⟨GlobalTheory.T.mem_kummerTowerUnramified_of_covers_one l a e ϖ LL k, covers_of_mem ϖ LL⟩, ?_⟩
  · intro k hk
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq l a k
    have hπ : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
    have hke : k (ϖ.seq 0 ^ e) = ϖ.seq 0 ^ e :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩)
    have hζ : (k (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, hke, div_self (pow_ne_zero _ hπ)]
    obtain ⟨ζK, hζK⟩ := lift_root LL a _ hζ
    refine ⟨⟨ζK, Multiplicative.ofAdd m⟩, GlobalTheory.T.covers_of_action' l a e ϖ LL _ k hk hm ?_⟩
    change k (ϖ.seq 0) = (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0
    rw [hζK, div_mul_cancel₀ _ hπ]
  · intro γ
    have hζ : ((((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)) ^ e = 1 := by
      have h1 : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 γ.left.2, Units.val_one]
      rw [← IntermediateField.coe_pow, h1]
      rfl
    obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.exists_galois_prescribed_unramified_kummer l a e ϖ hsucc γ.shift _ hζ
    obtain ⟨h, hh, k, hk, rfl⟩ := GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc g
    have hinj : Function.Injective h := h.injective
    refine ⟨k, hk, GlobalTheory.T.covers_of_action' l a e ϖ LL γ k hk (fun x hx => hinj ?_) (hinj ?_)⟩
    · have h1 := hg1 x hx
      have h2 : (x ^ l ^ γ.shift.val) ^ l ^ a = x ^ l ^ γ.shift.val := by
        rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [hfix h hh _ (hroot_mem _ h2)]
      exact h1
    · have hz : (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) ^ l ^ a = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
        rw [← hsucc, pow_succ, hζ, one_mul]
      rw [hfix h hh _ (mul_mem (hroot_mem _ hz) (ϖ.pi_mem_field a))]
      exact hg2
  · intro k ζ hk
    obtain ⟨hr, -⟩ := GlobalTheory.T.action_of_covers l a e ϖ LL k _ hk
    have hr' : ∀ x : Om l, x ^ l ^ a = x → k x = x := fun x hx => by
      rw [hr x hx]
      simp
    obtain ⟨k', hk', h, hh, hkh⟩ := GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf l a e ϖ hsucc k hr'
    have hc : Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) := by
      have := covers_mul ϖ LL hk (covers_of_mem ϖ LL hh)
      rwa [mul_one, ← hkh] at this
    refine ⟨k', hk', hc, ?_⟩
    rw [(GlobalTheory.T.action_of_covers l a e ϖ LL _ _ hc).2]
    rfl

end GlobalTheory.TameCover
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]

  rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → a = (l - 1).factorial → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : Gl l) (N : ℕ), (pc Pl h hN hF hS).IsFrob Fr → FrobStable (pc Pl h hN hF hS).Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → N < l → (∀ χ ∈ Sig, ∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ (pc Pl h hN hF hS).H → χ g = 1) → (∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l) → ∃ Sig' : Finset (ZMod e), (∀ c ∈ Sig', (l : ZMod e) * c ∈ Sig') ∧ (0 : ZMod e) ∈ Sig' ∧ Sig'.card ≤ N ∧ maxPeriod l Sig' = Formalism.MainNotions.ElementDenominator.rPrime (pc Pl h hN hF hS).Iner Fr Sig ∧ ∀ T : QLat LL, (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ ∧ TameType a ϖ Pl T Sig' := by
  first | exact @GlobalTheory.GoodLatt.main | exact GlobalTheory.GoodLatt.main | (intros; apply GlobalTheory.GoodLatt.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧ ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x := by
  first | exact @GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | exact GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | (intros; apply GlobalTheory.BSP.BK.evW_isUnit_injective_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  first | exact @GlobalTheory.BSP.exists_ker_vector_mem_OE | exact GlobalTheory.BSP.exists_ker_vector_mem_OE | (intros; apply GlobalTheory.BSP.exists_ker_vector_mem_OE <;> assumption)
end
