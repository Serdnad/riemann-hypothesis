module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCOB
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCP
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inf_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) : θ (infPart D (x : AE D)) ≠ 0 :=
  ((x.isUnit.map (infPart D)).map θ).ne_zero

theorem hasInfExp_mul {χ χ' : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (h : HasInfExp D χ τ a)
    (h' : HasInfExp D χ' τ b) : HasInfExp D (χ * χ') τ (a + b) := by
  obtain ⟨n, hn, e⟩ := h
  obtain ⟨m, hm, e'⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  have hz := inf_ne_zero (th0 D τ) x
  rw [MonoidHom.mul_apply, Circle.coe_mul, allSome_fam.1 e x h1 h2, allSome_fam.1 e' x h1 h2, zpow_add₀]
  exact div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)

theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, e⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, allSome_fam.1 e x h1 h2, _root_.zpow_neg]

theorem hasInfExp_one (τ : D.what₂.Tau) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, allSome_fam.2 fun x _ _ => by simp⟩


variable (D) in
def chrA : Subgroup ((AE D)ˣ →* Circle) where
  carrier := {χ | IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a}
  one_mem' := ⟨⟨continuous_const, fun _ => rfl⟩, fun τ => ⟨0, hasInfExp_one τ⟩⟩
  mul_mem' := fun {a b} ha hb => ⟨⟨ha.1.1.mul hb.1.1, fun x => by rw [MonoidHom.mul_apply, ha.1.2, hb.1.2, one_mul]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      obtain ⟨t, ht⟩ := hb.2 τ
      exact ⟨_, hasInfExp_mul hs ht⟩⟩
  inv_mem' := fun {a} ha => ⟨⟨ha.1.1.inv, fun x => by rw [MonoidHom.inv_apply, ha.1.2, inv_one]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      exact ⟨_, hasInfExp_inv hs⟩⟩

def ExpU (D : D7) : Prop := ∀ (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D χ τ a → HasInfExp D χ τ b → a = b

theorem heis_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (f g : WA V W → ℂ) :
    Heisenberg₂ ψ V W u (f + g) = Heisenberg₂ ψ V W u f + Heisenberg₂ ψ V W u g := by
  funext w; simp [Heisenberg₂, mul_add]

theorem heis_smul (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (c : ℂ) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W u (c • f) = c • Heisenberg₂ ψ V W u f := by
  funext w
  exact mul_left_comm _ c _

def schC (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [Heisenberg₂]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩
  add_mem' := fun {f g} hf hg => ⟨fun γ w => by rw [Pi.add_apply, Pi.add_apply, hf.quasi, hg.quasi, mul_add], by
      obtain ⟨U, hU, e⟩ := hf.level
      obtain ⟨U', hU', e'⟩ := hg.level
      exact ⟨U ⊓ U', hU.inter hU', fun u hu h0 => by rw [heis_add, e u hu.1 h0, e' u hu.2 h0]⟩,
    hf.cont.add hg.cont, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)⟩
  smul_mem' := fun c f hf => ⟨fun γ w => by
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm], by
      obtain ⟨U, hU, e⟩ := hf.level
      exact ⟨U, hU, fun u hu h0 => by rw [heis_smul, e u hu h0]⟩,
    hf.cont.const_smul c, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).const_smul c⟩


def admitted (V W : HSp D) (χ χ' : chrA D) : Prop := ResEta D χ.1 V.rank ∧ ResEta D χ'.1 W.rank

structure IsWeil (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : chrA D)
    (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) : Prop where
  Heisenberg₂ : ∀ g h w₀ (Φ Φ' : schC ψ V W), Φ'.1 = Heisenberg₂ ψ V W w₀ Φ.1 →
    (Om (g, h) Φ').1 = Heisenberg₂ ψ V W (actHom V W g h w₀) (Om (g, h) Φ).1
  aut : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ : schC ψ V W, (Om (γ, γ') Φ).1 0 = Φ.1 0
  cont : ∀ (Φ : schC ψ V W) w, Continuous fun p : GA D V × GA D W => (Om p Φ).1 w
  unit : ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p (Φ : schC ψ V W), ∫ w in 𝓕, ‖(Om p Φ).1 w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Φ.1 w‖ ^ 2 ∂μ
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : schC ψ V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ' : schC ψ V W, Φ'.1 = Theta.Heisenberg₂ ψ V W u Φ.1 → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Om (g, h) Φ) = (r : ℂ) * (splitFac V W χ.1 χ'.1 x y : ℂ) * ℓ Φ
  unr : ∀ S, UnramOutside D χ.1 S → UnramOutside D χ'.1 S → ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : schC ψ V W,
    (∀ u ∈ latVWS V W S, Theta.Heisenberg₂ ψ V W u Φ.1 = Φ.1) → Om (k, k') Φ = Φ

def kerC {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) (Φ : schC ψ V W)
    (g : GA D V) (h : GA D W) : ℂ := (Om (g, h) Φ).1 0

def LiftOK {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) : Prop :=
  ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ (Φ : schC ψ V W) (φ : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsCuspFun V φ →
      (∀ h, IntegrableOn (fun g => kerC Om Φ g h * φ g) 𝓕 μ) ∧
      IsAutFunSm (th0 D) W fun h => ∫ g in 𝓕, kerC Om Φ g h * φ g ∂μ

structure WeilRepresentationFamily (ψ : AddChar (AF D.host.F) ℂ) where
  om : ∀ V W, chrA D → chrA D → (GA D V × GA D W →* Module.End ℂ (schC ψ V W))
  weil : ∀ V W χ χ', admitted V W χ χ' → IsWeil ψ V W χ χ' (om V W χ χ')
  twW_up : ∀ (V W : HSp D) (χ χ' ν : chrA D), V.rank ≤ W.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = (((ν.1 x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_up : ∀ (V W : HSp D) (χ χ' ν : chrA D), V.rank ≤ W.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = ((ν.1 x : Circle) : ℂ) • om V W χ χ' (g, h)
  twW_dn : ∀ (V W : HSp D) (χ χ' ν : chrA D), W.rank < V.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = ((ν.1 x : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_dn : ∀ (V W : HSp D) (χ χ' ν : chrA D), W.rank < V.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = (((ν.1 x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  swap : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → admitted V W χ χ' →
    ∀ g h (Φ : schC ψ V W) (Φ' : schC ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) →
      ∀ x : WA V W, (om W V χ' χ (h, g) Φ').1 x.transpose = (om V W χ χ' (g, h) Φ).1 x

structure WeilC (ψ : AddChar (AF D.host.F) ℂ) extends WeilRepresentationFamily ψ where
  lift : ∀ V W χ χ', admitted V W χ χ' → LiftOK (om V W χ χ')

structure FormGaps (D : D7) : Prop where
  atTau : AtTauU D
  add : SmAdd D
  right : SmRight D
  conj : SmConj D
  cuspInt : CuspInt D
  volEx : VolEx D
  volU : VolU D
  petInt : PetInt D

variable {ψ : AddChar (AF D.host.F) ℂ}



open Classical in
def cptC (V : HSp D) (τ : D.what₂.Tau) :
    Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ :=
  if h : V.SigOK then (cpt_bas_ex V h τ).choose else 0

def kfinC (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (schC ψ V W) :=
  Submodule.span ℂ {Φ | IsPolFock ψ (th0 D) V W (cptC V) (cptC W) Φ.1}

end Formalism.L2.Fam.ThC

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.DIV.Inh

section Cover

variable (p q : ℕ)

end Cover


variable {D : D7}

theorem gram_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
  RingHom.id_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

def colM (V : HSp D) {n : ℕ} (v : Fin n → V.V) : Matrix (Fin V.rank) (Fin n) D.host.E := fun i k => V.frame.repr (v k) i

theorem colM_gram (V : HSp D) {n m : ℕ} (v : Fin n → V.V) (w : Fin m → V.V) (a : Fin n) (b : Fin m) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram * colM V w) a b = V.hT (v a) (w b) := by
  rw [gram_coord, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  rfl

theorem colM_vec (V : HSp D) {n : ℕ} (v : Fin n → V.V) (z : V.V) (a : Fin n) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram).mulVec (V.frame.repr z) a = V.hT (v a) z :=
  (colM_gram V v (fun _ : Fin 1 => z) a 0)

theorem frameMat_eq (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : frameMat A B ι = colM A fun k => ι (B.frame k) := by
  ext i k
  rw [frameMat, LinearMap.toMatrix_apply]
  rfl

theorem frame_rel {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * frameMat A B ι = B.gram := by
  ext a b
  rw [frameMat_eq, colM_gram, h]
  rfl

def besselFlagHyperbolic (D : D7) (c : Fin D.R.rS → D.host.E) (hc : ∀ i, c i ≠ 0) (y : GfC (D.sp.Y 0)) :
    BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) where
  ρ := D.R.rS
  codim := by
    rw [D.sp.X_rank 0 (Nat.zero_le _), D.sp.Y_rank 0 (Nat.zero_le _)]
    have := D.R.rS_two
    show D.R.k + 0 * (D.R.t + 1) + 2 * D.R.rS + 1 = D.R.k + D.R.m - 1 + 0 * D.R.t
    omega
  e := colM (D.sp.Y 0) D.sp.hypE
  e_iso := ⟨by
    have h1 : LinearIndependent D.host.E D.sp.hypE := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have e := congrArg (fun x => (D.sp.Y 0).hT (D.sp.hypF i) x) hg
      have hfe : ∀ k, (D.sp.Y 0).hT (D.sp.hypF i) (D.sp.hypE k) = if k = i then 1 else 0 := fun k => by
        rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
        split_ifs <;> simp

      simpa [map_sum, hfe] using e
    exact h1.map' (D.sp.Y 0).frame.equivFun.toLinearMap (LinearEquiv.ker _),
    by ext a b; rw [colM_gram, D.sp.hyp_ee]; rfl⟩
  e_perp := by ext a b; rw [frameMat_eq, colM_gram, (D.sp.hyp_orthX b _).1]; rfl
  z := (D.sp.Y 0).frame.repr D.sp.zm
  z_perpA := by funext a; rw [frameMat_eq, colM_vec, D.sp.zm_orth]; rfl
  z_perpE := by
    funext a
    rw [colM_vec, ← (D.sp.Y 0).herm.eq, (D.sp.hyp_orthz a).1]
    simp
  z_ne := by
    have e : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.Y 0).gram ((D.sp.Y 0).frame.repr D.sp.zm)
      ((D.sp.Y 0).frame.repr D.sp.zm) = (D.sp.Y 0).hT D.sp.zm D.sp.zm := (gram_coord _ _ _).symm
    rw [e, D.sp.zm_norm, neg_ne_zero]
    exact Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero
  c := c
  c_ne := hc
  y := y

variable {ψ : AddChar (AF D.host.F) ℂ}

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V}

def prM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin B.rank) (Fin A.rank) D.host.E :=
  B.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram)

theorem perp_rel (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * (1 - frameMat A B ι * prM A B ι) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, frame_rel h, prM, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (gram_det_ne B).isUnit, Matrix.one_mul, sub_self]

theorem emb_gen {E R : Type} [CommRing E] [CommRing R] {a b : ℕ} (f : E →+* R) (M : Matrix (Fin a) (Fin b) E)
    (P : Matrix (Fin b) (Fin a) E) (Q : Matrix (Fin a) (Fin a) E) (hQ : M * P + Q = 1) (g : Matrix (Fin a) (Fin a) R)
    (x : Matrix (Fin b) (Fin b) R) (e1 : g * M.map f = M.map f * x)
    (e2 : ∀ j, g.mulVec (fun i => f (Q i j)) = fun i => f (Q i j)) : g = M.map f * x * P.map f + Q.map f := by
  have e2' : g * Q.map f = Q.map f := by
    ext i j
    exact congrFun (e2 j) i
  have e3 : M.map f * P.map f + Q.map f = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_add f f.map_add, hQ, Matrix.map_one _ f.map_zero f.map_one]
  rw [← e1, ← e2', Matrix.mul_assoc, ← Matrix.mul_add, e3, Matrix.mul_one]

def coM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin A.rank) (Fin A.rank) D.host.E :=
  1 - frameMat A B ι * prM A B ι

theorem embU (D : D7) : EmbU D := by
  intro A B ι h g g' x a b
  have hQ : frameMat A B ι * prM A B ι + coM A B ι = 1 := add_sub_cancel _ _
  have hp : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram).mulVec
      (fun k => coM A B ι k j) = 0 := fun j => funext fun i => congrFun (congrFun (perp_rel h) i) j
  exact Subtype.ext (Units.ext ((emb_gen (incA D) _ _ _ hQ (mt A g) (mt B x) a.1 fun j => a.2 _ (hp j)).trans
    (emb_gen (incA D) _ _ _ hQ (mt A g') (mt B x) b.1 fun j => b.2 _ (hp j)).symm))

end Emb

section Rows

variable (X : ThetaX D)

end Rows

end Formalism.L2.Fam.ThC

end
end
