module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem cA_inc (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  rfl

theorem hO_eq_trace (x y : WO V W) :
    hO V W x y = Matrix.trace ((V.gram⁻¹).map (incA D) * ((y.map (cA D))ᵀ * W.gram.map (incA D) * x)) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem hO_ratMul (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (u v : WO V W) :
    hO V W (ratMul C u) (ratMul C v) =
      Matrix.trace ((V.gram⁻¹).map (incA D) * ((v.map (cA D))ᵀ * (Cᴴ * W.gram * C).map (incA D) * u)) := by
  have h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ := by
    ext i j; simp [Matrix.map_apply, cA_inc]
  rw [hO_eq_trace]
  unfold ratMul
  rw [Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem gram_eq {Y : Lag W} {C} (h : IsLagFrame W Y C) : C.1ᴴ * W.gram * C.1 = C.2ᴴ * W.gram * C.2 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  funext j k
  have m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 := fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  have := Y.2.2 _ (m j) _ (m k)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at this
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

theorem ratMul_add (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (γ) (u : WO V W) :
    ratMul C (ratW W V γ + u) = ratW W V (C * γ) + ratMul C u := by
  unfold ratMul ratW
  rw [Matrix.mul_add, Matrix.map_mul]

theorem integrand_periodic (hψ : ∀ x, ‖ψ x‖ = 1) {Y : Lag W} {C} (h : IsLagFrame W Y C) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (γ) (u : WO V W) :
    f₁ (ratMul C.1 (ratW W V γ + u)) * star (f₂ (ratMul C.2 (ratW W V γ + u))) =
      f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
  have e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ) := fun B => by
    unfold ratMul ratW; rw [Matrix.map_mul]
  have s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u) := by
    rw [e, e]; unfold symplOH symplO; rw [hO_ratMul, hO_ratMul, gram_eq h]
  rw [ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']
  set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz
  have : z * star z = 1 := by
    have := Complex.mul_conj' z
    rw [hz, hψ] at this
    simpa using this
  calc _ = (z * star z) * (f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) := by ring
    _ = _ := by rw [this, one_mul]

theorem swPair_rank_zero {νV 𝓗 νW 𝓖 μ 𝓕 fr} (hs : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) (h : W.rank = 0)
    (f₁ f₂ : WO V W → ℂ) :
    HasSum (fun Y : Lag W => ((νV 𝓗).toReal : ℂ) * lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV) := by
  haveI : IsEmpty (Fin W.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO V W) := ⟨fun a b => by funext i; exact isEmptyElim i⟩
  haveI : Subsingleton (Lag W) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Unique (Lag W) := uniqueOfSubsingleton default
  have hμ : μ 𝓕 = 1 := hs.covol.2.2
  have hc : ∀ g : WO V W → ℂ, g = fun _ => g 0 := fun g => funext fun w => by rw [Subsingleton.elim w 0]
  have z : ∀ x y : WO V W, symplOH V W x y = 0 := fun x y => by simp [symplOH, symplO, hO]
  have one : IsThetaFunO ψ V W (fun _ => 1) :=
    ⟨fun γ w => by simp [z], ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO, z]⟩, continuous_const,
      fun _ _ _ _ _ => contDiff_const⟩
  have key : ∀ p, ∀ f : WO V W → ℂ, om p f 0 = f 0 * om p (fun _ => 1) 0 := fun p f => by
    have : f = f 0 • (fun _ => (1 : ℂ)) := by funext w; simp [Subsingleton.elim w 0]
    conv_lhs => rw [this, map_smul]
    simp
  have nm : ∀ p, om p (fun _ => 1) 0 * star (om p (fun _ => 1) 0) = 1 := fun p => by
    have u := hs.weil.om_unit μ 𝓕 hs.covol.1 hs.covol.2.1 p _ one
    rw [hc (om p fun _ => 1)] at u
    simp only [setLIntegral_const, hμ, mul_one, enorm_one, one_pow] at u
    have u2 : ‖om p (fun _ => 1) 0‖ ^ 2 = 1 := by
      have := congrArg ENNReal.toReal u
      rwa [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_one] at this
    have := Complex.mul_conj' (om p (fun _ => 1) 0)
    rw [← Complex.ofReal_pow, u2] at this
    simpa using this
  have I : ∀ g, thetaKO om g 1 f₁ * star (thetaKO om g 1 f₂) = f₁ 0 * star (f₂ 0) := fun g => by
    unfold thetaKO
    rw [key _ f₁, key _ f₂, star_mul']
    calc _ = (om (g, 1) (fun _ => 1) 0 * star (om (g, 1) (fun _ => 1) 0)) * (f₁ 0 * star (f₂ 0)) := by ring
      _ = _ := by rw [nm, one_mul]
  have L : ∀ C, lagTerm μ 𝓕 C f₁ f₂ = f₁ 0 * star (f₂ 0) := fun C => by
    have : μ.real 𝓕 = 1 := by rw [Measure.real, hμ, ENNReal.toReal_one]
    unfold lagTerm
    simp only [Subsingleton.elim (ratMul _ _ : WO V W) 0]
    rw [setIntegral_const, this, one_smul]
  simp only [I, L, setIntegral_const]
  convert hasSum_unique (fun _ : Lag W => ((νV 𝓗).toReal : ℂ) * (f₁ 0 * star (f₂ 0))) using 1
  simp [Measure.real]

end GlobalTheory.RawLift.Model

end
end

section

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct

variable {D : D7}

section Sys

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def IsEigVec (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) (x : Y.Fm i j b) : Prop :=
  x ∈ V0 Y i j b ∧ x ≠ 0 ∧ ∀ k P, HkIdx i k P → Y.hkF i j b k P x = ev k P • x

def IsEigSys (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) : Prop :=
  ∃ x, IsEigVec Y i j b ev x

def sigEv {i : X.Tw} (s : X.Sig i) (k : ℕ) (P : PlE D.host) : FractionRing (X.O i) :=
  algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P)

variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}

end Sys

section Read

variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)

def fracMap (i : X.Tw) : FractionRing (X.O0 i) →+* FractionRing (X.O i) :=
  IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i)) (L := FractionRing (X.O i)) (X.O_inj i)

def embO (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O i) := (fracMap X i).comp (embSide X i b)

theorem fracMap_algebraMap (i : X.Tw) (x : X.O0 i) :
    fracMap X i (algebraMap (X.O0 i) (FractionRing (X.O0 i)) x) =
      algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) x) :=
  by simp [fracMap, IsFractionRing.map]

structure CoefRead (i : X.Tw) (b : Bool) where

  F : Type
  [fld : Field F]

  e : ↥D.LL0 →+* F

  u : F →+* FractionRing (X.O i)

  toC : F →+* ℂ
  u_e : ∀ x, u (e x) = embO X i b x
  toC_e : ∀ x, toC (e x) = embLL0 D x

attribute [instance] CoefRead.fld

variable {X} {i : X.Tw} {b : Bool}

end Read

section Par

def IsRowPar (Rw : RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  IsParam σ π ∧ ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w

variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)

variable {C Rw Y} {i : X.Tw} {b : Bool}

end Par

section Res

variable (Rw : RowSide D)

def IsoInduces {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def TeichAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  ∀ k, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 → ∀ z : Zbar l,
    (z : Qbar l) = ι.symm (D.ntypes.teichC k x) → red z = D.ntypes.iota k v w x

def ResAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π l ι r → IsResidual ι r σ w red

end Res

def ResTied (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), ResAt Rw ι w red

section Bridge

theorem ball_of_int {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (a b : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, ‖a x‖ < 1 ↔ ‖b x‖ < 1) (x : L) : ‖a x‖ ≤ 1 ↔ ‖b x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | (apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff ..)

theorem val_pos_iff (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) :
    0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
  have h := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)] at h
  rw [D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)]
  norm_cast at h ⊢
  omega

theorem IsoInduces.lt_iff {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {w : D.what₂.places.Pl} (h : IsoInduces ι w)
    (x : D.what₂.LL) : 0 < D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖ι.symm (D.what₂.embLL x)‖ := by simpa using hx
    rw [val_pos_iff w hx, h, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ h0, not_le]

theorem resChar_eq {w : D.what₂.places.Pl} {l : ℕ} (hl : l.Prime) (h : 0 < D.what₂.places.val w (l : D.what₂.LL)) :
    D.what₂.places.resChar w = l := by
  by_contra hne
  have hp := D.what₂.places.resChar_prime w
  have h1 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
    have hn : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ]; exact (D.what₂.places.val w).map_le_add ih (by simp)
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using hn n
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hn n
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hne)
  have e' : (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : D.what₂.LL) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) e
  have := (D.what₂.places.val w).map_lt_add (g := 0) (x := (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ))
    (y := (b : D.what₂.LL) * l) (by rw [AddValuation.map_mul]; exact h1.trans_le (le_add_of_nonneg_left (hint a)))
    (by rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b)))
  rw [e', AddValuation.map_one] at this
  exact lt_irrefl _ this

variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}

theorem norm_lt_iff (ρ : Reading X i b) (z : FractionRing (X.O0 i)) :
    (∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = z) ↔ ‖ρ.κ z‖ < 1 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.padicAlgCl_embedding_bounded_continuous (X.l i) (X.twistBaseCoefficientRing_isAdic i) (GlobalTheory.GalChar.toQ ρ.κ) ρ.κ_alg
  refine ⟨fun ⟨y, hy, e⟩ => e ▸ h2 y hy, fun h => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, zero_mem _, map_zero _⟩
  have h0 : 0 < ‖ρ.κ z‖ := by simpa using hz
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨y, e⟩ | ⟨y, e⟩
  · refine ⟨y, ?_, e⟩
    by_contra hy
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hy
    have e1 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ * ‖GlobalTheory.GalChar.toQ ρ.κ (u⁻¹ : (X.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have e2 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ < 1 := by rw [← e] at h; exact h
    exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) e2 (h1 _)).ne e1
  · have := h1 y
    change ‖ρ.κ (algebraMap _ _ y)‖ ≤ 1 at this
    rw [e, map_inv₀, norm_inv, inv_le_one₀ h0] at this
    exact absurd h (not_lt.2 this)

theorem exists_reading_of_induces {b' : Bool} (ρ : Reading X i b') {ι : Qbar (X.l i) ≃+* ℂ} {w : D.what₂.places.Pl}
    (h : IsoInduces ι w) (hw : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (embSide X i b x)‖ ≤ 1) :
    ∃ ρ' : Reading X i b, ρ'.ι = ι := by
  obtain ⟨g, hg⟩ := GlobalTheory.EmbUnitBallConj.exists_conj (X.l i) ↥D.LL0 (ρ.κ.comp (embSide X i b))
    (ι.symm.toRingHom.comp (embLL0 D)) fun x => (hw x).symm.trans (h x)
  refine ⟨⟨(g : Qbar (X.l i) →+* Qbar (X.l i)).comp ρ.κ, ι, fun z => ?_, fun x => ?_⟩, rfl⟩
  · rw [RingHom.comp_apply, ρ.κ_alg]
    exact g.commutes _
  · exact (congrArg ι (hg x)).trans (ι.apply_symm_apply _)

end Bridge

namespace Model

open Formalism.MainNotions.BlochKatoReduction (scalGL)

variable (D)


variable {D}

end Model

end GlobalTheory.EigTie

end
end
