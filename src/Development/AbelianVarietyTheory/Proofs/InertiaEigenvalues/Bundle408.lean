module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle392
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.PolarTraceMulVecMulVecEq
public import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open Matrix

namespace GlobalTheory.NewPrime.FormVanish

def twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) :
    Γ →* Matrix (Fin r) (Fin r) A where
  toFun g := ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul]
    rw [smul_mul_smul_comm]

theorem twMat_apply {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) :
    twMat ρ κ g = ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) := rfl

theorem repOn_twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) (v : Fin r → A) : repOn ρ κ A g v = twMat ρ κ g *ᵥ v := by
  funext a
  simp [repOn, matAct, twMat_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem eq_one_of_mulVec {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.one_apply, Pi.single_apply] using this

theorem auxiliaryCharacter_complexConj_invariant {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)
    (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; rfl
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem two_mul_values_eq_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hκ hκz hκL x y hb
  obtain ⟨J, hJ⟩ := hS.1.2.2.1
  obtain ⟨d, hd, hd2, -, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨g₀, u, hu⟩ := UpperTheory.KStar.exists_eps_eq_pow_nu X i
  set φ := algebraMap (X.O0 i) A with hφ
  set T := twMat (Tgl i s) κ with hT
  set T' := twMat ρ κ⁻¹ with hT'
  let χ : GE N →* A := (powMonoidHom D.R.t).comp (φ.toMonoidHom.comp ((Units.coeHom _).comp (eps0 X i)))
  have hχ : ∀ g, χ g = φ ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t := fun g => rfl
  let J' : GL (Fin D.R.r) A := Units.map φ.mapMatrix.toMonoidHom J
  have hJ1 : (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) = (J : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  have hJ2 : ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) =
      ((J⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  let d' : Aˣ := Units.map φ.toMonoidHom d
  have hd' : (d' : A) = φ d := rfl
  have e₁ : ∀ g, T g = ((κ g : Aˣ) : A) • (Tmat i s g).map φ := fun g => by rw [hT, twMat_apply, Tgl_coe]
  have sd : ∀ g, T' (cConj X g) = (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * (χ g • T g) *
      ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) := fun g => by
    rw [hT', twMat_apply, hρ, hJ g _ (cConj_apply X g), Matrix.map_mul, Matrix.map_mul, e₁, hJ1, hJ2,
      MonoidHom.inv_apply, antiHom_cConj X hκ, inv_inv, ← smul_mul_assoc, ← mul_smul_comm, hχ]
    congr 2
    ext a b
    simp [hφ, mul_left_comm]
  have z₁ : T z = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [e₁, hd, hκz]
    ext a b
    simp [hd', Matrix.one_apply, apply_ite φ]
  have z₂ : T' z = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
      apply Matrix.inv_eq_left_inv
      rw [hd, smul_mul_smul_comm, Units.inv_mul, mul_one, one_smul]
    have h2 : ((d'⁻¹ : Aˣ) : A) = φ ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) := rfl
    rw [hT', twMat_apply, hρ, Tdual, hε, h1, MonoidHom.inv_apply, hκz, h2]
    generalize ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) = e
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hφ]
    · simp [hab]
  have hχz : χ z = 1 := by rw [hχ, hε]; simp
  have z₃ : T' (cConj X z) = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [sd, hχz, one_smul, z₁, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]
  have z₄ : T (cConj X z) = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 := sd (cConj X z)
    have h3 : χ (cConj X z) = 1 := by rw [← hχz, hχ, hχ, auxiliaryCharacter_complexConj_invariant]
    rw [cConj_cConj, z₂, h3, one_smul] at h1
    have h4 : T (cConj X z) = ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) *
        ((J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * T (cConj X z) *
          ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A)) * J' := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [h4, ← h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
  have key := KStar.Tree.twist_mul_coord_eq_zero (GE N) A D.R.r T T' χ (cConj X) J' L z d' x.1 y.1
    (by
      have := GlobalTheory.NewPrime.Burnside.span_twist_eq_top D N X bkP i s A κ Q hS
      rwa [← funext e₁] at this) sd hL.1.2.1
    (fun h hh => (hL.1.2.2.1 h _ (cConj_apply X h)).1 hh)
    (fun h hh => ⟨eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ ρ hK hρ A h hh).1, hκL h hh,
          Units.val_one, one_smul],
      eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1,
          MonoidHom.inv_apply, hκL h hh, inv_one, Units.val_one, one_smul]⟩) z₁ z₂ z₄ z₃
    (by simpa [hd'] using hd2.map φ)
    (fun g h => by rw [← repOn_twMat]; exact x.2.2 g h) (fun g h => by rw [← repOn_twMat]; exact y.2.2 g h)
    (fun h hh => sub_eq_zero.1 (hb h hh)) g₀
  have hχ0 : χ g₀ ^ D.R.r - 1 = (X.l i : A) ^ nu X i * φ ((u : (X.O0 i)ˣ) : X.O0 i) := by
    have e := congrArg φ hu
    rw [map_sub, map_pow, map_one, map_mul, map_pow, map_natCast] at e
    rw [hχ, ← pow_mul, e]
  intro h hh h' hh' a b
  have e := key h hh h' hh' a b
  rw [hχ0] at e
  refine ((u.isUnit.map φ).mul_right_eq_zero).1 ?_
  linear_combination e

end GlobalTheory.NewPrime.FormVanish
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.comparison_cocycles_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  first | exact @GlobalTheory.NewPrime.comparison_cocycles | exact GlobalTheory.NewPrime.comparison_cocycles | (intros; apply GlobalTheory.NewPrime.comparison_cocycles <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_lambda_algebra_hom_evaluation : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  first | exact @GlobalTheory.NewPrime.LamHom.exists_lamHom | exact GlobalTheory.NewPrime.LamHom.exists_lamHom | (intros; apply GlobalTheory.NewPrime.LamHom.exists_lamHom <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.setup_and_antiHom_of_kills : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  first | exact @GlobalTheory.NewPrime.setup_of_factor | exact GlobalTheory.NewPrime.setup_of_factor | (intros; apply GlobalTheory.NewPrime.setup_of_factor <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.noInvDual_of_setup_of_isDual_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  first | exact @GlobalTheory.NewPrime.noInvDual_of_setup | exact GlobalTheory.NewPrime.noInvDual_of_setup | (intros; apply GlobalTheory.NewPrime.noInvDual_of_setup <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.pairing_equivariant_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  first | exact @GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | exact GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | (intros; apply GlobalTheory.NewPrime.PairEquiv.pairing_equivariant <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.perfect_pairing_finite_module_rows_criterion : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n), Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A), (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  first | exact @GlobalTheory.NewPrime.charDual_cogenerator | exact GlobalTheory.NewPrime.charDual_cogenerator | (intros; apply GlobalTheory.NewPrime.charDual_cogenerator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.selmerCocycles_scalarChange_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  first | exact @GlobalTheory.NewPrime.ScalarChange.selC_transfer | exact GlobalTheory.NewPrime.ScalarChange.selC_transfer | (intros; apply GlobalTheory.NewPrime.ScalarChange.selC_transfer <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.localDuality_perfect_pair_finite_modules : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  first | exact @GlobalTheory.LocalPair.local_pair | exact GlobalTheory.LocalPair.local_pair | (intros; apply GlobalTheory.LocalPair.local_pair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.det_ne_zero_of_lowestForm_ne_zero_presentation : ∀ (A B : Type) [CommRing A] [CommRing B] (π : B →+* A) (x y : B) (μ : Type) [Fintype μ] (a a' : ℕ) (Φ' : Matrix (Fin a') (Fin a') B) (u t : μ → Fin a' → B) (η : μ → B) (Φ : Matrix (Fin a) (Fin a) A) (E : Matrix (Fin a) (Fin a') A) (U : μ → Fin a → A) (k : μ → A) (l₀ : Fin a), Function.Surjective π → (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) → π x = 0 → π y = 0 → x * x = 0 → y ^ Fintype.card μ = 0 → (∀ f, x * y ^ (Fintype.card μ - 1) * f = 0 → π f = 0) → (∀ j, π (η j) = 1) → (∀ j, x • u j - (y * η j) • t j ∈ what₂ Φ') → what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) = ⊤ → (∀ b, (Φ * E) b ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → (∀ j, (fun c => π (u j c)) - Matrix.vecMul (U j) E ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → ∑ j, k j • (fun c => π (t j c)) ∈ what₂ (Φ'.map π) → ∑ j, k j * ∑ c, U j c * Φ.adjugate c l₀ ≠ 0 → Φ'.det ≠ 0 := by
  first | exact @GlobalTheory.LowDet.det_ne_zero | exact GlobalTheory.LowDet.det_ne_zero | (intros; apply GlobalTheory.LowDet.det_ne_zero <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX



theorem _root_.GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.latY_lattice | exact GlobalTheory.Pass.LocDual.OneX.latY_lattice | (intros; apply GlobalTheory.Pass.LocDual.OneX.latY_lattice <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.JSW

theorem jacobi_trudi_det_pad_zeros {A : Type*} [CommRing A] (h : ℕ → A) (h0 : h 0 = 1) {m n : ℕ} (hmn : m ≤ n)
    (l : Fin m → ℕ) : jtDet n h (padTo hmn l) = jtDet m h l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold jtDet
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun i j : Fin (m + k) =>
    if ((padTo hmn l i : ℤ) - i + j) < 0 then 0 else h (((padTo hmn l i : ℤ) - i + j).toNat)).submatrix
      finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply, padTo]
    have hj := j.2
    simp
    omega
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hM, Matrix.toBlocks₂₂, padTo, h0]
    · intro i j hij
      simp only [hM, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right, padTo]
      have : (j : ℕ) < i := hij
      simp
      omega
  have h11 : M.toBlocks₁₁ = Matrix.of fun i j : Fin m =>
      if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat) := by
    ext i j
    simp [hM, Matrix.toBlocks₁₁, padTo]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h22, h11, mul_one]

theorem schur_padTo_eq_jtDet {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ) :
    schur n (padTo hmn l) = jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  rw [schur_eq_jtDet]
  exact jacobi_trudi_det_pad_zeros _ (MvPolynomial.hsymm_zero _ _) hmn l

end GlobalTheory.JSW
end
end
