module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions

section Defs

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev Ev : Type := Fv F v ⊗[F] E

abbrev OEv : Subalgebra (v.adicCompletionIntegers F) (Ev E v) :=
  integralClosure (v.adicCompletionIntegers F) (Ev E v)

abbrev Wv (M : ℕ) : Type := Fin M → Ev E v

variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsSelfDualIn (U : Submodule (Ev E v) (Wv E v M)) (L : Submodule (OEv E v) (Wv E v M)) : Prop :=
  L.FG ∧ Submodule.span (Ev E v) (L : Set (Wv E v M)) = U ∧
    ∀ y : Wv E v M, y ∈ L ↔ (y ∈ U ∧ ∀ z ∈ L, hR (Fv F v) σ J z y ∈ OEv E v)

def IsSelfDualLat (L : Submodule (OEv E v) (Wv E v M)) : Prop := IsSelfDualIn v σ J ⊤ L

def perp (x : Wv E v M) : Submodule (Ev E v) (Wv E v M) where
  carrier := {y | hR (Fv F v) σ J x y = 0}
  zero_mem' := by simp [hR, Formalism.UG.hform]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, hR, Formalism.UG.hform] at *
    have : ∀ i j, sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * (c • a) j =
        c * (sigR (Fv F v) σ (x i) * JR (Fv F v) J i j * a j) := by
      intro i j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [this, ← Finset.mul_sum, ha, mul_zero]

def perpLat (x : Wv E v M) (L : Submodule (OEv E v) (Wv E v M)) :
    Submodule (OEv E v) (Wv E v M) :=
  (perp v σ J x).restrictScalars (OEv E v) ⊓ L

def act (g : HA (Fv F v) σ J) (y : Wv E v M) : Wv E v M :=
  (HA.mat (Fv F v) σ J g : Matrix (Fin M) (Fin M) (Ev E v)).mulVec y

open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) in
variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act_one (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Wv E v M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J 1 y = y := by
  have h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J 1 = 1 := rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, h, Units.val_one, Matrix.one_mulVec]

open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) in
variable {E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act_mul (g g' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J)
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Wv E v M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J (g * g') y =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act v σ J g' y) := by
  have h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J (g * g') =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J g * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J g' := rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.act,
    h, Units.val_mul, Matrix.mulVec_mulVec]

def latStab (L : Submodule (OEv E v) (Wv E v M)) : Subgroup (HA (Fv F v) σ J) where
  carrier := {g | ∀ y, y ∈ L ↔ act v σ J g y ∈ L}
  one_mem' := by intro y; rw [act_one]
  mul_mem' := by
    intro a b ha hb y
    rw [act_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (act v σ J g⁻¹ y)
    rw [← act_mul, mul_inv_cancel, act_one] at this
    exact this.symm

def vecStab (x : Wv E v M) : Subgroup (HA (Fv F v) σ J) :=
  MulAction.stabilizer (HA (Fv F v) σ J) (fun _ : Fin 1 => x)

def latUnitaryIn (U : Submodule (Ev E v) (Wv E v M)) (L' : Submodule (OEv E v) (Wv E v M)) :
    Subgroup (U ≃ₗ[Ev E v] U) where
  carrier := {u | (∀ y z : U, hR (Fv F v) σ J (u y : Wv E v M) (u z : Wv E v M) =
      hR (Fv F v) σ J (y : Wv E v M) (z : Wv E v M)) ∧
    ∀ y : U, (y : Wv E v M) ∈ L' ↔ (u y : Wv E v M) ∈ L'}
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun y z => (ha.1 (b y) (b z)).trans (hb.1 y z), fun y => (hb.2 y).trans (ha.2 (b y))⟩
  inv_mem' := by
    intro u hu
    refine ⟨fun y z => ?_, fun y => ?_⟩
    · have := hu.1 (u.symm y) (u.symm z)
      rw [u.apply_symm_apply, u.apply_symm_apply] at this
      exact this.symm
    · have := hu.2 (u.symm y)
      rw [u.apply_symm_apply] at this
      exact this.symm

def Xbeta (β : Fv F v) : Set (Wv E v M) := {x | x ≠ 0 ∧ qR (Fv F v) σ J x = β}

def sphere (L : Submodule (OEv E v) (Wv E v M)) (β : Fv F v) : Set (Wv E v M) :=
  {x | x ∈ L ∧ qR (Fv F v) σ J x = β}

def HasOrthonormalBasis (L : Submodule (OEv E v) (Wv E v M)) : Prop :=
  ∃ e : Module.Basis (Fin M) (OEv E v) L,
    gramR (Fv F v) σ J (fun i => (e i : Wv E v M)) = 1

def UnitVectorClaims (L : Submodule (OEv E v) (Wv E v M)) (β : Fv F v) : Prop :=

  (sphere v σ J L β).Nonempty ∧

  (∀ x ∈ sphere v σ J L β,
    Submodule.span (OEv E v) {x} ⊔ perpLat v σ J x L = L ∧
    Disjoint (Submodule.span (OEv E v) {x}) (perpLat v σ J x L) ∧
    IsSelfDualIn v σ J (perp v σ J x) (perpLat v σ J x L)) ∧

  (∀ x ∈ sphere v σ J L β, ∀ x' ∈ sphere v σ J L β,
    ∃ g ∈ latStab v σ J L, act v σ J g x = x') ∧

  (∀ x ∈ sphere v σ J L β,
    latStab v σ J L ⊓ vecStab v σ J x = latStab v σ J (perpLat v σ J x L) ⊓ vecStab v σ J x ∧
    ∃ φ : ↥(latStab v σ J L ⊓ vecStab v σ J x) ≃*
        latUnitaryIn v σ J (perp v σ J x) (perpLat v σ J x L),
      ∀ (g : ↥(latStab v σ J L ⊓ vecStab v σ J x)) (y : perp v σ J x),
        (((φ g : perp v σ J x ≃ₗ[Ev E v] perp v σ J x) y : perp v σ J x) : Wv E v M) =
          act v σ J g y) ∧

  (∀ x ∈ Xbeta v σ J β, ∀ x' ∈ Xbeta v σ J β, ∃ g : HA (Fv F v) σ J, act v σ J g x = x') ∧

  (∀ x ∈ Xbeta v σ J β,
    (∃ L₁, IsSelfDualLat v σ J L₁ ∧ x ∈ L₁) ∧ ∃ L₂, IsSelfDualIn v σ J (perp v σ J x) L₂)

end Defs

def UnramifiedOrSplit {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal

def SelfDualLatticeLemmas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 1 ≤ M → IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)), UnramifiedOrSplit E v →
  ∀ (L : Submodule (OEv E v) (Wv E v M)), IsSelfDualLat v σ J L →
    HasOrthonormalBasis v σ J L ∧
    (∀ L' : Submodule (OEv E v) (Wv E v M), IsSelfDualLat v σ J L' →
      ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ act v σ J g y ∈ L') ∧
    ∀ β : (v.adicCompletionIntegers F)ˣ,
      UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)

section Basic₂

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)


open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.sigR_mem {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v := by
  let φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v →ₐ[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v :=
    Algebra.TensorProduct.map (AlgHom.id (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ
  have h := (hz : IsIntegral (v.adicCompletionIntegers F) z).map
    (φ.restrictScalars (v.adicCompletionIntegers F))
  exact h

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Places

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsInertAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime

def IsSplitAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.primesOver (𝓞 E)).ncard = 2

def IsEtaAt (v : HeightOneSpectrum (𝓞 F)) (η : ℤ) : Prop :=
  (IsInertAt F E v ∧ η = -1) ∨ (IsSplitAt F E v ∧ η = 1)

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

abbrev maxOrder (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)

def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1

def IsDualExp (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (c : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp c

def dualIndex (v : HeightOneSpectrum (𝓞 F)) (c : ℤ) : ℝ := (resCard F v : ℝ) ^ c

end Places

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

def IsSelfDualLattice (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v

def latTup (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Fv F v ⊗[F] E) := {X | X 0 ∈ L}

def qTup (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : Fv F v := qR (Fv F v) σ J (X 0)

end Lattice

def densityValue (N : ℝ) (q : ℕ) (η : ℤ) (M : ℕ) : ℝ :=
  N ^ ((1 / 2 : ℝ) - M) * (1 - (η : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ)))

def SelfDualLatticeDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 1 ≤ M → IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (η : ℤ), IsEtaAt F E v η →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar F v ψ →
  AllSome (IsDualExp F v ψ) fun c =>
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ (latTup v L) = ENNReal.ofReal (dualIndex F v c ^ (-(M : ℤ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal (dualIndex F v c ^ (-(1 / 2 : ℝ))) ∧
    ∀ β : Fv F v, Valued.v β = 1 →
      (∀ (U : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (B : Set (Fv F v))
          (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
          {X | qTup σ J v X ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B →
          IsFibreFamily μ (qTup σ J v) id U ν B fib →
          fib β (latTup v L) =
            ENNReal.ofReal (densityValue (dualIndex F v c) (resCard F v) η M) ∧
          ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t (latTup v L) = fib β (latTup v L)) ∧
      (∀ g : Fv F v → ℂ,
          IsContDensityOn μ (qTup σ J v) id ν {t | t ≠ 0} ((latTup v L).indicator 1) g →
          ∀ t : Fv F v, Valued.v (t - β) < 1 →
            g t = (densityValue (dualIndex F v c) (resCard F v) η M : ℂ))

end GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Defs

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UnramifiedPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal


open Classical in
def eta (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsField (Fv F v ⊗[F] E) then -1 else 1

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

def intToEv (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
  (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype

def maxOrder (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  letI := (intToEv F E v).toAlgebra
  (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.mem_maxOrder (v : HeightOneSpectrum (𝓞 F))
    (z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v ↔
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.intToEv F E v).IsIntegralElem z :=
  Iff.rfl

variable {F E}

def IsSelfDualLattice (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F))
    (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y : Fin M → Fv F v ⊗[F] E, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v

def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1

def DualExponent (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (n : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp n

end Defs

def LocalDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)), UnramifiedPlace F E v →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar v ψ → ∀ n : ℤ, DualExponent v ψ n →
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ {X | X 0 ∈ L} = ENNReal.ofReal ((resCard F v ^ n) ^ (-(M : ℝ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal ((resCard F v ^ n) ^ (-(1 / 2 : ℝ))) ∧
    ∀ (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib →
    ∀ β : Fv F v, Valued.v β = 1 →
      fib β {X | qR (Fv F v) σ J (X 0) = β ∧ X 0 ∈ L} =
        ENNReal.ofReal ((resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) *
          (1 - eta F E v ^ M * (resCard F v ^ M)⁻¹)) ∧
      ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t {X | X 0 ∈ L} = fib β {X | X 0 ∈ L}


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    1 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (M : ℕ) (hM : 1 ≤ M) :
    0 < 1 - _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ := by
  have hq := _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard F v
  have hqM : 1 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := one_lt_pow₀ hq (by omega)
  have hpos : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := by linarith
  have hsign : |_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v| = 1 := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta
    split_ifs <;> norm_num
  have hle := le_abs_self (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)
  rw [abs_mul, abs_pow, hsign, one_pow, one_mul, abs_inv, abs_of_pos hpos] at hle
  have hinv : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqM
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
end
end
