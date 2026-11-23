module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotNuSigma

def Target : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G),
    (SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA) →
    (SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB) →
    (∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) →
    SigmaFinite ν

end PI.QuotNuSigma
end
end

section

namespace PI

def LBoundRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re)

def ZetaBoundRight : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)

def LInvRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

end PI
end

section

open NumberField

namespace PI

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

end PI
end

section

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UJClassFin

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  unfold cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL n A →* GL n B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end Group

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)

def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Adeles

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)

def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  UJ (sigR R σ) (JR R J)

def HFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  (UJ (σ : E →+* E) J).map (bc (inclR R))

def HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HR R σ J) :=
  (HFin R σ J).subgroupOf (HR R σ J)

def HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))

def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1

end Alg

section Vol

def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

def latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) : AddSubgroup (Fin M → Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def finMat (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) :=
  ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

theorem mapAlg_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) A) : (X * Y).map φ = X.map φ * Y.map φ :=
  Matrix.map_mul (f := φ.toRingHom)

theorem mapAlg_one {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} : (1 : Matrix (Fin n) (Fin n) A).map φ = 1 :=
  Matrix.map_one _ (map_zero φ) (map_one φ)

theorem HA_mat_mul (h h' : HA (AF F) σ J) :
    HA.mat (AF F) σ J (h * h') = HA.mat (AF F) σ J h * HA.mat (AF F) σ J h' :=
  rfl

theorem HA_mat_one : HA.mat (AF F) σ J 1 = 1 := rfl

theorem finMat_mul (h h' : HA (AF F) σ J) : finMat σ J (h * h') = finMat σ J h * finMat σ J h' := by
  unfold finMat
  rw [HA_mat_mul, Units.val_mul]
  exact mapAlg_mul _ _ _

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  unfold finMat
  rw [HA_mat_one, Units.val_one]
  exact mapAlg_one _

def SFin (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  mul_mem' := by
    intro h h' hh hh' y
    rw [finMat_mul, ← Matrix.mulVec_mulVec, hh' y]
    exact hh _
  one_mem' := by intro y; rw [finMat_one, Matrix.one_mulVec]
  inv_mem' := by
    intro h hh y
    have e : (finMat σ J h).mulVec ((finMat σ J h⁻¹).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
    have := hh ((finMat σ J h⁻¹).mulVec y)
    rw [e] at this
    exact this.symm

abbrev GamG : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

end Vol

def UJClassFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ (n : ℕ) (g : Fin n → HA (AF F) σ J),
      (∀ x, ∃ i, ∃ γ : GamG σ J, ∃ k : SFin σ J L, x = (γ : HA (AF F) σ J) * g i * k) ∧
      (∀ i j (γ γ' : GamG σ J) (k k' : SFin σ J L),
        (γ : HA (AF F) σ J) * g i * k = (γ' : HA (AF F) σ J) * g j * k' → i = j)

end PI.UJClassFin
end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def UnitaryApproxDefs.IsHerm (σ : A →+* A) (J : Matrix n n A) : Prop := UnitaryApproxDefs.cT σ J = J

theorem UnitaryApproxDefs.cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    UnitaryApproxDefs.cT σ (M * N) = UnitaryApproxDefs.cT σ N * UnitaryApproxDefs.cT σ M := by
  simp [UnitaryApproxDefs.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem UnitaryApproxDefs.cT_one (σ : A →+* A) : UnitaryApproxDefs.cT σ (1 : Matrix n n A) = 1 := by
  unfold UnitaryApproxDefs.cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UnitaryApproxDefs.UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [UnitaryApproxDefs.cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc UnitaryApproxDefs.cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = UnitaryApproxDefs.cT σ (b : Matrix n n A) * (UnitaryApproxDefs.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = UnitaryApproxDefs.cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, UnitaryApproxDefs.cT_one, Matrix.one_mul, Matrix.mul_one]
end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def UnitaryApproxDefs.inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UnitaryApproxDefs.UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) := UnitaryApproxDefs.UJ (UnitaryApproxDefs.sigR σ R) (J.map (UnitaryApproxDefs.inclE (F := F) R))

def UnitaryApproxDefs.tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def UnitaryApproxDefs.intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end Points

end PI

end
end

section

open NumberField

namespace PI.ClassNumImQ

def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤

def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)

end PI.ClassNumImQ
end

section

namespace PI

open Matrix

def PowBddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)

end PI
end

section

open NumberField

noncomputable section

namespace PI

def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def OkpInert : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p

end PI
end
end

section

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerIso

def IsIsom {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Prop :=
  ∀ x y, ∑ w, algebraMap K E (g x w) * cj (algebraMap K E (g y w))
      = algebraMap K E (∑ a, Algebra.trace K E (x a * cj (y a)))

def AtP {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n] (M : Set E)
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → E, (∀ a, x a ∈ M) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : K) * g x w ∈ (algebraMap (𝓞 K) K).range) ∧
  ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g.symm v a ∈ M

def detRel {K E : Type} [Field K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    (g g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : K :=
  LinearMap.det ((g₀.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))

def ordK {K : Type} [Field K] [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  -WithZero.log (𝔭.valuation K x)

def IsConj (K : Type) {E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) : Prop :=
  (∀ x, cj (cj x) = x) ∧ (∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') ∧
    ∃ k : K, cj (algebraMap K E k) ≠ algebraMap K E k

def DetOrdIndep : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] (n : Type) [Fintype n] (M : Set E) (p : ℕ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (g g' g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
    p.Prime → ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal → AtP M g p → AtP M g' p →
      ordK 𝔭 (detRel g g₀) = ordK 𝔭 (detRel g' g₀)

def DetOrdFin : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), I ≠ 0 →
    ∀ (S : ℕ → Prop) (pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (gp : ℕ → ((Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))) (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
      (∀ p, p.Prime → S p → ((p : ℕ) : 𝓞 K) ∈ (pp p).asIdeal) →
      (∀ p, p.Prime → S p → AtP {x : E | x ∈ I} (gp p) p) →
        {p : ℕ | p.Prime ∧ S p ∧ ordK (pp p) (detRel (gp p) g₀) ≠ 0}.Finite

def SplitsAt (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P ∧ ∃ a b : 𝓞 K,
    cj (algebraMap K E (a : K)) = algebraMap K E (b : K) ∧ a ∈ P ∧ b ∉ P

def SelfDualI (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Prop :=
  ∀ y : E, y ∈ I ↔ ∀ x ∈ I, Algebra.trace K E (x * cj y) ∈ (algebraMap (𝓞 K) K).range

end PI.KerIso
end
end

section

namespace PI


open Classical in
def DiagRank : Prop := by
  classical
  exact ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

end PI
end
