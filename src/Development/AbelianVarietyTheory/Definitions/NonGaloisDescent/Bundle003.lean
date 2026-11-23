module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles

@[expose] public section

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

def fourB {V : Type} [MeasurableSpace V] (μ : Measure V) (B : V → V → ℂ) (f : V → ℂ) (y : V) : ℂ :=
  ∫ x, f x * B x y ∂μ

def SelfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (B : V → V → ℂ) : Prop :=
  μ.IsAddHaarMeasure ∧ ∀ f : V → ℂ, IsTest f → ∀ y, fourB μ B (fourB μ B f) y = f (-y)

def IsTestRep {G X : Type} [Group G] [TopologicalSpace X] (W : G → (X → ℂ) → X → ℂ) : Prop :=
  (∀ g f, IsTest f → IsTest (W g f)) ∧ (∀ f, IsTest f → W 1 f = f) ∧
    (∀ g h f, IsTest f → W (g * h) f = W g (W h f)) ∧
    ∀ g (c : ℂ) f f', IsTest f → IsTest f' → W g (c • f + f') = c • W g f + W g f'

def nS {k : Type} [CommRing k] (z : k) : SpecialLinearGroup (Fin 2) k := ⟨!![1, z; 0, 1], by simp [Matrix.det_fin_two]⟩

def mS {k : Type} [CommRing k] (s : kˣ) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two]⟩

def wS (k : Type) [CommRing k] : SpecialLinearGroup (Fin 2) k := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

structure Et (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] where
  K : Type
  L : Type
  [crK : CommRing K]
  [algK : Algebra F K]
  [finK : Module.Finite F K]
  [redK : IsReduced K]
  [topK : TopologicalSpace K]
  [mtK : IsModuleTopology F K]
  [trK : IsTopologicalRing K]
  [lcK : LocallyCompactSpace K]
  [mK : MeasurableSpace K]
  [bK : BorelSpace K]
  [crL : CommRing L]
  [stL : StarRing L]
  [algFL : Algebra F L]
  [algKL : Algebra K L]
  [algEL : Algebra E L]
  [twK : IsScalarTower F K L]
  [twE : IsScalarTower F E L]
  [topL : TopologicalSpace L]
  [mtL : IsModuleTopology F L]
  [mL : MeasurableSpace L]
  [bL : BorelSpace L]
  push : Algebra.IsPushout F E K L
  star_K : ∀ x : K, star (algebraMap K L x) = algebraMap K L x
  star_E : ∀ y : E, star (algebraMap E L y) = algebraMap E L (star y)

attribute [instance] Et.crK Et.algK Et.finK Et.redK Et.topK Et.mtK Et.trK Et.lcK Et.mK Et.bK Et.crL Et.stL Et.algFL
  Et.algKL Et.algEL Et.twK Et.twE Et.topL Et.mtL Et.mL Et.bL

namespace Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def absK (t : A.K) : ℝ := by
  classical exact if h : IsUnit t then (distribHaarChar A.K h.unit : ℝ) else 0

def etaK (t : A.K) : ℂ := eta (Algebra.norm F t)

def psiK (ψ : AddChar F ℂ) (t : A.K) : ℂ := ψ (Algebra.trace F A.K t)

def NL (y : A.L) : A.K := Algebra.norm A.K y

def kerK (ψ : AddChar F ℂ) (y y' : A.K) : ℂ := A.psiK ψ (y * y')

def kerL (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) : ℂ := A.psiK ψ (x * Algebra.trace A.K A.L (star y' * y))

def orbK (μK : Measure A.K) (φ' : A.K × A.K → ℂ) (a : A.K) : ℂ :=
  ∫ t in {t : A.K | IsUnit t}, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK

def fourK (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  ∫ b', ∫ c', φ' (b', c') * A.psiK ψ (p.1 * c' + b' * p.2) ∂μK ∂μK

def orbL (ν : Measure (unitary A.L)) (φ : A.L → ℂ) (y₀ : A.L) : ℂ := ∫ t : unitary A.L, φ (t.1 * y₀) ∂ν

def IsNat (μK : Measure A.K) (μL : Measure A.L) (ν : Measure (unitary A.L)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ (s : A.K → A.L), (∀ y : A.L, IsUnit y → A.NL (s (A.NL y)) = A.NL y) →
    ∀ h : A.L → ℂ, IsTest h → tsupport h ⊆ {y | IsUnit y} →
      ∫ y, h y * ((A.absK (A.NL y) : ℂ))⁻¹ ∂μL =
        ∫ a in {a : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a}, A.orbL ν h (s a) * ((A.absK a : ℂ))⁻¹ ∂μK

structure Meas (ψ : AddChar F ℂ) where
  μK : Measure A.K
  μL : A.Kˣ → Measure A.L
  ν : Measure (unitary A.L)
  sdK : SelfDual μK (A.kerK ψ)
  sdL : ∀ x : A.Kˣ, SelfDual (μL x) (A.kerL ψ x)
  nat : A.IsNat μK (μL 1) ν

def IsWeil (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) : Prop :=
  IsTestRep W ∧ ∀ φ, IsTest φ →
    (∀ z y, W (nS z) φ y = A.psiK ψ (z * x * A.NL y) * φ y) ∧
    (∀ (s : A.Kˣ) y, W (mS s) φ y = ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)) ∧
    ∀ y, W (wS A.K) φ y = γ * fourB μ (A.kerL ψ x) φ y

def OK : Set A.K := {z | ∀ i, ‖(LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i‖ ≤ 1}

def InI (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) : Prop :=
  (∃ U ∈ 𝓝 (0 : A.K), ∀ g k : SpecialLinearGroup (Fin 2) A.K,
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) i j ∈ U) → Φ (g * k) = Φ g) ∧
    ∀ z (s : A.Kˣ) g, Φ (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * Φ g

def abelian₂ (μK : Measure A.K) (ψ : AddChar F ℂ) (a : A.K) (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (c : F) : ℂ :=
  ∫ z in {z : A.K | c • z ∈ A.OK}, Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) ∂μK

def tilde (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (c u : A.K) : ℂ :=
  ∫ b, φ' (b, c) * A.psiK ψ (u * b) ∂μK

def jHyp (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (g : SpecialLinearGroup (Fin 2) A.K) : ℂ :=
  ∫ t, A.tilde μK ψ φ' (t * g 1 0) (t * g 1 1) * A.etaK t ∂μK

def IsIsom {r : ℕ} (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) : Prop :=
  ∀ y y', star (j y) ⬝ᵥ j y' = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y')

def IsReps (S : Set A.Kˣ) : Prop := ∀ a : A.Kˣ, ∃! x : A.Kˣ, x ∈ S ∧ ∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y

def IsGen {r : ℕ} (τ : A.K) (p : Fin r → F) : Prop :=
  LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ)) ∧ Module.finrank F A.K = r ∧
    τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0

def invK {r : ℕ} (τ : A.K) (p : Fin r → F) (lam : F) (a : A.K) : Inv r F :=
  (p, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * a), lam)

end Et

def WeilField : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E), IsField A.K → IsField A.L → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∀ ω : A.K → ℂ,
    (∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)) →
    ∃ γ W, A.IsWeil ψ x ω μ γ W

def WeilEt : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∃ γ W, A.IsWeil ψ x A.etaK μ γ W

def RankOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (S : Set A.Kˣ), A.IsReps S →
    ∀ (γ : A.Kˣ → ℂ) (W : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ),
    (∀ x ∈ S, A.IsWeil ψ x A.etaK (m.μL x) (γ x) (W x)) →
    ∀ (φ' : A.K × A.K → ℂ) (φ : A.Kˣ → A.L → ℂ) (κ : ℂ), IsTest φ' → (∀ x ∈ S, IsTest (φ x)) →
    (∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y) →
    ∀ x ∈ S, ∀ y : A.L, IsUnit y →
      κ * A.orbK m.μK (A.fourK m.μK ψ φ') (x * A.NL y) =
        γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y

def GammaOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∀ (ω : A.K → ℂ) (γ : ℂ) W, A.IsWeil ψ x ω μ γ W → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → γ = 1

end GlobalTheory.JR
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Basic

variable {K : UQ} (B : InvAlg K)

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
private theorem sigma_smul_eq_conj_smul (e : K.E) (v : B.A) : B.σ (e • v) = K.c e • B.σ v := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.trace_sigma (u : B.A) :
    Algebra.trace K.E B.A (B.σ u) = K.c (Algebra.trace K.E B.A u) := by
  classical
  set b := Module.finBasis K.E B.A
  let φ : B.A ≃ₗ[K.E] (Fin (Module.finrank K.E B.A) → K.E) :=
    { toFun := fun v i => K.c (b.repr (B.σ v) i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun e v => by ext i; simp [sigma_smul_eq_conj_smul, K.c_c]
      invFun := fun f => B.σ (∑ i, K.c (f i) • b i)
      left_inv := fun v => by
        simp only [K.c_c, b.sum_repr, B.σ_σ]
      right_inv := fun f => by
        ext i
        simp [B.σ_σ, Finsupp.single_apply, K.c_c] }
  let b' := Module.Basis.ofEquivFun φ
  have hb' (j) : b' j = B.σ (b j) := by
    simp [b', Module.Basis.coe_ofEquivFun, φ, Pi.single_apply, apply_ite B.σ]
  have hrepr (w : B.A) (i) : b'.repr w i = K.c (b.repr (B.σ w) i) := by
    simp [b', φ]

  rw [Algebra.trace_eq_matrix_trace b' (B.σ u), Algebra.trace_eq_matrix_trace b u,
  Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hb', hrepr, ← map_mul, B.σ_σ]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_left (x y z : B.A) (e : K.E) :
    B.herm x (e • y) z = e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_right (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [sigma_smul_eq_conj_smul, mul_smul_comm, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_symm (x : B.A) (hx : B.σ x = x) (y z : B.A) :
    B.herm x z y = K.c (B.herm x y z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [← _root_.GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, hx, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_mul_left (x u y z : B.A) :
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_norm (x u y z : B.A) :
    B.herm (x * (u * B.σ u)) y z = B.herm x (u * y) (u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ]
  congr 1
  ring

end GlobalTheory.UnitLemma.Basic
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial Filter Topology

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def UU (x w : B.A) : ℕ := Nat.card {L : B.X x // w ∈ (L : Submodule K.O B.A)}

def Lin : Set (Submodule K.O B.A) :=
  {M | IsLat K.O K.E M ∧ (∀ y ∈ M, B.g * y ∈ M) ∧ ∀ y ∈ M, B.σ y ∈ M}

def sgnLat (M : Submodule K.O B.A) : ℚ :=
  let m : Fin (Module.finrank K.E B.A) → B.A :=
    Classical.epsilon fun m => Submodule.span K.O (Set.range m) = M
  K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
    Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det

def GG (u : B.A) : ℚ :=
  ∑ᶠ M ∈ {M ∈ B.Lin | u ∈ M ∧ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range}, B.sgnLat M

def rho (w : B.A) : ℕ :=
  Nat.card {k : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
    IsIntegral K.O ((((Quotient.out k : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A)}

def LieReg : Prop := B.σ B.g = B.g ∧ B.P.Separable

def Plus (x : B.A) : Prop := IsUnit x ∧ B.σ x = x

def LinLim (a : K.O) (x : B.A) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (B.GG (x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
    atTop (𝓝 ℓ)

end InvAlg

def UQ.Small (K : UQ) (a : K.O) : Prop :=
  a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal K.O ∧ K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a

def CountIdentity : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ x w : B.A, B.Plus x → IsUnit w →
    B.GG (x * (w * B.σ w)) = (B.UU x w : ℚ)

def UnitaryLimit : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ x : B.A, B.Plus x →
    Tendsto (fun k : ℕ => (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
      atTop (𝓝 (B.N x : ℝ))

def LinearDescent : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable →
    ∀ a : K.O, K.Small a → ∀ (ℓ : (B₁.prod B₂).A → ℝ) (ℓ₁ : B₁.A → ℝ) (ℓ₂ : B₂.A → ℝ),
    (∀ x, (B₁.prod B₂).Plus x → (B₁.prod B₂).LinLim a x (ℓ x)) →
    (∀ x, B₁.Plus x → B₁.LinLim a x (ℓ₁ x)) → (∀ x, B₂.Plus x → B₂.LinLim a x (ℓ₂ x)) →
    ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      (-(K.q : ℝ)) ^ (val K.O (resultant B₁.P B₂.P)) *
        ((∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep) * ∑ᶠ k : B₂.Cl, ℓ₂ k.rep)

end GlobalTheory.UnitLemma
end
end

section

noncomputable section
namespace GlobalTheory.PhiGam.Model
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section
variable (k : Type) [Field k]

theorem algebraMap_eq (c : k) : algebraMap k k⸨X⸩ c = HahnSeries.C c := by rw [HahnSeries.algebraMap_apply', ← HahnSeries.ofPowerSeries_C]; rfl

theorem smul_eq (c : k) (x : k⸨X⸩) : c • x = algebraMap k k⸨X⸩ c * x := by rw [algebraMap_eq, HahnSeries.C_mul_eq_smul]

instance towerA : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun c x y => by
  rw [smul_eq, smul_eq k c, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerB : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun c a y => by
  rw [smul_eq k c, Algebra.smul_def (c • a), Algebra.smul_def a, Algebra.smul_def c, map_mul, mul_assoc]
  rfl⟩

end

section
variable {k : Type} [Field k]

end

section
variable {k : Type} [Field k]

theorem gmult_top_bot {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (x : k) :
    gmult T ⊤ ⊥ x = Module.finrank k (T.maxGenEigenspace x) := by
  have hS : (⨆ m : ℕ, (⊥ : Submodule k U).comap ((T - algebraMap k (Module.End k U) x) ^ m))
      = T.maxGenEigenspace x := by
    apply le_antisymm
    · refine iSup_le fun m y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one] at hy
      exact (Module.End.mem_maxGenEigenspace T x y).mpr ⟨m, hy⟩
    · intro y hy
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T x y).mp hy
      refine Submodule.mem_iSup_of_mem m ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one]
      exact hm
  unfold gmult
  rw [top_inf_eq, hS]
  have hb : (⊥ : Submodule k U).submoduleOf (T.maxGenEigenspace x) = ⊥ := by
    ext y
    simp [Submodule.submoduleOf]
  rw [hb]
  exact (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

end

end GlobalTheory.PhiGam.Model
end
end

section

noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

end Det

def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

end GlobalTheory.Pat
end
end
