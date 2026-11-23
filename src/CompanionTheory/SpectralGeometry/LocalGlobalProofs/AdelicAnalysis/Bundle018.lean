module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle012
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityFormula
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealGaussianFourierTransform
public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SizeScale

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem continuous_size (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem size_nonneg (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tup_nonneg {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _

theorem size_add_le (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) :
    sizeInf b (x + y) ≤ sizeInf b x + sizeInf b y := by
  unfold sizeInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [map_add (f := _)]
  exact norm_add_le _ _

theorem size_zero (b : Module.Basis (Fin d) F E) : sizeInf b (0 : Ainf F ⊗[F] E) = 0 := by
  unfold sizeInf
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun v _ => ?_
  have h0 : ((0 : Fin d →₀ Ainf F) k) v = 0 := rfl
  rw [map_zero, h0, norm_zero]

theorem size_sum_le {ι : Type} (b : Module.Basis (Fin d) F E) (s : Finset ι)
    (f : ι → Ainf F ⊗[F] E) : sizeInf b (∑ c ∈ s, f c) ≤ ∑ c ∈ s, sizeInf b (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [size_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add_le b _ _).trans (by gcongr)

theorem coord_le_size (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) (j : Fin d)
    (v : InfinitePlace F) :
    ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖ ≤ sizeInf b y := by
  unfold sizeInf
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖
      ≤ ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖ :=
        Finset.single_le_sum
          (f := fun w => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ _ := Finset.single_le_sum
        (f := fun k => ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem repr_mul (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis (Ainf F) b).repr x i *
        (Algebra.TensorProduct.basis (Ainf F) b).repr y j *
          algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hBB : ∀ i j, B.repr (B i * B j) k = algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
    intro i j
    simp [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y, Finset.sum_mul_sum]

  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_mul_smul_comm, map_smul,
  Finsupp.smul_apply, hBB, smul_eq_mul]

theorem exists_size_mul_le (b : Module.Basis (Fin d) F E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Ainf F ⊗[F] E, sizeInf b (x * y) ≤ K * sizeInf b x * sizeInf b y := by
  obtain ⟨S₀, hS₀⟩ := (Set.finite_range (fun p : Fin d × Fin d × Fin d × InfinitePlace F =>
    ‖(algebraMap F (Ainf F) (b.repr (b p.1 * b p.2.1) p.2.2.1)) p.2.2.2‖)).bddAbove
  set S := |S₀| with hS
  have hs : ∀ i j k v, ‖(algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖ ≤ S := fun i j k v =>
    (hS₀ ⟨(i, j, k, v), rfl⟩).trans (le_abs_self _)
  refine ⟨(d : ℝ) * d * S, by positivity, fun x y => ?_⟩
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hpt : ∀ k (v : InfinitePlace F), ‖B.repr (x * y) k v‖ ≤
      (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
    intro k v
    have hev : B.repr (x * y) k v =
        ∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v := by
      rw [repr_mul b x y k]
      have := map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
        (fun i => ∑ j, B.repr x i * B.repr y j * algebraMap F (Ainf F) (b.repr (b i * b j) k))
        Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) _ _
    rw [hev]
    calc ‖∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖
        ≤ ∑ i, ∑ j : Fin d, ‖B.repr x i v‖ * sizeInf b y * S := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (coord_le_size b y j v) (norm_nonneg _))
            (hs i j k v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (size_nonneg b y))
      _ = (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc sizeInf b (x * y) = ∑ k, ∑ v : InfinitePlace F, ‖B.repr (x * y) k v‖ := rfl
    _ ≤ ∑ k : Fin d, ∑ v : InfinitePlace F, (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun v _ => hpt k v
    _ = (d : ℝ) * ((d : ℝ) * S * sizeInf b y * ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.mul_sum]
    _ = (d : ℝ) * d * S * sizeInf b x * sizeInf b y := by
        have : sizeInf b x = ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖ := Finset.sum_comm
        rw [this]; ring

end

theorem size_rmul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (C : Set (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))), IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ g ∈ C, ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, sizeTup b (rmul (Ainf F) X g) ≤ c * sizeTup b X := by
  intro F E _ _ _ _ _ σ _ d b n M C hC
  obtain ⟨K, hK0, hK⟩ := exists_size_mul_le b
  have hcont : Continuous fun g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      ∑ c, ∑ a, sizeInf b (g c a) :=
    continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun a _ =>
      (continuous_size b).comp (continuous_id.matrix_elem c a)
  obtain ⟨D, hD⟩ := (hC.image hcont).bddAbove
  refine ⟨K * |D| + 1, by positivity, fun g hg X => ?_⟩
  have hg' : ∀ c, ∑ a, sizeInf b (g c a) ≤ |D| := fun c =>
    (Finset.single_le_sum (f := fun c => ∑ a, sizeInf b (g c a))
      (fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _) (Finset.mem_univ c)).trans
      ((hD ⟨g, hg, rfl⟩).trans (le_abs_self _))
  calc sizeTup b (rmul (Ainf F) X g)
      = ∑ a, ∑ i, sizeInf b (∑ c, X c i * g c a) := rfl
    _ ≤ ∑ a, ∑ i, ∑ c, K * sizeInf b (X c i) * sizeInf b (g c a) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
          (size_sum_le b _ _).trans (Finset.sum_le_sum fun c _ => hK _ _)
    _ = ∑ i, ∑ c, K * sizeInf b (X c i) * ∑ a, sizeInf b (g c a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ c, K * sizeInf b (X c i) * |D| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hg' c) (mul_nonneg hK0 (size_nonneg b _))
    _ = K * |D| * sizeTup b X := by
        unfold sizeTup
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (K * |D| + 1) * sizeTup b X := by
        nlinarith [tup_nonneg b X]

end GlobalTheory.CompanionTheory.SW.SizeScale
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons α (fun _ => 0)) (fun j => Fin.cons (c j) (X j))

def scl {K : Type} [Mul K] {N n : ℕ} (u : K) (y : Fin n → Fin N → K) : Fin n → Fin N → K :=
  fun a i => y a i * u

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def s0 {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S 0 0)

def cvec {n : ℕ} (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :
    Fin n → R ⊗[F] E :=
  fun j => ((((a (s0 R S))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * S 0 j.succ

def schurM (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => S i.succ j.succ -
    sigR R σ (cvec R t a S i) * inclR R (algebraMap F E t) * cvec R t a S j


open scoped Classical in
open Classical in
def schur (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1)) : HermR R σ n :=
  if h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n then ⟨_, h⟩ else 0

theorem schur_coe (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n) :
    (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a S := by
  simp [schur, h]

def Bset (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ ∧
    IsUnit (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibS (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (Bset R σ t a B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def Pint (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ≥0∞ :=
  ∫⁻ y₀, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def Preal (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ :=
  ∫ y₀, ∫ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def sTil (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : HA R σ (blockOne (algebraMap F E t) J) :=
  s (scl ((((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) y)

def chi {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : ℝ≥0∞ :=
  ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
    φ (Fin.cons (y 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a y)
      (fun j => Fin.cons (c j) (X j)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam)

def Uset (B₀ : Set R) (a : R → Rˣ) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' Bset R σ t a B₀)

def Unt (R : Type) [CommRing R] [Algebra F R] (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

def Mid {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n,
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure StageData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.RMulGram

theorem mul_regroup {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i

theorem colsM_injective {M n : ℕ} {X Y : Fin n → Fin M → R ⊗[F] E}
    (h : colsM R X = colsM R Y) : X = Y := by
  funext a i
  exact congrFun (congrFun h i) a

theorem gramR_eq_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1

theorem colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by
  ext i a
  simp only [rmul, colsM, Matrix.mul_apply]

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]

theorem actTup_rmul {M n : ℕ} (k : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  funext a i
  simp only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end

theorem rmul_gram_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩

end GlobalTheory.CompanionTheory.SW.RMulGram
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.lattice_matrix_determinant_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F → (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), |(gM (ι := ι) ρ (fun v => b v) N).det| = ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | exact GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.siegel_matrix_symmetric_posdef_imag : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧ ∀ x : ι × InfinitePlace F → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) = gauss B ρ P τ (cur x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | exact GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss <;> assumption)
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧ (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧ ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | exact GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | (intros; apply GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic <;> assumption)
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_fibre_family_on_open_orbit : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X], (∀ (q : Q) (v : V), g (q • v) = q • g v) → ∀ (χ χ' : Q →* ℝ≥0), Continuous χ → Continuous χ' → (∀ q : Q, μ.map (fun v => q • v) = χ q • μ) → (∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) → ∀ b₀ : X, IsOpenEmbedding (fun q : Q => q • b₀) → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν (Set.range fun q : Q => q • b₀) fib := by
  first | exact @GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit | exact GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit | (intros; apply GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.real_gaussian_fourier_transform : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 → P.PosDef → P * S⁻¹ * P = S → ∃ c : ℂ → ℂ, ∀ τ : ℂ, 0 < τ.im → ‖c τ‖ = (Real.sqrt ‖τ‖ ^ Fintype.card ι)⁻¹ ∧ c τ * c (-τ⁻¹) = 1 ∧ Integrable (fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))) ∧ ∀ y : ι → ℝ, ((Real.sqrt |S.det| : ℝ) : ℂ) * ∫ x : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ)) = c τ * Complex.exp ((Real.pi : ℂ) * Complex.I * ((-τ⁻¹).re : ℂ) * ((y ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ) - (Real.pi : ℂ) * ((-τ⁻¹).im : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GaussOne.fourier_gaussian_real_place | exact GlobalTheory.CompanionTheory.SW.GaussOne.fourier_gaussian_real_place | (intros; apply GlobalTheory.CompanionTheory.SW.GaussOne.fourier_gaussian_real_place <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.closed_subgroup_quotient_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | exact GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | (intros; apply GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset <;> assumption)
end
