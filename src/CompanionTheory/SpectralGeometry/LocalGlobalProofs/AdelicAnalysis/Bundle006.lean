module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import Mathlib.RingTheory.Artinian.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle001
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def toA (x : ι → F) : ι → A F := fun j => algebraMap F (A F) (x j)

theorem oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)

theorem oh_zero : (0 : A F) ∈ Oh F := fun _ => zero_mem _

theorem oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v => neg_mem (hx v)


variable (ι F) in
def latN (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨z, hz, e'⟩ := hb i
    exact ⟨y + z, oh_add hy hz, by simp [e, e', mul_add]⟩
  zero_mem' := fun i => ⟨0, oh_zero, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, oh_neg hy, by simp [e]⟩

def indC (N : ℕ) (a : ι → F) : (ι → A F) → ℂ :=
  Set.indicator {x | x - toA a ∈ latN F ι N} fun _ => 1

def emb (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) : ι × InfinitePlace F → ℝ :=
  fun p => ρ p.2 (x p.1)

def cur (x : ι × InfinitePlace F → ℝ) : InfinitePlace F → ι → ℝ := fun w i => x (i, w)

def DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  blockDiagonal fun w => B.map (ρ w)

def ZM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℂ :=
  blockDiagonal fun w => fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

def EM (ρ : InfinitePlace F → (F →+* ℝ)) (b : InfinitePlace F → 𝓞 F) :
    Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  fun w v => ρ w (b v : F)

def gM [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  (N : ℝ) • ((1 : Matrix ι ι ℝ) ⊗ₖ EM ρ b)

theorem sum_rho_eq_trace {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (c : F) :
    ∑ w, ρ w c = ((Algebra.trace ℚ F c : ℚ) : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := c)
  have hb : Function.Bijective
      (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) := by
    constructor
    · intro w v h
      have : w.embedding = v.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding v, this]
    · intro σ
      refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
      have hr : (InfinitePlace.mk σ.toRingHom).IsReal := hT.isReal _
      have he := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp hr)
      ext x
      show ((InfinitePlace.mk σ.toRingHom).embedding) x = σ x
      rw [he]
      rfl
  have h2 : ∑ σ : F →ₐ[ℚ] ℂ, σ c = ∑ w : InfinitePlace F, w.embedding c := by
    rw [← (Equiv.ofBijective _ hb).sum_comp]
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [hρ]
  rw [← h2, ← h1]
  simp

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThetaUD

variable {F : Type} [Field F] [NumberField F]

theorem form_mulVec {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
  conv_rhs => rw [← h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_map {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f Q x i).symm

theorem trace_eq_sum (hT : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ w, ((ρ w y : ℝ) : ℂ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by simp
  rw [h2, h1]
  symm
  refine Fintype.sum_bijective (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) ?_ _ _ ?_
  · constructor
    · intro w w' h
      have : w.embedding = w'.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', this]
    · intro σ
      have hr : (InfinitePlace.mk (σ : F →+* ℂ)).IsReal := hT.isReal _
      have hc : ComplexEmbedding.IsReal (σ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 hr
      refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
      ext x
      have := InfinitePlace.embedding_mk_eq_of_isReal hc
      simp [this]
  · intro w
    simp [hρ]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_add (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => τ w + (c w : ℝ)) y = gauss B ρ P τ y *
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ w, ((c w : ℂ) * ((y w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
  unfold gauss
  rw [← Complex.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  push_cast
  ring

theorem gauss_sq (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by
  unfold gauss
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : (((c w : ℝ) : ℂ) ^ 2 * τ w).re = c w ^ 2 * (τ w).re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have him : (((c w : ℝ) : ℂ) ^ 2 * τ w).im = c w ^ 2 * (τ w).im := by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

theorem term_U (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  obtain ⟨hOf, hOi⟩ := hO
  set t : F := x ⬝ᵥ (B *ᵥ x) with ht
  have hfin : qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      algebraMap F (A F) (1 / 2 * t) := by
    unfold qf
    rw [form_mulVec gf (Bf B) hOf]
    have := form_map (algebraMap F (A F)) B x
    unfold Bf hf
    rw [this, map_mul]
  have hinf : ∀ w, (gi w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (x j))) =
      ρ w t := by
    intro w
    rw [form_mulVec (gi w) _ (hOi w), form_map]
  have hphase : ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) = 1 := by
    rw [← map_mul, hψ.2, trace_eq_sum hT ρ hρ, ← Complex.exp_add]
    have : ∑ w, ((ρ w (b * (1 / 2 * t)) : ℝ) : ℂ) = (1 / 2) * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [map_mul, map_div₀, map_one, map_ofNat]
      push_cast
      ring
    rw [this]
    have h0 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) +
        (Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold thTerm opU
  rw [gauss_add B ρ P τ (fun w => ρ w b), hfin]
  simp only [hinf]
  calc _ = (ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)))) *
        (φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) *
          gauss B ρ P τ fun w => gi w *ᵥ fun j => ρ w (x j)) := by ring
    _ = _ := by rw [hphase, one_mul]

theorem term_D (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (a : F) (x : ι → F) :
    thTerm B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) x =
      thTerm B ρ P gf gi φ τ (a • x) := by
  unfold thTerm opD
  rw [gauss_sq B ρ P τ (fun w => ρ w a)]
  have h1 : (algebraMap F (A F) a • gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      gf *ᵥ fun j => algebraMap F (A F) ((a • x) j) := by
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  have h2 : (fun w => ρ w a • gi w *ᵥ fun j => ρ w (x j)) =
      fun w => gi w *ᵥ fun j => ρ w ((a • x) j) := by
    funext w
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  intro F _ _ ψ hψ ι _ _ M B ρ P hQ gf gi hO φ τ
  refine ⟨fun b => ?_, fun a ha => ?_, fun c => ?_⟩
  · unfold theta
    exact tsum_congr fun x => term_U ψ hψ M B ρ P hQ gf gi hO φ τ b x
  · unfold theta
    simp only [term_D]
    exact (MulAction.toPerm (Units.mk0 a ha) : Equiv.Perm (ι → F)).tsum_eq (thTerm B ρ P gf gi φ τ)
  · unfold theta
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [thTerm, mul_assoc]

end GlobalTheory.CompanionTheory.SW.ThetaUD
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition

private theorem coe_n {R : Type} [CommRing R] (b : R) :
    ((nMat b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl

private theorem coe_m {R : Type} [CommRing R] (a : Rˣ) :
    ((mMat a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] := rfl

private theorem coe_w {R : Type} [CommRing R] :
    ((wMat : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] := rfl

private theorem SL2_eq_of_entries_eq_matrix {R : Type} [CommRing R] {g : SL(2, R)} {p q r s : R}
    {h : SL(2, R)} (hh : (h : Matrix (Fin 2) (Fin 2) R) = !![p, q; r, s])
    (h0 : g 0 0 = p) (h1 : g 0 1 = q) (h2 : g 1 0 = r) (h3 : g 1 1 = s) : g = h := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)
  rw [hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]

theorem decompositions : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  intro R _ g
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  refine ⟨?_, ?_, ?_, hw⟩
  · intro c hc
    have hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := by simp
    have hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R) := by simp
    have hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R) := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]
    generalize ((c⁻¹ : Rˣ) : R) = u at hu
    rw [hc] at hdet ⊢
    congr
    · linear_combination (g 0 0) * hu
    · linear_combination (g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet
    · ring
    · linear_combination (g 1 1) * hu
  · intro a ha
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    rw [hw]
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · linear_combination (g 1 0) * hu
    · linear_combination (g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet
  · intro a ha hc
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha, hc] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · ring
    · linear_combination (g 1 1) * hu - u * hdet

end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.finite_field_quadratic_form_point_count : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | exact GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | (intros; apply GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.symmetric_invertible_exists_posdef_congruence : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 → ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | exact GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | (intros; apply GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm <;> assumption)
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.haar_invariant_under_transvection : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | exact GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | (intros; apply GlobalTheory.CompanionTheory.SW.transvection_map_addHaar <;> assumption)
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.matrix_transvection_diagonal_decomposition : ∀ (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K), A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D * (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  first | exact @GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec | exact GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec | (intros; apply GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec <;> assumption)
end
