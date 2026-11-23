module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle002
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem succ_le_ringKrullDim_of_algebraicIndependent {σ : Type} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {n : ℕ}
    (x : Fin n → MvPolynomial σ ℚ ⧸ qIdeal P) (hx : AlgebraicIndependent ℚ x) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hdom := isDomain_qQuot P hP hH
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ qIdeal P)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℚ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℚ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℚ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℚ ⧸ qIdeal P)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℚ ⧸ qIdeal P) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℚ ⧸ qIdeal P) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  letI := (ratHom P).toAlgebra
  haveI := ratHom_isLocalization P
  refine succ_le_ringKrullDim_of_isLocalization
    (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) ?_ n
    (le_trans (by exact_mod_cast hns) hdim)
  intro p hp hdis
  refine exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective p hp ?_
  ext m
  simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Submodule.mem_bot]
  constructor
  · intro hm
    by_contra hm0
    refine Set.disjoint_left.mp hdis ⟨m, mem_nonZeroDivisors_of_ne_zero hm0, rfl⟩ ?_
    simpa [eq_intCast] using hm
  · rintro rfl
    simp

end ReciprocityTheory.ChartRestriction.G.Geo
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section LemSec

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem coordIdeal_isPrime [IsDomain Ω] (x : ι → Ω) : (coordIdeal o x).IsPrime :=
  RingHom.ker_isPrime _

end LemSec

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]

theorem mixedDisc_one (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ => f) y = (fderiv ℝ (fderiv ℝ f) y (Pi.single 0 1) (Pi.single 0 1) +
      fderiv ℝ (fderiv ℝ f) y (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1)) /
        (2 * Real.pi) := by
  have hre : ∀ u v : ℝ, ((((u : ℂ) + Complex.I * (v : ℂ)) / 4).re) = u / 4 := by
    intro u v
    simp [Complex.div_ofNat_re]
  rw [maDensity, mixedDisc_one]
  simp only [cxHessian, hre]
  have := Real.pi_pos
  simp
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Algebra

abbrev MRingOver (R : Type*) [CommRing R] (ι : K → Type*) := MvPolynomial (Σ k, ι k) R

abbrev MRing (ι : K → Type*) := MRingOver ℤ ι

variable {R : Type*} [CommRing R]

def IsMultiHomog (s : MRingOver R ι) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k

def IsMultiHomogIdeal (P : Ideal (MRingOver R ι)) : Prop :=
  ∃ S : Set (MRingOver R ι), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MRingOver R ι)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MRingOver R ι) ∉ W

def IsMultiProjPrime (P : Ideal (MRingOver R ι)) : Prop :=
  P.IsPrime ∧ IsMultiHomogIdeal P ∧ IsRelevant P

def IsHorizontal (P : Ideal (MRing ι)) : Prop :=
  P.comap (C : ℤ →+* MRing ι) = ⊥

def IsArithVar (P : Ideal (MRing ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime P ∧ IsHorizontal P ∧
    ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

def divSupp (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : Set (Ideal (MRingOver R ι)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}


open scoped Classical in
open Classical in
def multAt (J W : Ideal (MRingOver R ι)) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRingOver R ι ⧸ J))).toNat
  else 0

theorem divSupp_finite [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : (divSupp P s).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun _ hW => hW.1

def divCycle [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) :
    Ideal (MRingOver R ι) →₀ ℕ := by
  classical
  exact Finsupp.ofSupportFinite
    (fun W => if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0)
    ((divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (ite_eq_right h))

def charOf (W : Ideal (MRing ι)) : ℕ :=
  (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs


open scoped Classical in
open Classical in
def geoNum : (n : ℕ) → Ideal (MRing ι) → (Fin n → K → ℤ) → ℤ
  | 0, V, _ =>
    if h : IsRelevant V then
      ((Module.length ℤ
        (MRing ι ⧸ (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, (h k).choose⟩ : MRing ι) - 1)))).toNat : ℤ)
    else 0
  | n + 1, V, a =>
    if h : IsRelevant V then
      ∑ k, a (Fin.last n) k *
        ∑ᶠ W ∈ divSupp V (X ⟨k, (h k).choose⟩),
          (multAt (V ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) W : ℤ) * geoNum n W (Fin.init a)
    else 0

end Algebra

section Complex

def mcPts (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}


variable (ι) in
structure HermLine (ι : K → Type*) where

  a : K → ℤ

  h : ((Σ k, ι k) → ℂ) → ℝ
  pos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < h z
  smul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * h z

def IsSmoothHerm (A : HermLine ι) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def HermLine.tensor (A B : HermLine ι) : HermLine ι where
  a := A.a + B.a
  h z := A.h z * B.h z
  pos z hz := mul_pos (A.pos z hz) (B.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ (A.a + B.a) k = ‖c k‖ ^ A.a k * ‖c k‖ ^ B.a k := fun k =>
      zpow_add₀ (norm_ne_zero_iff.mpr (hc k)) _ _
    simp only [this, Finset.prod_mul_distrib]
    ring

def segre (z : (Σ k, ι k) → ℂ) : ((k : K) → ι k) → ℂ :=
  fun i => ∏ k, z ⟨k, i k⟩

variable {e : ℕ}

def fibre (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ mcPts P, segre z = w ∧ Ψ w = Fin.cons 1 y}

def IsSheet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y'

def sheetDensity (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0

def ptsIntegralAt (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w

def IsGoodProj (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ mcPts P, Ψ (segre z) ≠ 0

def ptsIntegral (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ then
    ptsIntegralAt P hΨ.choose φ g
  else 0

def logNorm (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z)

def arInt (P : Ideal (MRing ι)) (s : MRing ι) (A : HermLine ι) (L : Fin e → HermLine ι) : ℝ :=
  ptsIntegral P (fun j z => Real.log ((L j).h z)) (logNorm A s)

end Complex

section Constructors

def HermLine.ofMetrics (m : ∀ k, ConeMetric (C := ℂ) (ι := ι k)) (a : K → ℤ) : HermLine ι where
  a := a
  h z := ∏ k, (m k).ρ (fun i => z ⟨k, i⟩) ^ a k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    exact zpow_pos ((m k).pos _ fun h0 => hi (congrFun h0 i)) _
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (fun i => c k * z ⟨k, i⟩) = c k • fun i => z ⟨k, i⟩ := rfl
    simp only [this, (m k).smul, mul_zpow]

def HermLine.ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (-u z)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]

end Constructors

section Family

def recR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ := by
  classical
  exact (∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W n L
        else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))) -
    arInt P s A L

def IsIntersectionFamily (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) : Prop :=
  (∀ P n (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → I P n (L ∘ σ) = I P n L) ∧
  (∀ P n (L : Fin n → HermLine ι) (A B : HermLine ι), IsArithVar P (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P (n + 1) (Fin.snoc L (A.tensor B)) =
        I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)) ∧
  (∀ P n (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (a : K → ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
      (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ P →
      I P (n + 1) (Fin.snoc L A) = recR I P L A s)

end Family

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
