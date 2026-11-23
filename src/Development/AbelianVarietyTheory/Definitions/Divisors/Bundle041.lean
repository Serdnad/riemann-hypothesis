module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue GlobalTheory.ArInt GlobalTheory.VolBr

namespace GlobalTheory.HSAmp

section Gram

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type}

def gram (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ᶠ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ

def cmb [Fintype ι] (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : ℝ := ‖∑ i, c i * v σ y i‖ ^ 2

def l2 [Fintype ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) : ℝ :=
  ∑ᶠ σ, ∫ y, cmb v c σ y ∂μ σ

def bergmanDensity [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) : ℝ :=
  (∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))).re

structure IsFam (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) : Prop where

  finite : Finite S

  integrable : ∀ σ i j, Integrable (fun y => v σ y i * (starRingEnd ℂ) (v σ y j)) (μ σ)

end Gram

def ellCount {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (R : ℝ) : ℕ :=
  {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.ncard

variable {k : Type} [CommRing k] {X : Scheme.{0}}

structure VolDens (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  dens : AlgChart p σ D → CxPts p σ → ℝ

  cont : ∀ c, ContinuousOn (dens c) c.e.source

  pos : ∀ c, ∀ y ∈ c.e.source, 0 < dens c y

  trans : ∀ c c', ∀ y ∈ c.e.source, y ∈ c'.e.source → dens c y = ‖transDet c.e c'.e y‖ ^ 2 * dens c' y

def VolDens.meas {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ω.dens c y)

def VolDens.IsRatio {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (ω : VolDens p σ D) {B : LB X} (φ : Weight p σ B)
    (ρ : CxPts p σ → ℝ) : Prop :=
  Continuous ρ ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, c.chernDens φ y = ρ y * ω.dens c y

structure SmFn (p : X ⟶ Sp k) where

  u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ

  cInf : ∀ σ y, CInfAt (u σ) y

  conj : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))

def SmFn.smul {p : X ⟶ Sp k} (t : ℝ) (u : SmFn p) : SmFn p where
  u σ y := t * u.u σ y
  cInf σ y := (u.cInf σ y).const_mul t
  conj σ σ' i y y' h hy := congrArg (t * ·) (u.conj σ σ' i y y' h hy)

def SmFn.pull {p : X ⟶ Sp k} (u : SmFn p) {Y : Scheme.{0}} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : SmFn q where
  u σ y := u.u σ (Points.PtsOver.map π hπ _ y)
  cInf σ _ := CInfAt.pull π hπ (u.cInf σ _)
  conj σ σ' _ _ _ h _ := u.conj σ σ' PUnit.unit _ _ ((congrArg (· ≫ π) h).trans (Category.assoc _ _ _)) mem_ptsIn_top

abbrev up {p : X ⟶ Sp k} (L : HermLB p) (u : SmFn p) : HermLB p := L.raise u.u u.cInf u.conj

variable [IsIntegral X] {p : X ⟶ Sp k}

def upperParabolic (P : Pair p) (u : SmFn p) : Pair p := ⟨up P.L u, P.A, P.r, P.r', P.hr, P.hr'⟩

def val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℂ :=
  ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y *
    (Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ)

theorem norm_val (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    ‖val P a b σ y f‖ = P.nu a b σ y f := by
  rw [val, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rfl

def vals (P : Pair p) (a b : ℤ) {ι : Type} (f : ι → X.functionField) (σ : k →+* ℂ) (y : CxPts p σ) (i : ι) : ℂ :=
  val P a b σ y (f i)

def NV (P : Pair p) (a b : ℤ) (f : X.functionField) : Set X :=
  {x | ∀ i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → UnitAt x (P.loc a b f i j)}

def ballIn (P : Pair p) (Λ : AddSubgroup X.functionField) (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ Λ ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

theorem ballIn_H (P : Pair p) (a b : ℤ) (R : ℝ) : ballIn P (P.H a b) a b R = P.Bl a b R := rfl

structure GoodFam (P : Pair p) (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) : Prop where

  le : ∀ m : ℕ, Λ m ≤ P.H m 1

  fg : ∀ m, (Λ m).FG

  small : ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → Λ m ≤ AddSubgroup.closure (ballIn P (Λ m) m 1 (C ^ m))

  rank : Tendsto (fun m : ℕ => (Module.finrank ℤ (Λ m) : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g)

structure Gens (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField) : Prop where

  pos : 0 < e

  mem : ∀ l, x l ∈ P.H e 0

  cover : ∀ z : X, ∃ l, z ∈ NV P e 0 (x l)

def IsCan (P : Pair p) {D : ℕ} (e n : ℕ) (x : Fin (D + 1) → X.functionField) (u : SmFn p) : Prop :=
  ∀ σ y, u.u σ y = ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))

def ratF {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) : Subfield K :=
  Subfield.closure (Set.range fun j : Fin D => x j.succ / x 0)

def ratR {K : Type} [Field K] {D : ℕ} (x : Fin (D + 1) → K) (l : Fin (D + 1)) : Subring K :=
  Subring.closure (Set.range fun j => x j / x l)


omit [IsIntegral X] in
def fib (X : Scheme.{0}) (ℓ : ℕ) : Set X := {x | ringChar (X.residueField x) = ℓ}

section Inhabitants

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder

omit [IsIntegral X]


end Inhabitants

end GlobalTheory.HSAmp
end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair.AdjModel

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

theorem exists_place {Q : Subring K} (hQ : IsLocModel c Q) {t : Q} (ht : Prime t) :
    ∃ S : Place c, S.IsPrimeOf Q ∧ S.ord (t : K) = 1 ∧
      ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ord (t : K) = 0 := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := by
    letI := c0.toAlgebra
    haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k Q
  haveI : IsFractionRing Q K := by
    refine IsFractionRing.of_field Q K fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  let p : Ideal Q := Ideal.span {t}
  haveI : p.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).2 ht
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q K := Localization.subalgebra.ofField K p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField K _ hp
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap Q A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap Q A t ≠ 0 := fun e => ht.ne_zero (Subtype.ext (congrArg (fun z : A => (z : K)) e))
  have hnf : ¬ IsField A := fun hf => ht0 (by
    have := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hm] at this
    exact Ideal.span_singleton_eq_bot.1 this)
  haveI : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).2 (show (IsLocalRing.maximalIdeal A).IsPrincipal from ⟨_, hm⟩)
  haveI : IsFractionRing A K := Localization.subalgebra.isFractionRing_ofField K _ hp
  let V : ValuationSubring K :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, ?_, fun P hP hne => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · exact S.ord_irreducible (t := algebraMap Q A t)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm)
  · by_contra h0
    have htK : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
    have h1 : 0 ≤ P.ord (t : K) := (P.ord_nonneg_iff htK).2 (hP.1 _ t.2)
    refine hne (ValuationSubring.eq_of_le_of_ne_top P.ring (fun f hf => ?_) S.ring_ne_top)
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 f hf
    have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
      have hd' : b = t * d := congrArg Subtype.val hd
      have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
      have := (P.ord_nonneg_iff hd0).2 (hP.1 _ d.2)
      rw [hd', P.ord_mul htK hd0] at hbo
      omega
    obtain ⟨g, hg⟩ := (hu _ hbp).exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
    rw [this]
    exact A.mul_mem (A.algebraMap_mem ⟨a, ha⟩) g.2


end GlobalTheory.FieldPair.AdjModel
end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

theorem mono (h : AdjKlt c n T S η φ) (hT : T ≤ T') : AdjKlt c n T' S η φ :=
  ⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 := by
  refine ⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

theorem adjKlt_of_lt_disc (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0)
    (h : ∀ E : Place c, E.Contains T → E.ring ≠ S.ring → -1 < E.disc η φ) :
    AdjKlt c n T S η φ :=
  ⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ =>
    h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩

end GlobalTheory.FieldPair
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

def NonUnit (R : Subring K) (f : K) : Prop := f ∈ R ∧ (f = 0 ∨ f⁻¹ ∉ R)

def RatRes (c : k →+* K) (R : Subring K) : Prop := ∀ r ∈ R, ∃ a, NonUnit R (r - c a)

def Dominates (ρ : K →+* L) (B : Subring L) (O : Subring K) : Prop :=
  ∀ f ∈ O, ρ f ∈ B ∧ (NonUnit O f → NonUnit B (ρ f))

structure IsEtTower (cK : k →+* K) (R : Subring K) (cL : k →+* L) (T : Subring L) {r : ℕ}
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) : Prop where

  base : IsLocModel cK R

  normal : IsIntegrallyClosed R

  top : IsLocModel cL T

  const : ∀ a, (ι ⟨cK a, base.const_mem a⟩ : L) = cL a

  retr : ∀ a, ψ (ι a) = a

  zero : ∀ i, ψ (τ i) = 0

  etale : (MvPolynomial.eval₂Hom ι τ).FormallyEtale


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_iff {R : Subring K} (f : R) :
    _root_.GlobalTheory.FieldPair.NonUnit R f ↔ ¬ IsUnit f := by
  constructor
  · rintro ⟨-, h0 | hinv⟩ hu
    · have hf : f = 0 := Subtype.ext (by simpa using h0)
      exact not_isUnit_zero (hf ▸ hu)
    · obtain ⟨u, rfl⟩ := hu
      have hmul : ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]
        rfl
      rw [inv_eq_of_mul_eq_one_right hmul] at hinv
      exact hinv (u⁻¹ : Rˣ).1.2
  · intro hnu
    refine ⟨f.2, ?_⟩
    by_contra h
    push_neg at h
    apply hnu
    exact IsUnit.of_mul_eq_one (b := (⟨_, h.2⟩ : R)) (Subtype.ext (by simp [h.1]))


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_zero (R : Subring K) : _root_.GlobalTheory.FieldPair.NonUnit R 0 :=
  ⟨R.zero_mem, Or.inl rfl⟩


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.not_nonUnit_one (R : Subring K) : ¬ _root_.GlobalTheory.FieldPair.NonUnit R 1 := by
  rintro ⟨-, h | h⟩
  · exact one_ne_zero h
  · exact h (by rw [inv_one]; exact R.one_mem)


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.Dominates.trans {M : Type} [Field M] {ρ : K →+* L} {σ : L →+* M}
    {O : Subring K} {B : Subring L} {C : Subring M} (h : _root_.GlobalTheory.FieldPair.Dominates ρ B O)
    (h' : _root_.GlobalTheory.FieldPair.Dominates σ C B) :
    _root_.GlobalTheory.FieldPair.Dominates (σ.comp ρ) C O := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  obtain ⟨h3, h4⟩ := h' (ρ f) h1
  exact ⟨h3, fun hn => h4 (h2 hn)⟩


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.ratRes_self : _root_.GlobalTheory.FieldPair.RatRes (RingHom.id k) ⊤ := by
  intro r _
  exact ⟨r, by rw [RingHom.id_apply, sub_self]; exact _root_.GlobalTheory.FieldPair.nonUnit_zero ⊤⟩

end GlobalTheory.FieldPair
end
end
