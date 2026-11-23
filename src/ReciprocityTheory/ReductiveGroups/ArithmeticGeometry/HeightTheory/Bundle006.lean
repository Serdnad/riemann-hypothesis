module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Continuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A) (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))

structure AxH : Type where
  nonempty : Nonempty ι
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0
  WW_span : d.WW = Submodule.span (𝓞 K) (Set.range d.w)
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  Thp_span : d.Thp = Submodule.span (𝓞 K) (Set.range d.thp)
  thp_mem : ∀ k c, d.thp k c ∈ 𝒜 c d.wF
  et_mem : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde)
  firstSectionMem : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1)
  secondSectionMem : ∀ c, d.ta2 c ∈ 𝒜 c d.G2
  et_ne : ∀ c, d.et c ≠ 0
  firstSectionNeZero : ∀ c, d.ta1 c ≠ 0
  secondSectionNeZero : ∀ c, d.ta2 c ≠ 0
  ord_mul : ∀ c v, d.admitted c v → ∀ {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.ord c v (G + G') (f * g) = d.ord c v G f + d.ord c v G' g
  ord_smul : ∀ c v, d.admitted c v → ∀ {G : WT} {f : A c} (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    ((d.ord c v G (a • f) : ℤ) : WithTop ℤ) = v a + (d.ord c v G f : WithTop ℤ)
  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  nrm_conj : ∀ c (G : WT) (f : A c) (P : Ω c →+* ℂ),
    d.nrm c G f ((starRingEnd ℂ).comp P) = d.nrm c G f P
  bdd : ∀ (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)
  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))
  ord_nonneg_WW : ∀ c v, d.admitted c v → ∀ f ∈ d.WW, f c ≠ 0 → 0 ≤ d.ord c v d.wL (f c)
  ord_nonneg_Thp : ∀ c v, d.admitted c v → ∀ f ∈ d.Thp, f c ≠ 0 → 0 ≤ d.ord c v d.wF (f c)
  ord_nonneg_et : ∀ c v, d.admitted c v → 0 ≤ d.ord c v (d.n1 • d.wde) (d.et c)
  ordDoubleFirstSection_nonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v ((2 : ℕ) • d.G1) (d.ta1 c)
  ordSecondSectionNonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v d.G2 (d.ta2 c)
  a3' : ∀ c {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite
  sel : Fin d.del → Fin d.np
  a4 : ∃ e : ∀ c, A c, (∀ c, e c ∈ 𝒜 c d.wF ∧ e c ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) K,
      (∀ c, ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) K, (∀ c, d.sH c q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) K, ∀ c, d.sH c q * y c = ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)))
  i_ge : 1 ≤ d.i
  g_zero_ge_ask_sum : 1 ≤ d.g0
  cc_nonneg : 0 ≤ d.cc
  cc_le : d.cc ≤ 1
  ccg0 : d.cc * d.g0 ≤ 1 / 2
  size_L : 1 ≤ d.wsize d.wL
  DF_le : d.DF ≤ d.wsize d.wL
  rw_le : Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1)
  nK_le : Real.log (Module.finrank ℚ K) ≤ d.PO
  rd_le : Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ≤ d.PO
  P_ge : 1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO
  a13 : ∀ c (sg : K →+* ℂ) {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm c G f P)) d.sphMeasure

variable {𝒜}

def FinitePlaceHyp : Prop :=
  (∀ la, 0 ≤ d.nu la) ∧
  ((Function.support d.nu).Finite) ∧
  ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤ d.PN * d.wsize d.wL) ∧
  (∀ c v la, d.admitted c v → IsOver (K := K) v la →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        (ramIdx (K := K) v la : ℝ) * d.nu la +
          d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def TrivialPlaceHyp : Prop :=
  (∀ c v, d.admitted c v → IsTrivOn K v →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def HtLAM : Prop :=
  (∀ c, ∀ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 →
      -(d.PP0' * d.n96 * d.wsize d.wL) ≤
        meanK fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c)))

def HtSup : Prop :=
  (meanK (fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) ≤ d.Gc * d.wsize d.wL) ∧
  (∀ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp k))) ≤ d.Gc * d.wsize d.wF) ∧
  (meanK (fun sg => Real.log (d.supN sg ((2 : ℕ) • d.G1) d.ta1)) ≤
      2 * d.PI4 * d.D * d.wsize d.wL) ∧
  (meanK (fun sg => Real.log (d.supN sg d.G2 d.ta2)) ≤ d.PI4 * d.D * d.wsize d.wL)

def HeightIntegralEstimateTrivialPlace : Prop :=
  (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet)

def HeightIntegralBoundEstimate : Prop :=
  (∀ c (P : Ω c →+* ℂ),
      -Real.log (d.be c P) ≤
        d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo)

def PHc : ℝ := 2 * d.PH + d.Gc

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

noncomputable def liftY : FractionRing (MvPolynomial σ L) →+* FractionRing (MvPolynomial σ E) :=
  IsFractionRing.lift (A := MvPolynomial σ L)
    (g := (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map (algebraMap L E)))
    ((IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map_injective _ (algebraMap L E).injective))

theorem basis_extend [FiniteDimensional L E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n L E) :
    letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
      (liftY (L := L) (E := E) (σ := σ)).toAlgebra;
    ∃ b' : Module.Basis n (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)),
      (∀ i, b' i = algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (b i))) ∧
      ∀ e : E, Algebra.leftMulMatrix b' (algebraMap (MvPolynomial σ E)
          (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e)) =
        (Algebra.leftMulMatrix b e).map (algebraMap L (FractionRing (MvPolynomial σ L))) := by

  try intro _
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := (liftY (L := L) (E := E) (σ := σ)).toAlgebra
  letI : Algebra (MvPolynomial σ L) (MvPolynomial σ E) := MvPolynomial.algebraMvPolynomial
  classical
  have hlift : ∀ q : MvPolynomial σ L, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.map (algebraMap L E) q) := by
    intro q
    show liftY (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) = _
    simp only [liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hsmul : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      q • P = MvPolynomial.map (algebraMap L E) q * P := fun q P => by
    rw [Algebra.smul_def]; rfl
  have himg : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (q • P) = algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P := by
    intro q P; rw [hsmul, map_mul, hlift]
  have hmem : ∀ P : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro P

    rw [PolynomialCoordinateBasis.eq_sum_crd b P, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [himg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (FractionRing (MvPolynomial σ L)) (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial σ L))
      Finset.univ g
    have hd' : ∀ j, ∃ a : MvPolynomial σ L, algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) a = (d : MvPolynomial σ L) • g j :=
      fun j => hd j (Finset.mem_univ j)
    choose a ha using hd'
    have h0 : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E)) = 0 := by

      rw [map_sum]
      simp only [himg, ha]
      have e1 : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) ((d : MvPolynomial σ L) • g j) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
          algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) d) * ∑ j, g j • algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      rw [e1]
      beta_reduce at hg
      rw [hg, mul_zero]
    have h1 : ∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E) = 0 :=
      IsFractionRing.injective _ (FractionRing (MvPolynomial σ E)) (by rw [h0, map_zero])
    have h2 := (Fintype.linearIndependent_iff.mp (PolynomialCoordinateBasis.linearIndependent_C (σ := σ) b)) a h1 i
    have h3 : (d : MvPolynomial σ L) • g i = 0 := by rw [← ha i, h2, map_zero]
    rw [Algebra.smul_def] at h3
    exact (mul_eq_zero.mp h3).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  have hmul : ∀ x ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), ∀ y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), x * y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x hx y hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    show algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b k)) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b l)) ∈ _
    rw [← map_mul]; exact hmem _
  have hone : (1 : FractionRing (MvPolynomial σ E)) ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by simpa using hmem 1
  have hfg : (Subalgebra.toSubmodule ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))).FG := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  have htop : ⊤ ≤ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x _
    obtain ⟨a, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ E) x
    have hint := IsIntegral.of_mem_of_fg _ hfg (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q) (hmem q)
    have hinv := Subalgebra.inv_mem_of_algebraic ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))
      (x := ⟨algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q, hmem q⟩) hint.isAlgebraic
    rw [div_eq_mul_inv]
    exact hmul _ (hmem a) _ hinv
  refine ⟨Module.Basis.mk hli htop, fun i => Module.Basis.mk_apply _ _ _, fun e => ?_⟩
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.mk_apply]
  have hx : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
      ∑ k, algebraMap L (FractionRing (MvPolynomial σ L)) (b.repr (e * b j) k) • (Module.Basis.mk hli htop) k := by
    rw [← map_mul, ← MvPolynomial.C_mul]
    conv_lhs => rw [← b.sum_repr (e * b j)]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Module.Basis.mk_apply, Algebra.smul_def (algebraMap L (FractionRing (MvPolynomial σ L)) _),
      IsScalarTower.algebraMap_apply L (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)), MvPolynomial.algebraMap_eq,
      ← himg, hsmul, MvPolynomial.map_C, ← MvPolynomial.C_mul, Algebra.smul_def]
  beta_reduce
  rw [hx, Module.Basis.repr_sum_self]

end ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

theorem gtE_bound (m lam A Bt N : ℝ) (hm : 0 ≤ m) (hlam : 0 < lam) (hA0 : 0 ≤ A)
    (hA : A ≤ m ^ 2 / lam) (hB0 : 0 ≤ Bt) (hBt : Bt ≤ 1 / 2) (hN0 : 0 ≤ N)
    (hN : N ≤ (m + 1) / lam) : A ^ 2 + (Bt * N) ^ 2 ≤ ((m + 1) ^ 2 / lam) ^ 2 := by
  have hA' : A * lam ≤ m ^ 2 := by rwa [le_div_iff₀ hlam] at hA
  have hN' : N * lam ≤ m + 1 := by rwa [le_div_iff₀ hlam] at hN
  have h1 : (A * lam) ^ 2 ≤ (m ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hA' 2
  have hBN : Bt * (N * lam) ≤ 1 / 2 * (m + 1) :=
    mul_le_mul hBt hN' (by positivity) (by norm_num)
  have h2 : (Bt * (N * lam)) ^ 2 ≤ (1 / 2 * (m + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hBN 2
  have h3 : (m ^ 2) ^ 2 + (1 / 2 * (m + 1)) ^ 2 ≤ ((m + 1) ^ 2) ^ 2 := by
    nlinarith [pow_nonneg hm 3, sq_nonneg m, hm]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (A ^ 2 + (Bt * N) ^ 2) * lam ^ 2 = (A * lam) ^ 2 + (Bt * (N * lam)) ^ 2 := by ring
    _ ≤ ((m + 1) ^ 2) ^ 2 := by linarith

private theorem exists_int_inner_of_mem_span_int' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (y : E) (h : ∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) (v : E)
    (hv : v ∈ span ℤ (Set.range b)) : ∃ m : ℤ, inner ℝ y v = m := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  choose f hf using h
  refine ⟨∑ j, c j * f j, ?_⟩
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hf j]

theorem gtE_main (n : ℕ) : ∀ (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : ℝ), 0 < lam →
    (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) →
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam := by
  induction n with
  | zero =>
    intro b lam hlam hmin
    exact ⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    intro b lam hlam hmin
    classical
    obtain ⟨y1, hy1, hint1, hy1n⟩ := gtB_dual_short (Nat.succ_pos m) b lam hlam hmin
    obtain ⟨y0, xu, hxu, hy0, hint0, hy0n, h01⟩ := gtC_prim b y1 hy1 hint1
    obtain ⟨bW, hWL, hproj⟩ := gtD_lat b y0 xu hy0 hxu h01 hint0
    have hfin : Module.finrank ℝ (ℝ ∙ y0)ᗮ = m := by
      rw [Module.finrank_eq_card_basis bW, Fintype.card_fin]
    set φ : (ℝ ∙ y0)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((stdOrthonormalBasis ℝ (ℝ ∙ y0)ᗮ).reindex (finCongr hfin)).repr with hφ
    set bE : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) := bW.map φ.toLinearEquiv with hbEdef
    have hbE : ∀ j, bE j = φ (bW j) := fun j ↦ rfl
    have hspanφ : ∀ p : (ℝ ∙ y0)ᗮ, p ∈ span ℤ (Set.range bW) → φ p ∈ span ℤ (Set.range bE) := by
      intro p hp
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩

      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hbE]
    have hspanφ' : ∀ x, x ∈ span ℤ (Set.range bE) → φ.symm x ∈ span ℤ (Set.range bW) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩

      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_zsmul, hbE, LinearIsometryEquiv.symm_apply_apply]
    have hminE : ∀ x ∈ span ℤ (Set.range bE), x ≠ 0 → lam ≤ ‖x‖ := by
      intro x hx hx0
      have h1 := hmin _ (hWL _ (hspanφ' x hx)) (by
        intro h
        apply hx0
        have h2 : φ.symm x = 0 := Subtype.ext h
        simpa using congrArg φ h2)
      exact h1.trans (le_of_eq (φ.symm.norm_map x))
    obtain ⟨z, hzli, hzint, hzn⟩ := ih bE lam hlam hminE
    set w : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ ((φ.symm (z i) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) with hw
    have hwy0 : ∀ i, inner ℝ y0 (w i) = 0 := fun i ↦
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (φ.symm (z i)).2
    have hwn : ∀ i, ‖w i‖ = ‖z i‖ := fun i ↦ φ.symm.norm_map (z i)
    have hwli : LinearIndependent ℝ w :=
      (hzli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker).map'
        (ℝ ∙ y0)ᗮ.subtype (Submodule.ker_subtype _)
    set u : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ w i - (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) • y0 with hu
    refine ⟨Fin.cons y0 u, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hexp : ∑ i : Fin m, g i.succ • u i = ∑ i : Fin m, g i.succ • w i -
          (∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) • y0 := by
        simp only [hu, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
      rw [hexp] at hg
      have hin := congrArg (fun v ↦ inner ℝ y0 v) hg
      simp only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right, hwy0,
        mul_zero, Finset.sum_const_zero, inner_zero_right, real_inner_self_eq_norm_sq] at hin
      have hy0sq : ‖y0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy0)
      have hg0 : g 0 = ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) := by
        have h3 : (g 0 - ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) *
            ‖y0‖ ^ 2 = 0 := by linear_combination hin
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · exact absurd h hy0sq
      have hX : ∑ i : Fin m, g i.succ • w i = 0 := by
        have h4 := hg
        rw [hg0] at h4
        simpa using h4
      have hsucc : ∀ i : Fin m, g i.succ = 0 := Fintype.linearIndependent_iff.mp hwli _ hX
      intro i
      cases i using Fin.cases with
      | zero => rw [hg0]; simp [hsucc]
      | succ k => exact hsucc k
    · intro i j
      cases i using Fin.cases with
      | zero => simpa using hint0 j
      | succ k =>
        simp only [Fin.cons_succ]
        obtain ⟨p, hp, hpeq⟩ := hproj (b j) (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨k0, hk0⟩ := hint0 j
        obtain ⟨mp, hmp⟩ := exists_int_inner_of_mem_span_int' bE (z k) (hzint k) (φ p) (hspanφ p hp)
        refine ⟨mp + k0 * round (inner ℝ (w k) xu), ?_⟩
        have hb : b j = (p : EuclideanSpace ℝ (Fin (m + 1))) + inner ℝ y0 (b j) • xu := by
          rw [hpeq]; abel
        have hwp : inner ℝ (w k) (p : EuclideanSpace ℝ (Fin (m + 1))) = inner ℝ (z k) (φ p) := by
          show inner ℝ ((φ.symm (z k) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1)))
            (p : EuclideanSpace ℝ (Fin (m + 1))) = _
          rw [← Submodule.coe_inner, ← φ.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
        have h1 : inner ℝ (w k) (b j) = mp + k0 * inner ℝ (w k) xu := by
          conv_lhs => rw [hb]
          rw [inner_add_right, real_inner_smul_right, hk0, hwp, hmp]
        have h2 : inner ℝ (u k) (b j) = inner ℝ (w k) (b j) -
            (inner ℝ (w k) xu - round (inner ℝ (w k) xu)) * inner ℝ y0 (b j) := by
          simp only [hu, inner_sub_left, real_inner_smul_left]
        rw [h2, h1, hk0]
        push_cast
        ring
    · intro i
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        calc ‖y0‖ ≤ ‖y1‖ := hy0n
          _ ≤ ((m + 1 : ℕ) : ℝ) / lam := hy1n
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / lam := by gcongr; exact le_self_pow₀ h1 two_ne_zero
      | succ k =>
        simp only [Fin.cons_succ]
        have hc' : |inner ℝ (w k) xu - round (inner ℝ (w k) xu)| ≤ 1 / 2 := abs_sub_round _
        have hwy0' : inner ℝ (w k) y0 = 0 := by rw [real_inner_comm]; exact hwy0 k
        have hsq : ‖u k‖ ^ 2 = ‖w k‖ ^ 2 +
            (|inner ℝ (w k) xu - round (inner ℝ (w k) xu)| * ‖y0‖) ^ 2 := by
          simp only [hu]
          rw [norm_sub_sq_real, real_inner_smul_right, hwy0', norm_smul, Real.norm_eq_abs]
          ring
        have hA : ‖w k‖ ≤ (m : ℝ) ^ 2 / lam := by rw [hwn]; exact hzn k
        have hN : ‖y0‖ ≤ ((m : ℝ) + 1) / lam := by
          have := hy0n.trans hy1n
          simpa using this
        have hbd := gtE_bound m lam ‖w k‖ _ ‖y0‖ (Nat.cast_nonneg m) hlam (norm_nonneg _) hA
          (abs_nonneg _) hc' (norm_nonneg _) hN
        rw [← hsq] at hbd
        have h5 : ‖u k‖ ≤ ((m : ℝ) + 1) ^ 2 / lam :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd
        simpa using h5

theorem transference_dual {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam :=
  gtE_main n b lam hlam hmin

end ReciprocityTheory.ChartRestriction.G.T0
end
