module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
import Mathlib.Algebra.MvPolynomial.Cardinal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Cardinal

noncomputable section

theorem exists_ringHom_complex_ker_eq_of_isPrime {σ : Type} [Finite σ] (P : Ideal (MvPolynomial σ ℚ))
    [P.IsPrime] : ∃ φ : MvPolynomial σ ℚ →+* ℂ, ∀ f, φ f = 0 ↔ f ∈ P := by
  let Q := MvPolynomial σ ℚ ⧸ P
  let F := FractionRing Q
  have : CharZero F := charZero_of_injective_algebraMap (R := ℚ) (algebraMap ℚ F).injective
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  refine ⟨(ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P), fun f => ?_⟩
  have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
    ψ.injective.comp (IsFractionRing.injective Q F)
  rw [RingHom.comp_apply, map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]

theorem PullConeNull.proof : PullConeNull.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL
  set I := coneNullIdeal y L

  have hrad : ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ∈ I.radical := by
    intro c
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) ⟨hIP, hP⟩
    obtain ⟨φ, hker⟩ := exists_ringHom_complex_ker_eq_of_isPrime P
    let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
    have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ (map (Int.castRingHom ℚ) f) := by
      intro f
      have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ.comp (map (Int.castRingHom ℚ)) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · exact RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C)
            ((φ.comp (map (Int.castRingHom ℚ))).comp C)) r
        · simp [z]
      exact RingHom.congr_fun h f
    by_contra hc
    have hz : z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_⟩
      · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
        exact Ideal.mul_mem_right _ P ((hker _).mp h0)
      · rw [hev, hker]
        exact hIP (Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩))
    obtain ⟨j, hj⟩ := hL z hz
    apply hj
    rw [hev, hker]
    exact hIP (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
  choose n hn using fun c => Ideal.mem_radical_iff.mp (hrad c)
  refine ⟨Finset.univ.sup n, fun c => ?_⟩
  have hle : n c ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ c)
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact I.mul_mem_right _ (hn c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ProjFSMass.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ)
    (m : ConeMetric ℂ (Ix κ)), IsProjFrame x e → IsPullFS x e m →
    ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ ∧
        ptsIntegralAt (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ (purePot m D) (fun _ => 1) = (projDeg x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatNoetherFrame.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (e : Fin (D + 1) → Ix κ), IsInvMat B ∧ IsRatProjFrame (matAct B x) e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def TopPullFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsSmoothMetric m → IsProjFrame x e →
    IsPullFS x e m → top I x m D = (projDeg x e : ℝ) * hhOf I D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PullFSExtension.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    ∃ m₀ : ConeMetric ℂ (Ix κ), IsSmoothMetric m₀ ∧ IsConjInvariant m₀ ∧
      IsSemipositiveRel ⊥ (coordIdeal ℤ x) (HermLine.ofCone m₀) ∧ IsPullFS x e m₀

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsIsometricOn (P : Ideal (MRing ι)) (A B : HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (α β : K → ℕ), IsMultiHomog f α ∧ IsMultiHomog g β ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (α k : ℤ) - β k = A.a k - B.a k) ∧ divCycle P f = divCycle P g ∧
    ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z

end Objects

def IsomInvariance.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L L' : Fin n → HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, IsIsometricOn P (L j) (L' j)) → I P n L = I P n L'

def GraphIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι ι₂ : K → Type) [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (A : ∀ k, ι₂ k → ι k → ℤ) (B₁ : HermLine ι) (B : HermLine ι₂)
    (B₁' B' : HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → IsBasePtFree P (linForm A) → B₁.a = B.a →
    (∀ z ∈ mcPts P, B₁.h z = B.h (linApply A z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P (linForm A)) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} {K₂ : Type} {ι₂ : K₂ → Type}

def formApply (g : (Σ k, ι₂ k) → MRing ι) (z : (Σ k, ι k) → ℂ) : (Σ k, ι₂ k) → ℂ :=
  fun q => eval z (map (Int.castRingHom ℂ) (g q))

variable [Fintype K] [∀ k, Fintype (ι k)]

end Objects

def GraphChangeOfModel.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
      (G : GenFibre inrV (graphIdeal P g))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inr : K₂ → K ⊕ K₂)))
      (L : Fin d → HermLine ι₂) (L₁ : Fin d → HermLine ι),
      IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
      IsArithVar (imageZ inrV (graphIdeal P g)) d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L₁ j)) →
      (∀ j k, (L₁ j).a k = ∑ k₂, (L j).a k₂ * (δ k₂ k : ℤ)) →
      (∀ j, ∀ z ∈ mcPts P, (L₁ j).h z = (L j).h (formApply g z)) →
      I K ι P d L₁ = (J (fibreIdeal Sum.inr G) 0 Fin.elim0 : ℝ) * I K₂ ι₂ (imageZ inrV (graphIdeal P g)) d L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeWithoutBigness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem tensor_constLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) :
    (A.tensor (constLine c)).h z = A.h z * Real.exp (-c) := rfl

theorem tensor_constLine_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : (A.tensor (constLine c)).a = A.a := by
  show A.a + (constLine (ι := ι) c).a = A.a
  simp [constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]

theorem isSmoothHerm_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (c : ℝ) :
    IsSmoothHerm (A.tensor (constLine c)) := by
  unfold IsSmoothHerm
  have : (A.tensor (constLine c)).h = fun z => A.h z * Real.exp (-c) := rfl
  rw [this]
  exact hA.mul contDiffOn_const

theorem leviForm_twist (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((A.tensor (constLine c)).h z)) z w =
      leviForm (fun z => Real.log (A.h z)) z w := by
  have hev : (fun z => Real.log ((A.tensor (constLine c)).h z)) =ᶠ[𝓝 z]
      (fun z => Real.log (A.h z) + (-c)) := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [tensor_constLine_h, Real.log_mul (A.pos z' hz').ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fderiv ℝ (fun z => Real.log ((A.tensor (constLine c)).h z))) z =
      fderiv ℝ (fderiv ℝ (fun z => Real.log (A.h z))) z := by
    rw [hev.fderiv.fderiv_eq]
    congr 1
    funext z'
    exact fderiv_add_const _
  unfold leviForm
  rw [h2]

theorem isSemipositiveRel_twist {P0 P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (h : IsSemipositiveRel P0 P A) (c : ℝ) : IsSemipositiveRel P0 P (A.tensor (constLine c)) := by
  refine ⟨isSmoothHerm_twist h.1 c, fun z hz w hw => ?_⟩
  rw [leviForm_twist A c hz.1 w]
  exact h.2 z hz w hw

theorem isConjInvariantH_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : IsConjInvariantH A) (c : ℝ) :
    IsConjInvariantH (A.tensor (constLine c)) := by
  intro z
  rw [tensor_constLine_h, tensor_constLine_h, h z]

theorem nefOnFibres_twist {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : NefOnFibres P A.a) (c : ℝ) :
    NefOnFibres P (A.tensor (constLine c)).a := by
  rw [tensor_constLine_a]
  exact h

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Q : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Q La 1 D) : ∃ τ, 1 ≤ τ ∧ ∃ s ∈ La τ, s ≠ 0 ∧ Q τ s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k : ℕ, smallSectionCount Q La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hsub : Subsingleton {s : La (1 * k) // Q (1 * k) (s : Ω)} := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha0 : (a : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) a a.2 h0 ha
        have hb0 : (b : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) b b.2 h0 hb
        exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
      have hcard : Nat.card {s : La (1 * k) // Q (1 * k) (s : Ω)} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      have hlog : smallSectionCount Q La (1 * k) = 0 := by
        unfold smallSectionCount
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h <;> rw [h] <;> simp
      rw [hlog, zero_div]
  have : arVolP Q La 1 D = 0 := by
    unfold arVolP
    simp only [hzero]
    exact limsup_const 0
  linarith

theorem exists_gt_of_lt {N e' g T : ℝ} (hN : 0 < N) (h : N * e' * g < T) :
    ∃ e'', e' < e'' ∧ N * e'' * g < T := by
  by_cases hg : g ≤ 0
  · refine ⟨e' + 1, by linarith, ?_⟩
    have h1 : N * (e' + 1) * g = N * e' * g + N * g := by ring
    have h2 : N * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hg
    linarith
  · push Not at hg
    have hd : 0 < (T - N * e' * g) / (2 * N * g) := div_pos (by linarith) (by positivity)
    refine ⟨e' + (T - N * e' * g) / (2 * N * g), by linarith, ?_⟩
    have h1 : N * (e' + (T - N * e' * g) / (2 * N * g)) * g = N * e' * g + (T - N * e' * g) / 2 := by
      field_simp
    rw [h1]
    linarith

end LatticeWithoutBigness


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
