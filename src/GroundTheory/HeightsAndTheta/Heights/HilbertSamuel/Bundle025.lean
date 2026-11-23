module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Nullstellensatz
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubquot

set_option linter.unusedSectionVars false

theorem iSupIndep_comap {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (p j).comap g) ≤ (⨆ (j) (_ : j ≠ i), p j).comap g :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  have h0 := (Submodule.disjoint_def.mp (hp i)) (g x) (Submodule.mem_comap.mp hx) (Submodule.mem_comap.mp (hle hx'))
  exact hg (by rw [h0, map_zero])

theorem iSupIndep_map_of_ker_le {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨x, hx, rfl⟩ := hy
  have hy2 : f x ∈ (⨆ (j) (_ : j ≠ i), p j).map f := by
    simpa only [Submodule.map_iSup] using hy'
  obtain ⟨z, hz, hzx⟩ := hy2
  have hk : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  have hk' := hL hk
  rw [iSup_split_single (fun c => LinearMap.ker f ⊓ p c) i, Submodule.mem_sup] at hk'
  obtain ⟨l, hl, w, hw, hlw⟩ := hk'
  have hw1 : w ∈ ⨆ (j) (_ : j ≠ i), p j :=
    (show (⨆ (j) (_ : j ≠ i), LinearMap.ker f ⊓ p j) ≤ ⨆ (j) (_ : j ≠ i), p j from
      iSup₂_mono fun j _ => inf_le_right) hw
  have hxl : x - l ∈ p i := sub_mem hx (Submodule.mem_inf.mp hl).2
  have hxl' : x - l ∈ ⨆ (j) (_ : j ≠ i), p j := by
    have e : x - l = z + w := by
      calc x - l = (x - z) - l + z := by abel
        _ = z + w := by rw [← hlw]; abel
    rw [e]
    exact Submodule.add_mem _ hz hw1
  have h0 := (Submodule.disjoint_def.mp (hp i)) (x - l) hxl hxl'
  rw [sub_eq_zero.mp h0]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k


variable (S ι) in
def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}

theorem monTimes_subset_span (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by
  rintro _ ⟨u, h, hh, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hh)

theorem span_monTimes_le (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S :=
  Submodule.span_le.mpr (monTimes_subset_span H)

theorem monomial_smul_mem (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx

theorem span_le_span_monTimes (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by
  let T : Submodule (MRingOver S ι) M :=
    { carrier := Submodule.span S (monTimes S ι H)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro p y hy
        refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
        · have e : (monomial u a : MRingOver S ι) = a • monomial u (1 : S) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [e, smul_assoc]
          exact Submodule.smul_mem _ a (monomial_smul_mem H u hy)
        · rw [add_smul]
          exact Submodule.add_mem _ hp hq }
  have hT : Submodule.span (MRingOver S ι) H ≤ T := by
    rw [Submodule.span_le]
    intro h hh
    have e : h = (monomial 0 (1 : S) : MRingOver S ι) • h := by
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_smul]
    exact Submodule.subset_span ⟨0, h, hh, e⟩
  exact fun x hx => hT hx

theorem monTimes_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩

theorem mem_iSup_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN

end GradedSubquot


open GradedSubquot in
theorem GradedSubquot.proof : GradedSubquot.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 G H hM hG hH hGH

  have hind : iSupIndep (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) :=
    iSupIndep_comap hM.1.submodule_iSupIndep ((Submodule.span (MRingOver S ι) H).subtype.restrictScalars S)
      (fun a b h => Subtype.ext h)
  have hsup : ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    exact (show (⨆ c, ((Submodule.span (MRingOver S ι) H).comap (Submodule.span (MRingOver S ι) H).subtype).restrictScalars S ⊓
        subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) ≤ ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c from
      iSup_mono fun c => inf_le_right) (mem_iSup_inf hM hH le_rfl x x.2)
  refine ⟨⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup,
    fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩, ?_⟩

  set L := (Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype with hLdef
  set f := L.mkQ.restrictScalars S with hfdef
  have hker : LinearMap.ker f = L.restrictScalars S := by
    ext x
    simp [hfdef]
  have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) := by
    rw [hker]
    intro x hx
    exact mem_iSup_inf hM hG hGH x hx
  have hind2 := iSupIndep_map_of_ker_le hind f hL
  have hsup2 : ⨆ c, quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) L c = ⊤ := by
    change ⨆ c, (subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c).map f = ⊤
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective L
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
  rintro a c p _ hp ⟨x, hx, rfl⟩
  exact ⟨p • x, hM.2 a c p (x : M) hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def LocIdealKer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (T : Submonoid (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓜 → IsMultiHomogIdeal P → (∀ t ∈ T, ∃ a : K → ℕ, IsMultiHomog t a) →
    ∀ w ∈ KH.locPart ι 𝓜 T d,
      (w ∈ locIdealPart 𝓜 T P d ↔
        IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
          (LocalizedModule.mkLinearMap T (M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M)))
          (P • ⊤ : Submodule (MRingOver S ι) M).mkQ w = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtFibreLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → IsClosedMultiPt P →
    Subsingleton (KH.cechHc ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) d 1) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormBound.proof (h₁ : ProjAvoidingForm.Statement) (h₂ : FibreRepresentatives.Statement)
    (h₃ : FibreNormMax.Statement) (h₄ : MetricMaxComparison.Statement) : FibreNormBound.Statement := by
  intro K _ ι _ Ω _ y D A df f hV hB hA hf hfP
  obtain ⟨e, L, G, he, hL, hL0, hG, hGf⟩ := h₁ K ι Ω y D df f hV hf hfP
  obtain ⟨n, c, B, hn, hB1, hF⟩ := h₃ K ι Ω y D A.a e L hV hB he hL hL0
  obtain ⟨C, hC, hAC⟩ := h₄ K ι A hA
  choose S hS₁ hS₂ using h₂ K ι Ω y D e L he hL hL0
  refine ⟨n, c, B * C ^ n, G, S, hn, one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hC), hG, ?_, ?_⟩
  · intro ζ _ hGζ z hz
    obtain ⟨hzP, t, ht⟩ := hS₁ ζ z hz
    exact ⟨hzP, hGf ζ hGζ z hzP ⟨t, ht⟩⟩
  · intro τ u hu hu0
    obtain ⟨F, hF0, hFdeg, hFb⟩ := hF τ u hu hu0
    refine ⟨F, hF0, hFdeg, fun ζ hζ _ M hM hrep => ?_⟩
    have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
    have key := hFb ζ hζ (S ζ) (hS₂ ζ) (M * C ^ τ) (by positivity) (fun z hz => by
      obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩ := hrep z hz
      refine ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, ?_⟩
      have hzb := (hS₁ ζ z hz).1.1
      have h0 : 0 ≤ A.h z := (A.pos z hzb).le
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := hle
        _ ≤ M * (C * (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z) ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
            gcongr
            exact hAC z hzb
        _ = M * C ^ τ * (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring)
    have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
    have hpow : C ^ (τ * n) ≤ C ^ (n * (τ + 1)) :=
      pow_le_pow_right₀ hC (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_right n (Nat.le_succ τ))
    calc ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * (M * C ^ τ) ^ n := key
      _ = B ^ (τ + 1) * M ^ n * C ^ (τ * n) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ B ^ (τ + 1) * M ^ n * C ^ (n * (τ + 1)) := by gcongr
      _ = (B * C ^ n) ^ (τ + 1) * M ^ n := by rw [mul_pow, ← pow_mul]; ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KleimanVarietyH1Generation.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (Q : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiProjPrime Q → KH.NefOnF I Q α → 1 ≤ b → 1 ≤ a →
    H1GenAmple F Q (b • α + fun _ => (a : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∈ coneNullIdeal y L) →
    ∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog g d →
      (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def relChartLat {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) : Submodule R Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)}
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  zero_mem' := fun c _ => by simp
  smul_mem' := fun r s hs c hc => by rw [smul_mul_assoc]; exact Subalgebra.smul_mem _ (hs c hc) r

def RelLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n m : ℕ) (g : Fin m → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (relChartLat (Algebra.adjoin ℤ (Set.range g)) y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentsMeetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y ∧
      ∃ W ∈ S, ∃ W' ∈ S, W ≠ W' ∧ z ∈ zeroLocus ℂ W ∧ z ∈ zeroLocus ℂ W'} = 0

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory
  Topology

noncomputable section

namespace ArithmeticVolumeResolution

variable {ι0 : Type} [Fintype ι0]

theorem error_isLittleO (D : ℕ) (K₁ K₂ : ℝ) :
    (fun n : ℕ => K₁ * (n : ℝ) ^ D + K₂ * ((n : ℝ) ^ D * Real.log n)) =o[atTop] pw D := by
  have h1 : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D := by
    have := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto
      tendsto_natCast_atTop_atTop
    exact this
  have h2 : (fun n : ℕ => (n : ℝ) ^ D * Real.log n) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO
      (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact (h1.const_mul_left K₁).add (h2.const_mul_left K₂)

end ArithmeticVolumeResolution


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
