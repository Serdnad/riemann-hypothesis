module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import Mathlib.LinearAlgebra.Charpoly.Basic
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem TwoBlockFnField.ratio_mem {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (p q : Ix κ) : x p / x q ∈ blockFnField (ι := GlobalTheory κ) x :=
  IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩

theorem TwoBlockFnField.matAct_le {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (A : Matrix (Ix κ) (Ix κ) ℚ) :
    blockFnField (ι := GlobalTheory κ) (matAct A x) ≤ blockFnField (ι := GlobalTheory κ) x := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, -, rfl⟩
  by_cases h0 : ∀ j, x j = 0
  · have : matAct A x p = 0 := by simp [matAct, h0]
    rw [this, zero_div]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := not_forall.mp h0
    have key : ∀ i, matAct A x i / x c ∈ blockFnField (ι := GlobalTheory κ) x := by
      intro i
      have : matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c) := by
        simp only [matAct, Finset.sum_div, mul_div_assoc]
      rw [this]
      refine sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)
      simp
    have : matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c) := by
      rw [div_div_div_cancel_right₀ hc]
    rw [this]
    exact div_mem (key p) (key q)

theorem TwoBlockFnField.matAct_eq {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B) :
    blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x := by
  classical
  obtain ⟨B', -, h⟩ := isInvMat_mul hB
  refine le_antisymm (TwoBlockFnField.matAct_le x B) ?_
  have := TwoBlockFnField.matAct_le (matAct B x) B'
  rwa [matAct_matAct h] at this

theorem TwoBlockFnField.proof : TwoBlockFnField.Statement := by
  intro Ω _ _ κ _ x B hB
  have hE := TwoBlockFnField.matAct_eq x B hB
  refine ⟨le_antisymm ?_ ?_, hE⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    obtain ⟨b, i⟩ := p
    obtain ⟨b', j⟩ := q
    simp only at hpq
    subst hpq
    by_cases hb : b = 0
    · subst hb
      simpa [pair] using TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩
    · simp only [pair, hb, if_false]
      rw [← hE]
      exact TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩
    cases u; cases u'
    refine IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩
    simp [pair]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem aeval_map_intRat_eq {σ : Type} (x : σ → ℂ) (f : MvPolynomial σ ℤ) :
    aeval x (map (algebraMap ℤ ℚ) f) = eval x (map (Int.castRingHom ℂ) f) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem FibreNormBadPrimesFinite.proof : FibreNormBadPrimesFinite.Statement := by
  intro K _ ι _ Ω _ _ y D e L _ _ _ _ hC
  set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef
  have key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧
      ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I := by
    intro c
    set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩
    set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I
    have hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0 := fun g hg => by
        rw [← aeval_map_intRat_eq, ← algebraMap_def]
        exact hx _ (Ideal.mem_map_of_mem _ hg)
      rw [algebraMap_def, aeval_map_intRat_eq]
      by_contra hne
      simp only [f, map_prod, map_X, eval_X] at hne
      have hblk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)
      obtain ⟨j, hj⟩ := hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩
      exact hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    rw [vanishingIdeal_zeroLocus_eq_radical] at hv
    obtain ⟨r, hr⟩ := hv
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]
      at hr
    obtain ⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩ := hr
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.1 hm
    refine ⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩
    have hinj : Function.Injective (map (σ := Σ k, ι k) (algebraMap ℤ ℚ)) :=
      map_injective _ (algebraMap ℤ ℚ).injective_int
    have hu' : f ^ r * C n = u := hinj (by simpa only [algebraMap_def, map_mul] using h)
    rw [mul_comm, hu']
    exact hu
  choose N hN r hr using key
  refine Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_
  rintro p ⟨hp, hH⟩
  obtain ⟨z, hz, hP, hL⟩ := hH
  choose c hc using hz
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))) :=
    sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))
  have h1 := hker (hr c)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast,
    map_intCast] at h1
  have hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)
  have hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0 := (mul_eq_zero.1 h1).resolve_right hprod
  rw [CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at hNz
  simp only [Set.mem_iUnion, Set.mem_Iic]
  exact ⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J :=
  fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 :=
  fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.lift x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.lift x x p, mcPts_smul hPh c hc (R.mem x x (R.mem_U x)), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [brW, h0]
    · simp only [brW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, brQ]
      rw [div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.inj x x' hx.1 ?_
  refine sameOrbit_of_segre (R.mem x' x' (R.mem_U x')).1
    (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.lift x x)) 0 • v) hw
  simp only [brW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
      ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
  rwa [show brQ R Ψ x = y from hx.1] at this

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hz, h, hΨz⟩
  obtain ⟨x, c, hc, hxc⟩ := R.surj z hz hzJ
  have hseg : segre (R.lift x x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.lift x x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzJ ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hxc]
    field_simp [hc p.1]
  · funext i
    simp only [brQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [brW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def coneNullIdealZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : Ideal (MRing ι) :=
  Ideal.span ((mCoordIdeal y : Set (MRing ι)) ∪ Set.range L)

def PullConeNullModP.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∃ N M : ℕ, ¬ p ∣ M ∧ ∀ c : ∀ k, ι k,
        (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullGradedAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (d₀ : K → ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog g d → (∀ k, d₀ k ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

namespace ProjLine

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResVolume.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X],
    IsArithVar P (e + 1) → ∃ dV : Measure R.X, IsSmoothVolume R.A dV

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def IsDehomNormForms (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (j : Fin (D + 1)) (m : ℕ) (s : Ω)
    (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ) : Prop :=
  aeval y (L j) ≠ 0 ∧ ∃ _ : FiniteDimensional (pullField y L) Ω,
    c 0 = 1 ∧ (∀ i ≤ Module.finrank (pullField y L) Ω, (c i).IsHomogeneous (i * m)) ∧
    (LinearMap.charpoly (Algebra.lmul (pullField y L) Ω (s / aeval y (L j) ^ m))).map
        (algebraMap (pullField y L) Ω) =
      ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
        Polynomial.C (aeval (fun i' => aeval y (L i') / aeval y (L j)) (c i)) *
          Polynomial.X ^ (Module.finrank (pullField y L) Ω - i)

end Defs

def FibreNormDehomCharpoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    FiniteDimensional (pullField y L) Ω ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, IsDehomNormForms y L j (q * τ) s c ∧
          (s ≠ 0 → c (Module.finrank (pullField y L) Ω) ≠ 0)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
