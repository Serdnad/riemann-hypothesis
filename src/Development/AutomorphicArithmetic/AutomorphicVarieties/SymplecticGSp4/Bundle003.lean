module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle048
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_mul {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K) {x y : M4 K}
    (hx : x ∈ Submodule.span K (Set.range r)) (hy : y ∈ Submodule.span K (Set.range r)) :
    x * y ∈ Submodule.span K (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      exact Submodule.subset_span ⟨g * h, map_mul r g h⟩
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add b c _ _ hb hc => rw [add_mul]; exact add_mem hb hc
  | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_top {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule K (Matrix n n K)) (h : ∀ i j, Matrix.single i j (1 : K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have := S.smul_mem (x i j) (h i j)
  simpa [Matrix.smul_single] using this

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_iff {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K)
    (he : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) (i j : Fin 4) :
    Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 := geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    have h2 := Submodule.smul_mem _ (r g i j)⁻¹ h1
    rw [Matrix.single_mul_mul_single, Matrix.smul_single] at h2
    simpa [hg] using h2
  · intro h
    by_contra hn
    have hz : ∀ g, r g i j = 0 := fun g => by
      by_contra h'
      exact hn ⟨g, h'⟩
    have key : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha => obtain ⟨g, rfl⟩ := ha; exact hz g
      | zero => rfl
      | add b c _ _ hb hc => simp [hb, hc]
      | smul c b _ hb => simp [hb]
    simpa using key _ h

theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg :
    ∀ {H : Type} [Group H] (K : Type) [Field K] (r : H →* M4 K) (ν : H → K), (∀ g, IsGSp (ν g) (r g)) → (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) → (∀ i j, Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r)) ∧ (∀ i, Ge r i i) ∧ (∀ i j k, Ge r i j → Ge r j k → Ge r i k) ∧ (∀ i j, Ge r i j → Ge r j.rev i.rev) ∧ (Irr r ↔ ∀ i j, Ge r i j) ∧ (Ge r 0 2 → Ge r 2 0 → (∀ g, IsBlock (r g)) → Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) = ⊤) := by
  intro H _ K _ r ν hν he
  have hiff := geAlg_iff r he
  refine ⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have := geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)
    rw [Matrix.single_mul_single_same, mul_one] at this
    exact (hiff i k).2 this
  · rintro i j ⟨g, hg⟩
    refine ⟨g⁻¹, fun h0 => hg ?_⟩
    have h1 : adj (r g) = ν g • r g⁻¹ := by
      have h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹ := by rw [hν g]
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul] at h2
    have h3 := congrFun (congrFun h1 j.rev) i.rev
    rw [adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero] at h3
    have h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by decide
    rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3
  · constructor
    · intro h i j
      rw [hiff, h]
      trivial
    · intro h
      exact geAlg_top _ fun i j => (hiff i j).1 (h i j)
  · intro h02 h20 _
    let f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun x => x.submatrix ixA ixA
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hm : ∀ x ∈ Submodule.span K (Set.range r),
        f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) := by
      intro x hx
      have := Submodule.mem_map_of_mem (f := f) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1 := by
      intro a b
      ext c d
      have hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b := by decide
      show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _
      simp only [Matrix.single_apply, hinj]
    refine geAlg_top _ fun a b => ?_
    rw [← hs]
    apply hm
    fin_cases a <;> fin_cases b
    · exact he 0
    · exact (hiff 0 2).1 h02
    · exact (hiff 2 0).1 h20
    · exact he 2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_diag {K : Type} [Field K] (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (h : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c :=
  _root_.UpperTheory.Reformulated.B.OrderedFlagDiagonal.ordFlag_diag c hc X h

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_aeval {K : Type} [Field K] (c : Fin 4 → K) (X P : M4 K)
    (h : X * P = P * Matrix.diagonal c) (p : Polynomial K) :
    Polynomial.aeval X p * P = P * Matrix.diagonal fun k => p.eval (c k) := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i j
    simp [Matrix.mul_diagonal, Algebra.algebraMap_eq_smul_one, mul_comm]
  | add p q hp hq =>
    rw [map_add (f := _), add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]
    simp
  | monomial n a hn =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_assoc, h, ← mul_assoc, hn, mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag :
    ∀ {H : Type} [Group H] (I : Subgroup H) (K : Type) [Field K] (ps : Fin 4 → H → K) (s₀ : H) (r : H →* M4 K), Function.Injective (fun i => ps i s₀) → Ord I ps s₀ r → ∃ (u : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ), (∀ g i j, j < i → ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i j = 0) ∧ (∀ g i, ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i i = κ i g) ∧ (∀ i, ∀ s ∈ I, (κ i s : K) = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (κ i g : K) = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H _ I K _ ps s₀ r hc ho
  obtain ⟨P, hP⟩ := ordFlag_diag _ hc (r s₀) ho.charpoly
  set d : Fin 4 → K := fun i => ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀) with hd
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e => (Finset.mem_erase.mp hj).1 (hc e).symm
  have hprj : ∀ i, prj (fun a => ps a s₀) (r s₀) i
      = (P : M4 K) * Matrix.diagonal (Pi.single i (d i)) * ((P⁻¹ : (M4 K)ˣ) : M4 K) := by
    intro i
    rw [Units.eq_mul_inv_iff_mul_eq, prj, ordFlag_aeval _ _ _ hP]
    congr 2
    funext k
    rw [Polynomial.eval_prod]
    by_cases hk : k = i
    · subst hk; simp [hd]
    · rw [Pi.single_eq_of_ne hk]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (by simp)
  have key : ∀ (Y : M4 K) i j, prj (fun a => ps a s₀) (r s₀) i * Y * prj (fun a => ps a s₀) (r s₀) j = 0 →
      (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) i j = 0 := by
    intro Y i j h
    have h2 : Matrix.diagonal (Pi.single i (d i)) * (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) *
        Matrix.diagonal (Pi.single j (d j)) = 0 := by
      have := congrArg (fun Z : M4 K => ((P⁻¹ : (M4 K)ˣ) : M4 K) * Z * (P : M4 K)) h
      simpa [hprj, mul_assoc] using this
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
    simpa [hd0] using h3
  set M : H → M4 K := fun g => ((P⁻¹ : (M4 K)ˣ) : M4 K) * r g * (P : M4 K) with hM
  have htri : ∀ g i j, j < i → M g i j = 0 := fun g i j hij => key _ i j (ho.stable g j i hij)
  have hmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp [hM, mul_assoc]
  let κ₀ : Fin 4 → H →* K := fun i =>
    { toFun := fun g => M g i i
      map_one' := by simp [hM]
      map_mul' := by
        intro g h
        rw [hmul, Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [htri g i k hk, zero_mul]
        · rw [htri h k i hk, mul_zero] }
  refine ⟨P⁻¹, fun i => (κ₀ i).toHomUnits, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [inv_inv]
    exact htri g i j hij
  · intro g i
    rw [inv_inv]
    rfl
  · intro i s hs
    have h1 := key _ i i (ho.inert s hs i)
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul, Matrix.sub_apply, sub_eq_zero] at h1
    show M s i i = _
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    exact h1
  · intro i g
    show d i * M g i i = _
    rw [hprj, mul_assoc, mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    show _ = (Matrix.diagonal (Pi.single i (d i)) * M g).trace
    simp [Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
end
