module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Mirror
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin K (by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  letI : CommRing S := { mul_comm := isMulCommutative_iff.mp inferInstance }
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem smul_mem_laHat {c : AfP p} (hc : IsIntAf c) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    c • v ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  apply KNLevel.mem_laHat_of_repr b
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, KNLevel.isIntAf_iff]
  exact mul_mem ((KNLevel.isIntAf_iff _).mp hc)
    ((KNLevel.isIntAf_iff _).mp (KNLevel.repr_isIntAf b v hv i))

private theorem inAf_mem_laHat (a : D.La) : inAf D a ∈ LaHat D := by
  unfold inAf LaHat
  exact AddSubgroup.subset_closure ⟨1, a, (KNLevel.isIntAf_iff 1).mpr (one_mem _), rfl⟩

private theorem exists_den_act (g : G.GAf) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ LaHat D, m • L.actG g z ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := KNLevel.bA b
  obtain ⟨m, hm, hden⟩ := AfPCpctDen.exists_den p
    (Set.range fun ki : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
      B.repr (L.actG g (B ki.1)) ki.2) (Set.finite_range _).isCompact
  refine ⟨m, hm, fun z hz => ?_⟩
  have hy : ∀ k, m • L.actG g (B k) ∈ LaHat D := by
    intro k
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, KNLevel.isIntAf_iff]
    exact hden _ ⟨(k, i), rfl⟩

  rw [← B.sum_repr z, map_sum, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [LinearMap.map_smul, smul_comm m]
  exact smul_mem_laHat (KNLevel.repr_isIntAf b z hz k) (hy k)

private theorem rd_move (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (w : VQ D) :
    rd L x h₂ w = L.actG (h₂⁻¹ * h₁) (rd L x h₁ w) := by
  simp only [rd]
  rw [← Module.End.mul_apply (L.actG (h₂⁻¹ * h₁)), ← map_mul, mul_inv_cancel_right]

private theorem stable (hd : RdDense) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (P : VQ D → Prop)
    (A₁ : ∀ w, P w ↔ rd L x h₁ w ∈ LaHat D) (A₂ : ∀ w, P w ↔ rd L x h₂ w ∈ LaHat D)
    (z : AfP p ⊗[ℚ] VQ D) (hz : z ∈ LaHat D) : L.actG (h₂⁻¹ * h₁) z ∈ LaHat D := by
  obtain ⟨m, hm, hden⟩ := exists_den_act L (h₂⁻¹ * h₁)
  obtain ⟨w, e, he, rfl⟩ := hd p D G L x h₁ m hm z
  have h1 : rd L x h₁ w ∈ LaHat D := by
    have := sub_mem hz (nsmul_mem he m)
    rwa [add_sub_cancel_right] at this
  have h2 : rd L x h₂ w ∈ LaHat D := (A₂ w).mp ((A₁ w).mpr h1)
  rw [map_add (f := _), map_nsmul, ← rd_move L x h₁ h₂ w]
  exact add_mem h2 (hden e he)

private theorem congOne_of_gen {N : ℕ} {g : G.GAf}
    (gen : ∀ a : D.La, ∃ u ∈ LaHat D, L.actG g (inAf D a) = inAf D a + N • u) : L.CongOne N g := by
  unfold Link.CongOne
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, y, hc, rfl⟩ := hz
    obtain ⟨u, hu, hgu⟩ := gen y
    have hcy : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = c • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨c • u, smul_mem_laHat hc hu, ?_⟩
    rw [hcy, LinearMap.map_smul, hgu, smul_add, smul_comm c N u]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add (f := _), e₁, e₂, smul_add]; abel⟩
  | neg y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, neg_add, smul_neg]⟩

end SlopeTestRemainingChoices

theorem coordKN_of : RdDense → CoordKN := by
  intro hd p _ D G L x N hN hcop D' t j h₁ h₂ hc1
  have memOf : ∀ {g : G.GAf}, L.CongOne N g → ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
    intro g hC v hv
    obtain ⟨w, hw, e⟩ := hC v hv
    rw [e]
    exact add_mem hv (nsmul_mem hw N)
  have cong : ∀ k₁ k₂ : G.GAf, IsCoordA L x N D' t j k₁ → IsCoordA L x N D' t j k₂ →
      L.CongOne N (k₂⁻¹ * k₁) := by
    intro k₁ k₂ hk₁ hk₂
    have hst : ∀ z ∈ LaHat D, L.actG (k₂⁻¹ * k₁) z ∈ LaHat D :=
      stable L hd x k₁ k₂ (fun w => ∃ r u, p ^ r • w = j u) hk₁.1 hk₂.1
    apply congOne_of_gen L
    intro a
    obtain ⟨w₁, hw₁, e₁⟩ := hk₁.2 a
    obtain ⟨w₂, hw₂, e₂⟩ := hk₂.2 a
    refine ⟨w₂ - L.actG (k₂⁻¹ * k₁) w₁, sub_mem hw₂ (hst w₁ hw₁), ?_⟩
    have e₃ := rd_move L x k₁ k₂ (j (t a))
    rw [e₂, e₁, map_add (f := _), map_nsmul] at e₃
    rw [smul_sub, ← add_sub_assoc, e₃]
    abel
  constructor
  · intro hc2
    exact ⟨cong h₁ h₂ hc1 hc2, by rw [mul_inv_rev, inv_inv]; exact cong h₂ h₁ hc2 hc1⟩
  · intro hg
    obtain ⟨hC, hCi⟩ := hg
    have hinv : (h₂⁻¹ * h₁)⁻¹ = h₁⁻¹ * h₂ := by rw [mul_inv_rev, inv_inv]
    refine ⟨fun w => ?_, fun a => ?_⟩
    · rw [hc1.1 w]
      constructor
      · intro hw
        rw [rd_move L x h₁ h₂ w]
        exact memOf hC _ hw
      · intro hw
        rw [rd_move L x h₂ h₁ w, ← hinv]
        exact memOf hCi _ hw
    · obtain ⟨w₁, hw₁, e₁⟩ := hc1.2 a
      obtain ⟨w₃, hw₃, e₃⟩ := hC _ (inAf_mem_laHat a)
      refine ⟨w₃ + L.actG (h₂⁻¹ * h₁) w₁, add_mem hw₃ (memOf hC _ hw₁), ?_⟩
      rw [rd_move L x h₁ h₂, e₁, map_add (f := _), map_nsmul, e₃, smul_add, add_assoc]

end UpperTheory.Gal.W2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.IsogenyReduction

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem exists_bound (k : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) :
    ∃ c : ℕ, 0 < c ∧ ∀ z ∈ LaHat D, c • k z ∈ LaHat D := by
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let S : Set (AfP p) := Set.range (fun ij : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
    (KNLevel.bA b).repr (k (KNLevel.bA b ij.2)) ij.1)
  have hS : IsCompact S := (Set.finite_range _).isCompact
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨c, hc, ?_⟩
  have hB : ∀ j, inAf D (b j) = KNLevel.bA b j := by
    intro j
    simp [KNLevel.bA, inAf, Algebra.TensorProduct.basis_apply]
  have hgen : ∀ j, c • k (inAf D (b j)) ∈ LaHat D := by
    intro j
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [hB j, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    exact hcS _ ⟨(i, j), rfl⟩
  have hall : ∀ x : D.La, (c • k) (inAf D x) ∈ LaHat D := by
    intro x
    let f : D.La →+ (AfP p ⊗[ℚ] VQ D) :=
      ((c • k).toAddMonoidHom).comp (AddMonoidHom.mk' (inAf D) GammaUniq.inAf_add)
    have hf : ∀ y, f y = (c • k) (inAf D y) := fun y => rfl

    rw [← hf, ← b.sum_repr x, map_sum]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hgen j) _
  intro z hz
  exact GammaUniq.map_mem (c • k) hall hz

private theorem end_eq (k T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
    (h : ∀ (a : D.La) (n : ℕ), 0 < n → n.Coprime p → ∃ w ∈ LaHat D, ∃ w' ∈ LaHat D,
      k (inAf D a) = T (inAf D a) + n • w + n • k w') : k = T := by
  apply GammaUniq.end_ext
  intro a
  obtain ⟨c, hc, hcb⟩ := exists_bound k
  have hz : c • (k (inAf D a) - T (inAf D a)) = 0 := by
    apply GammaUniq.eq_zero_of_dvd_laHat
    intro n hn hnp
    obtain ⟨w, hw, w', hw', he⟩ := h a n hn hnp
    refine ⟨c • w + c • k w', add_mem (AddSubgroup.nsmul_mem _ hw c) (hcb w' hw'), ?_⟩
    have hd : k (inAf D a) - T (inAf D a) = n • w + n • k w' := by
      rw [he]
      abel
    rw [hd, smul_add, smul_add, smul_comm c n w, smul_comm c n (k w')]
  have hX : k (inAf D a) - T (inAf D a) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hc.ne')
  exact sub_eq_zero.mp hX

variable (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (u w : VQ D) :
    rd L x g (u + w) = rd L x g u + rd L x g w := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (n : ℕ) (w : VQ D) :
    rd L x g (n • w) = n • rd L x g w := by
  induction n with
  | zero =>
    simp only [zero_smul, UpperTheory.Gal.W2.rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih =>
    rw [succ_nsmul, rd_add, ih, succ_nsmul]

private theorem rd_eq (x : (AfP p ⊗[ℚ] G.C)ˣ) (g h : G.GAf) (w : VQ D) :
    rd L x h w = L.actG (h⁻¹ * g) (rd L x g w) := by
  unfold UpperTheory.Gal.W2.rd
  rw [← Module.End.mul_apply (L.actG (h⁻¹ * g)), ← map_mul, mul_inv_cancel_right]

private theorem coord_of (x : (AfP p ⊗[ℚ] G.C)ˣ) {N : ℕ} {D' : PLat D.O D.inv} {t t₀ : D.La → D'.La}
    {j : D'.La →+ VQ D} {g : G.GAf} (hc : IsCoordA L x N D' t₀ j g) (h : ∀ a, ∃ u, t₀ a = t a + N • u) :
    IsCoordA L x N D' t j g := by
  refine ⟨hc.1, fun a => ?_⟩
  obtain ⟨w, hw, he⟩ := hc.2 a
  obtain ⟨u, hu⟩ := h a
  have hmem : rd L x g (j u) ∈ LaHat D := (hc.1 (j u)).mp ⟨0, u, by simp⟩
  refine ⟨w - rd L x g (j u), sub_mem hw hmem, ?_⟩
  rw [hu, map_add (f := _), map_nsmul, rd_add, rd_nsmul] at he
  rw [smul_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]

end UpperTheory.Gal.W2.IsogenyReduction

open UpperTheory.Gal.W2.IsogenyReduction in
theorem UpperTheory.Gal.W2.isogCoord_of :
    UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.IsogForm → UpperTheory.Gal.W2.RdDense → UpperTheory.Gal.W2.IsogCoord := by
  intro hAd hCo hIf hRd p _ D G L B N N' hN hNp hN' hN'p h hconj ρ D' t D'' t'' P P'' inc d hP hP'' hPP
    hdp hd f nu f'' nu'' hf hf'' hft hft'' hiff j h₁ M hpl hco hloc
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hdp)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hinc : Function.Injective inc := fun u1 u2 he => hP.2.1 (by rw [← hPP u1, ← hPP u2, he])
  obtain ⟨lift, hlift⟩ : ∃ lift : D''.La → D'.La, ∀ u'', inc (lift u'') = d • u'' :=
    ⟨fun u'' => (hd u'').choose, fun u'' => (hd u'').choose_spec⟩
  have hlift_add : ∀ a b, lift (a + b) = lift a + lift b := fun a b =>
    hinc (by rw [map_add (f := _), hlift, hlift, hlift, smul_add])
  have hlift_inc : ∀ u, lift (inc u) = d • u := fun u => hinc (by rw [hlift, map_nsmul])
  obtain ⟨j'', hj''⟩ : ∃ j'' : D''.La →+ VQ D, ∀ u'', j'' u'' = (d : ℚ)⁻¹ • j (lift u'') :=
    ⟨AddMonoidHom.mk' (fun u'' => (d : ℚ)⁻¹ • j (lift u''))
      (fun a b => by simp only [hlift_add, map_add (f := _), smul_add]), fun _ => rfl⟩
  have hj''d : ∀ u'', (d : ℚ) • j'' u'' = j (lift u'') := by
    intro u''
    rw [hj'', smul_smul, mul_inv_cancel₀ hd', one_smul]
  have hj''inc : ∀ u, j'' (inc u) = j u := by
    intro u
    rw [hj'', hlift_inc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hd', one_smul]
  have hpl'' : IsPlace L B.β D'' j'' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have h1 : j (lift a) = j (lift b) := by rw [← hj''d, ← hj''d, hab]
      have h2 := hpl.1 h1
      have h3 : d • a = d • b := by rw [← hlift, ← hlift, h2]
      haveI := D''.free
      have h4 : (d : ℤ) • a = (d : ℤ) • b := by rw [natCast_zsmul, natCast_zsmul]; exact h3
      exact smul_right_injective D''.La (by exact_mod_cast hd0 : (d : ℤ) ≠ 0) h4
    · intro c u
      have hl : lift (c • u) = c • lift u := hinc (by
        rw [hlift, map_smul, hlift]
        exact smul_comm d c u)
      rw [hj'', hj'', hl, hpl.2.1, map_smul]
    · intro w
      obtain ⟨m, u, hm, hmw⟩ := hpl.2.2.1 w
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
    · obtain ⟨r, hr, hrEF⟩ := hIf p D G L h ρ D' D'' P P'' inc hP hP'' hPP f nu f'' nu'' hf hf'' hiff
      obtain ⟨s, hs, hsEF⟩ := hpl.2.2.2
      refine ⟨r * s, mul_pos hr hs, fun u1 u2 => ?_⟩
      have key : ((D''.EF (d • u1) (d • u2) : ℤ) : ℚ) = (d : ℚ) * d * (D''.EF u1 u2) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast
        ring
      have hform : ∀ (c : ℚ) (x y : VQ D), formB L B.β (c • x) (c • y) = c * c * formB L B.β x y := by
        intro c x y
        simp only [formB, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      calc ((D''.EF u1 u2 : ℤ) : ℚ) = ((d : ℚ) * d)⁻¹ * (D''.EF (d • u1) (d • u2) : ℤ) := by
            rw [key]
            field_simp
        _ = ((d : ℚ) * d)⁻¹ * (D''.EF (inc (lift u1)) (inc (lift u2)) : ℤ) := by rw [hlift, hlift]
        _ = ((d : ℚ) * d)⁻¹ * (r * (D'.EF (lift u1) (lift u2) : ℤ)) := by rw [hrEF]
        _ = ((d : ℚ) * d)⁻¹ * (r * (s * formB L B.β (j (lift u1)) (j (lift u2)))) := by rw [hsEF]
        _ = r * s * formB L B.β (j'' u1) (j'' u2) := by
            rw [← hj''d u1, ← hj''d u2, hform]
            field_simp
  have hloc'' : IsLocP D'' j'' M := by
    intro w
    constructor
    · rintro ⟨m, u'', hm, hmw⟩
      refine (hloc w).mp ⟨d * m, lift u'', Nat.Coprime.mul_left hdp hm, ?_⟩
      rw [mul_smul, hmw, ← hj''d, Nat.cast_smul_eq_nsmul]
    · intro hw
      obtain ⟨m, u, hm, hmw⟩ := (hloc w).mpr hw
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
  obtain ⟨h₂, hR₂⟩ := hAd p D G L B D'' j'' hpl'' f'' nu'' hf''
  obtain ⟨h₃, hR₃⟩ := hAd p D G L B D' j hpl f nu hf
  have hc₂ : IsCoordA L (trivX B) N D'' t'' j'' h₂ := coord_of L (trivX B) (hR₂ N hN hNp) hft''
  have hc₃ : IsCoordA L (trivX B) N' D' t j h₃ := coord_of L (trivX B) (hR₃ N' hN' hN'p) hft
  have hk₃ : h₃⁻¹ * h₁ ∈ L.KN N' := (hCo p D G L (trivX B) N' hN' hN'p D' t j h₁ h₃ hco).mp hc₃
  have hkey : h₂⁻¹ * h₃ = h := by
    apply GammaUniq.actG_injective L
    apply end_eq
    intro a n hn hnp
    obtain ⟨w₃, hw₃m, hw₃⟩ := (hR₃ n hn hnp).2 a
    obtain ⟨b, e, he⟩ := (hf''.2 n hn hnp).2.2.2.1 (inc (f n a))
    obtain ⟨wT, hwTm, hT⟩ := (hiff n hn hnp a b).mp ⟨e, he⟩
    obtain ⟨w₂, hw₂m, hw₂⟩ := (hR₂ n hn hnp).2 b
    have hrm : rd L (trivX B) h₂ (j'' e) ∈ LaHat D := ((hR₂ n hn hnp).1 (j'' e)).mp ⟨0, e, by simp⟩
    refine ⟨w₂ + rd L (trivX B) h₂ (j'' e) - wT, sub_mem (add_mem hw₂m hrm) hwTm, -w₃, neg_mem hw₃m, ?_⟩
    have eA : rd L (trivX B) h₂ (j (f n a)) = L.actG (h₂⁻¹ * h₃) (inAf D a) + n • L.actG (h₂⁻¹ * h₃) w₃ := by
      rw [rd_eq L (trivX B) h₃ h₂, hw₃, map_add (f := _), map_nsmul]
    have eB : rd L (trivX B) h₂ (j (f n a)) = inAf D b + n • w₂ + n • rd L (trivX B) h₂ (j'' e) := by
      rw [← hj''inc, he, map_add (f := _), map_nsmul, rd_add, rd_nsmul, hw₂]
    have e1 := eA.symm.trans eB
    rw [eq_sub_of_add_eq e1, hT]
    simp only [smul_add, smul_sub, map_neg, smul_neg]
    abel
  have hh₂ : h₂ = h₃ * h⁻¹ := by
    rw [← hkey, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  refine ⟨j'', hj''inc, hpl'', ?_, hloc''⟩
  apply (hCo p D G L (trivX B) N hN hNp D'' t'' j'' h₂ (h₁ * h⁻¹) hc₂).mpr
  have hx : (h₁ * h⁻¹)⁻¹ * h₂ = h * (h₃⁻¹ * h₁)⁻¹ * h⁻¹ := by
    rw [hh₂]
    group
  rw [hx]
  exact hconj _ (inv_mem hk₃)
end
