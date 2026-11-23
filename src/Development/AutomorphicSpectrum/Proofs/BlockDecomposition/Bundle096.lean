module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Mathlib.RingTheory.Artinian.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle073
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle074
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Mathlib.Topology.Sheaves.Presheaf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LimLift

open CrystallineSemistableComparison.CechClassBoundaries

variable {R : Type} [CommRing R]

theorem cls_congr {K : Cx.{1} R} {j : ℕ} {a b : K.X j} (h : a = b) (ha : K.d j a = 0) (hb : K.d j b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h
  rfl

theorem pow_tf {K : Cx.{1} R} {c : R} (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (n j : ℕ) (x : K.X j)
    (h : c ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (ht _ _ h)

theorem ker_red {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (j : ℕ) (z : K.H j) (hz : r.mapH j z = 0) :
    ∃ y, z = c ^ n • y := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1] at hz
  have hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0 := by
    cases j with
    | zero =>
      refine ⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩
      rw [sub_zero]
      exact (mem_boundaries_zero_iff _).1 hz
    | succ j =>
      obtain ⟨b, hb⟩ := (mem_Bs _).1 hz
      obtain ⟨v, rfl⟩ := hs j b
      refine ⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩
      rw [map_sub, ← r.comm, hb, sub_self]
  obtain ⟨v, hvB, hvd, h0⟩ := hv
  obtain ⟨y, hy⟩ := (hk j _).1 h0
  have hdy : K.d j y = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hy, map_sub, ha, hvd, sub_zero]
  refine ⟨K.cls y hdy, ?_⟩
  have hcy : K.d j (c ^ n • y) = 0 := by rw [map_smul, hdy, smul_zero]
  rw [← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]
  simpa using hvB

theorem kill_H {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (j : ℕ) (h : L.H j) : c ^ n • h = 0 := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 h
  obtain ⟨a, rfl⟩ := hs j w
  have h0 : c ^ n • r.f j a = 0 := by
    rw [← map_smul]
    exact (hk j _).2 ⟨a, rfl⟩
  have hd : L.d j (c ^ n • r.f j a) = 0 := by rw [h0, map_zero]
  rw [← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]
  exact zero_mem _

theorem lift_level {K L : Cx.{1} R} (c : R) (n k j : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0)
    (hA : ∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) (x : L.H j) :
    ∃ y : K.H j, r.mapH j y = c ^ k • x := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 x
  obtain ⟨a, rfl⟩ := hs j w
  have h1 : r.f (j + 1) (K.d j a) = 0 := by rw [← r.comm]; exact hw
  obtain ⟨b, hb⟩ := (hk (j + 1) _).1 h1
  have hdb : K.d (j + 1) b = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hb, K.dd]
  have hcb : K.d (j + 1) (c ^ n • b) = 0 := by rw [map_smul, hdb, smul_zero]
  have h2 : c ^ n • K.cls b hdb = 0 := by
    rw [← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]
    exact (mem_Bs _).2 ⟨a, hb⟩
  have h3 := hA _ n h2
  have hkb : K.d (j + 1) (c ^ k • b) = 0 := by rw [map_smul, hdb, smul_zero]
  rw [← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1] at h3
  obtain ⟨e, he⟩ := (mem_Bs _).1 h3
  have hy : K.d j (c ^ k • a - c ^ n • e) = 0 := by
    rw [map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a := by
    rw [map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]
  have hd : L.d j (c ^ k • r.f j a) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨K.cls _ hy, ?_⟩
  rw [mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]
  exact cls_congr hr _ _

theorem mapH_tr {K L M : Cx.{1} R} (r : Cx.Hom K L (RingHom.id R)) (r' : Cx.Hom K M (RingHom.id R))
    (t : Cx.Hom L M (RingHom.id R)) (j : ℕ) (h : ∀ x, t.f j (r.f j x) = r'.f j x) (z : K.H j) :
    t.mapH j (r.mapH j z) = r'.mapH j z := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]
  exact cls_congr (h a) _ _

theorem lim_lift : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  intro R _ K Kn c red tr hc hs hk ht j k hA hB hC
  refine ⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩
  choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)
  have hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u := by
    intro n
    refine ker_red c n (red n) (hs n) (hk n) ht j _ ?_
    rw [map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]
  obtain ⟨z, hz⟩ := hC y hdiff
  refine ⟨z, fun n => ?_⟩
  obtain ⟨u, hu⟩ := hz n
  have e : z = c ^ k • y n + c ^ n • u := by rw [← hu]; abel
  rw [e, map_add (f := _), map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]

end GlobalTheory.CompanionTheory.LimLift
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.artinian_limit_lift_of_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W), (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n), (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) → ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  first | exact @GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | exact GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | (intros; apply GlobalTheory.CompanionTheory.ArtinTower.exists_compatible <;> assumption)
end

section

open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatDP

variable {B : Type} [CommRing B] [Algebra ℚ B]

theorem inv_fact_smul_add_pow_mem (S : Subring B) {z w : B}
    (hz : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • z ^ k ∈ S) (hw : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • w ^ k ∈ S)
    (k : ℕ) : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k ∈ S := by
  have e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k =
      ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i)) := by
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]
    congr 1
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
    have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
    field_simp
  rw [e]
  exact S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)

variable {W : Type} [CommRing W] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem inv_fact_smul_dpE_pow (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • Lat.dpE f ξ l M j ^ k =
      ((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j) := by
  have hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ) := by
    exact_mod_cast Nat.uniformBell_mul_eq k hj
  have hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
  have h3 : ((k * j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k * j).factorial_ne_zero
  rw [Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]
  congr 1
  have h4 : (j.factorial : ℚ) ^ k ≠ 0 := pow_ne_zero _ h2
  rw [eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]
  field_simp

theorem inv_fact_smul_term_mem (c : W) (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k ∈ Lat.sub f ξ l M := by
  have e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k =
      f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j)) := by
    rw [mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]
  rw [e]
  have hf : f c ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)

theorem inv_fact_smul_sum_mem {n : ℕ} (c : Fin n → W) (s : Finset (Fin n)) (k : ℕ) :
    ((k.factorial : ℚ))⁻¹ • (∑ i ∈ s, f (c i) * Lat.dpE f ξ l M (i + 1)) ^ k ∈ Lat.sub f ξ l M := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa using (Lat.sub f ξ l M).one_mem
    · simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k

theorem dpClosed {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ)
    (h : Lat.Hyp f ξ l m) : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ) := by
  intro x hx k
  obtain ⟨n, c, e⟩ := (GlobalTheory.T.mem_lattice_ideal_iff_sum f ξ l M m h x).1 hx
  refine ⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']
  rfl

end GlobalTheory.CompanionTheory.LatDP
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

namespace GlobalTheory.CompanionTheory.LsRho

variable {W : Type} [CommRing W]

theorem mapH_eq_self {K : Cx.{1} W} (φ : Cx.Hom K K (RingHom.id W)) (n : ℕ)
    (h : ∀ x, φ.f n x = x) (u : K.H n) : φ.mapH n u = u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_of_comp {K L P : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L P (RingHom.id W))
    (χ : Cx.Hom K P (RingHom.id W)) (n : ℕ) (h : ∀ x, χ.f n x = ψ.f n (φ.f n x)) (u : K.H n) :
    χ.mapH n u = ψ.mapH n (φ.mapH n u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_comp_eq_smul {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L K (RingHom.id W))
    (s : W) (n : ℕ) (h : ∀ x, ψ.f n (φ.f n x) = s • x) (u : K.H n) :
    ψ.mapH n (φ.mapH n u) = s • u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem kill (l : ℕ) (K : Cx.{1} W) (j n : ℕ) (x : (qsys l K j).M n) : ((l : W) ^ n) • x = 0 := by
  change ((l : W) ^ n) • (x : (quo l K n).H j) = 0
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : ((l : W) ^ n) • z = 0 := by
    refine Subtype.ext ?_
    change ((l : W) ^ n) • z.1 = 0
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ z.1
    rw [← hw]
    change Submodule.Quotient.mk (((l : W) ^ n) • w) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [← Submodule.Quotient.mk_smul, hz]
  rfl

end GlobalTheory.CompanionTheory.LsRho

end
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.hensel_polynomial_refinement : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
  first | exact @GlobalTheory.CompanionTheory.AicStep.aic_step | exact GlobalTheory.CompanionTheory.AicStep.aic_step | (intros; apply GlobalTheory.CompanionTheory.AicStep.aic_step <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BigStep

def gens {A : Type} [CommRing A] (𝓔 : Set (Set (MvPolynomial (Fin 3) A))) :
    Set (MvPolynomial (𝓔 × Fin 3) A) :=
  {f | ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
    f = MvPolynomial.rename (fun t => (E, t)) q}

theorem exists_kill (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A)
    {𝓔 : Set (Set (MvPolynomial (Fin 3) A))}
    (hfin : ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 →
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
        ∀ E ∈ J, Pt (algebraMap A B) E)
    (F : Finset (MvPolynomial (𝓔 × Fin 3) A)) (hF : (F : Set _) ⊆ gens 𝓔) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ τ : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B, ∀ g ∈ F, τ g = 0 := by
  classical
  have hg : ∀ g : {g // g ∈ F}, ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
      g.1 = MvPolynomial.rename (fun t => (E, t)) q := fun g => hF g.2
  choose Eg qg hq hgq using hg
  obtain ⟨B₁, i1, i2, hP, hC, hpt⟩ := hfin (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact (Eg g).2)
  have hpt' : ∀ E : 𝓔, ∃ y : Fin 3 → B₁, E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1) →
      ∀ q ∈ E.1, MvPolynomial.eval₂ (algebraMap A B₁) y q = 0 := by
    intro E
    by_cases h : E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    · obtain ⟨y, hy⟩ := hpt _ h
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hpt'
  refine ⟨B₁, i1, i2, hP, hC, MvPolynomial.aeval (fun v => y v.1 v.2), ?_⟩
  intro g hg
  have e := hgq ⟨g, hg⟩
  simp only at e
  rw [e, MvPolynomial.aeval_rename, MvPolynomial.aeval_def]
  exact hy _ ⟨⟨g, hg⟩, rfl⟩ _ (hq ⟨g, hg⟩)

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := by
  classical
  intro p _ A _ r 𝓔 hA hfin
  have hpS : (p : MvPolynomial (𝓔 × Fin 3) A) = 0 := by
    have := congrArg (algebraMap A (MvPolynomial (𝓔 × Fin 3) A)) hA.char
    simpa using this
  obtain ⟨B, instB, i, hQ⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (MvPolynomial (𝓔 × Fin 3) A)
    (Ideal.span (gens 𝓔)) hpS
  letI instAB : Algebra A B := (i.comp MvPolynomial.C).toAlgebra
  let iA : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B := { i with commutes' := fun _ => rfl }
  refine ⟨B, instB, instAB, hQ.pf, ?_, ?_, ?_⟩
  · apply GlobalTheory.CompanionTheory.CovCmp.cov_of_solv
    intro m n a c hS
    obtain ⟨k, s, hs⟩ := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow p A (MvPolynomial (𝓔 × Fin 3) A) B iA
      (Ideal.span (gens 𝓔)) m n a c hA.char hQ hS
    have hT := fun t => Submodule.mem_span_finite_of_mem_span (hs t)
    choose G hGs hGm using hT
    obtain ⟨B₁, i1, i2, hP, hC, τ, hτ⟩ := exists_kill p r hfin (Finset.univ.biUnion G) (by
      intro g hg
      obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hg)
      exact hGs t ht)
    refine ⟨B₁, i1, i2, hC,
      GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow p A B₁ m n k a c hP ⟨fun j => τ (s j), fun t => ?_⟩⟩
    have hle : Ideal.span (G t : Set (MvPolynomial (𝓔 × Fin 3) A)) ≤ RingHom.ker τ :=
      Ideal.span_le.2 fun g hg =>
        hτ g (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, Finset.mem_coe.1 hg⟩)
    have h0 := hle (hGm t)

    rw [RingHom.mem_ker, map_sub, map_sum, AlgHom.commutes, sub_eq_zero] at h0
    simpa only [map_smul] using h0
  · intro E hE
    refine ⟨fun t => i (MvPolynomial.X ((⟨E, hE⟩ : 𝓔), t)), fun q hq => ?_⟩
    have hz : i (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 :=
      (hQ.ker _).2 ⟨0, by
        have h : MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q ∈ Ideal.span (gens 𝓔) :=
          Ideal.subset_span ⟨⟨E, hE⟩, q, hq, rfl⟩
        simpa using h⟩
    have hi : i = MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v)) :=
      MvPolynomial.ringHom_ext (by simp) (by simp)
    have hz' : MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v))
        (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 := by
      rw [← hi]; exact hz
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename] at hz'
    exact hz'
  · intro T _ x hT hpts
    have hpts' : ∀ E : 𝓔, ∃ y : Fin 3 → T, ∀ q ∈ E.1, MvPolynomial.eval₂ x y q = 0 :=
      fun E => hpts E.1 E.2
    choose y hy using hpts'
    have hle : Ideal.span (gens 𝓔) ≤
        RingHom.ker (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨E, q, hq, rfl⟩
      show MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2) _ = 0
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
      exact hy E q hq
    obtain ⟨ψ, hψ, -⟩ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift p _ B T i _
      (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) hQ hT (fun g hg => hle hg)
    refine ⟨ψ, RingHom.ext fun a => ?_⟩
    have := RingHom.congr_fun hψ (MvPolynomial.C a)
    show ψ (i (MvPolynomial.C a)) = x a
    simpa using this

end GlobalTheory.CompanionTheory.BigStep
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.perfect_frobenius_root_solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | exact GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

theorem _root_.GlobalTheory.T.perfect_tensor_product : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | exact GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pf_tensor <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.twisted_jacquet_exact_smooth : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ → ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) → (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧ IsCompact (L : Set G)) → ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g → LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | exact GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | (intros; apply GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker <;> assumption)
end

section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegmentWords

theorem wt_inSh_antisymm : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  intro T s hs hj L M hL hM hLM hML
  by_contra hne
  have h1 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj L (M : Multiset (ASeg T)) hL hLM (Ne.symm hne)
  have h2 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj M (L : Multiset (ASeg T)) hM hML hne
  exact lt_asymm h1 h2

end GlobalTheory.CompanionTheory.SegmentWords
end
