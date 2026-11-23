module

public import Development.EtaleCohomology.DivisorCycles.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle050
public import Mathlib.LinearAlgebra.Lagrange
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

section

open Matrix

namespace LateralTheory.DivDb.BigCorner₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N n : ℕ}

def gens (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x | ∃ a ∈ A, ∃ g, x = a * (ρ g : Mat C N)}

lemma rmul (ρ : Γ →* GL (Fin N) C) (g h : Γ) : (ρ (g * h) : Mat C N) = ρ g * ρ h := by simp

lemma rone (ρ : Γ →* GL (Fin N) C) : (ρ 1 : Mat C N) = 1 := by simp

lemma rinv (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g : Mat C N) * ρ g⁻¹ = 1 := by
  rw [← rmul, mul_inv_cancel, rone]

lemma rinv' (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g⁻¹ : Mat C N) * ρ g = 1 := by
  rw [← rmul, inv_mul_cancel, rone]

lemma span_mul (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A)
    (x y : Mat C N) (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) :=
  _root_.UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul ρ A hN x y hx hy

lemma one_mem_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) :
    (1 : Mat C N) ∈ Submodule.span C (gens ρ A) :=
  Submodule.subset_span ⟨1, A.one_mem, 1, by rw [rone, one_mul]⟩

noncomputable def RR (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) :
    Subalgebra C (Mat C N) :=
  (Submodule.span C (gens ρ A)).toSubalgebra (one_mem_span ρ A) (span_mul ρ A hN)

lemma mem_RR {ρ : Γ →* GL (Fin N) C} {A : Subalgebra C (Mat C N)} {hN : Normd ρ A} {x : Mat C N} :
    x ∈ RR ρ A hN ↔ x ∈ Submodule.span C (gens ρ A) := Iff.rfl

lemma corner_gen (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ gens ρ A) : ∃ c : C, p i * x * p i = c • p i := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  by_cases h : p i * a * (ρ g : Mat C N) * p i = 0
  · exact ⟨0, by rw [zero_smul, ← mul_assoc, h]⟩
  · obtain ⟨w, hw, hpw⟩ := hyp g i ⟨a, ha, h⟩
    have ha' : (ρ g⁻¹ : Mat C N) * a * ρ g ∈ A := by simpa using hN g⁻¹ a ha
    have e1 : a * (ρ g : Mat C N) = ρ g * ((ρ g⁻¹ : Mat C N) * a * ρ g) := by
      simp only [← mul_assoc, rinv, one_mul]
    obtain ⟨c, hc⟩ := hC.2 _ (A.mul_mem hw ha') i
    refine ⟨c, ?_⟩
    rw [e1, ← mul_assoc, ← mul_assoc, hpw, ← hc]; simp only [mul_assoc]

lemma corner_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∃ c : C, p i * x * p i = c • p i := by
  induction hx using Submodule.span_induction with
  | mem x hx' => exact corner_gen ρ A p hC hN hyp i hx'
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨c, hc⟩ := hu; obtain ⟨d, hd⟩ := hv
    exact ⟨c + d, by rw [mul_add, add_mul, hc, hd, add_smul]⟩
  | smul c u _ hu =>
    obtain ⟨d, hd⟩ := hu
    exact ⟨c * d, by rw [mul_smul_comm, smul_mul_assoc, hd, smul_smul]⟩

lemma normd_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) (g : Γ)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) :
    (ρ g : Mat C N) * x * (ρ g⁻¹ : Mat C N) ∈ Submodule.span C (gens ρ A) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, h, rfl⟩ := hx'
    refine Submodule.subset_span ⟨(ρ g : Mat C N) * a * ρ g⁻¹, hN g a ha, g * h * g⁻¹, ?_⟩
    have key : (ρ g⁻¹ : Mat C N) * (ρ g * (ρ h * ρ g⁻¹)) = ρ h * ρ g⁻¹ := by
      rw [← mul_assoc, rinv', one_mul]
    rw [rmul, rmul]; simp only [mul_assoc, key]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hu

lemma keeps_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hK : Keeps ρ A)
    (W : Submodule C (Fin N → C)) (hW : ∀ g, ∀ v ∈ W, (ρ g : Mat C N) *ᵥ v ∈ W)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∀ v ∈ W, x *ᵥ v ∈ W := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, g, rfl⟩ := hx'
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    exact hK W hW a ha _ (hW g v hv)
  | zero => intro v _; simp
  | add u v _ _ hu hv => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hu w hw) (hv w hw)
  | smul c u _ hu => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hu w hw)

end LateralTheory.DivDb.BigCorner₂

open LateralTheory.DivDb.BigCorner₂ in
theorem LateralTheory.DivDb.BigCorner₂.BigCorner_of : LateralTheory.DivDb.BigCorner := by
  intro Γ C _ _ N n ρ A p hC hN hK hyp
  refine ⟨RR ρ A hN, fun g => ?_, ⟨fun i => ?_, fun a ha i => ?_⟩, fun g a ha => ?_, fun W hW a ha => ?_⟩
  · exact mem_RR.2 (Submodule.subset_span ⟨1, A.one_mem, g, (one_mul _).symm⟩)
  · exact mem_RR.2 (Submodule.subset_span ⟨p i, hC.1 i, 1, by rw [rone, mul_one]⟩)
  · exact corner_span ρ A p hC hN hyp i (mem_RR.1 ha)
  · exact mem_RR.2 (normd_span ρ A hN g (mem_RR.1 ha))
  · exact keeps_span ρ A hK W hW (mem_RR.1 ha)
end

section

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ProjPf

variable {C : Type} [Field C] {N n : ℕ}

theorem root_minpoly (X : LateralTheory.DivDb.Mat C N) (c : C) (h : X.charpoly.IsRoot c) :
    (minpoly C X).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)
  rw [← Matrix.minpoly_toLin']
  exact Module.End.hasEigenvalue_iff_isRoot.1 h1

theorem prod_dvd (e : Fin n → C) (he : Function.Injective e) (f : C[X]) (hf : ∀ k, f.eval (e k) = 0) :
    (∏ k, (X - Polynomial.C (e k))) ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · exact fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab
  · intro k _; exact Polynomial.dvd_iff_isRoot.2 (hf k)

theorem minpoly_eq (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) :
    minpoly C X = ∏ k, (Polynomial.X - Polynomial.C (e k)) := by
  obtain ⟨q, hq0, hqd, hq⟩ := hD
  have hint : IsIntegral C X := Matrix.isIntegral X
  have hmon : (minpoly C X).Monic := minpoly.monic hint
  have hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X :=
    prod_dvd e he _ (fun k => root_minpoly X _ (hr k))
  have hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdeg : (minpoly C X).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0
    omega
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hdeg

theorem evb (e : Fin n → C) (he : Function.Injective e) (i k : Fin n) :
    (Lagrange.basis Finset.univ e i).eval (e k) = if k = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)

theorem vanish (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) (f : C[X])
    (hf : ∀ k, f.eval (e k) = 0) : aeval X f = 0 := by
  rw [← minpoly.dvd_iff, minpoly_eq X e he hD hr]
  exact prod_dvd e he f hf

end LateralTheory.DivDb.ProjPf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.ProjPf

theorem Proj_of : Proj := by
  intro C _ N n X e he hD hr
  classical
  set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb
  have V := vanish X e he hD hr
  refine ⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩
  · show aeval X (b i) * aeval X (b i) = aeval X (b i)
    rw [← sub_eq_zero, ← map_mul, ← map_sub]
    apply V; intro k
    simp only [hb, eval_sub, eval_mul, evb e he]
    split_ifs <;> simp
  · show aeval X (b i) * aeval X (b j) = 0
    rw [← map_mul]
    apply V; intro k
    simp only [hb, eval_mul, evb e he]
    split_ifs with h1 h2 <;> simp_all
  · show ∑ i, aeval X (b i) = 1
    have h : aeval X (∑ i, b i - 1) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]
      simp

    rw [map_sub, map_one, map_sum, sub_eq_zero] at h
    exact h
  · intro h0
    have h1 : minpoly C X ∣ b i := (minpoly.dvd_iff).2 h0
    rw [minpoly_eq X e he hD hr] at h1
    have hne : b i ≠ 0 := Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)] at h2
    have h3 : (b i).natDegree = n - 1 := by
      simp only [hb]
      rw [Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]
      simp
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h2
    have := i.pos
    omega
  · have : aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]
      simp

    rw [map_sub, aeval_X, map_sum, sub_eq_zero] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, aeval_C, Algebra.smul_def]
  · exact Polynomial.aeval_mem_adjoin_singleton C _

end LateralTheory.DivDb
end
