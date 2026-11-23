module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle007
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem module_finite_z1_padicInt (l : ℕ) [Fact l.Prime] {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ ψ : G →* kˣ) (hΦ : PhiCond (Γ := G) l)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) : Finite (Z1 χ ψ) := by
  classical
  letI := ZMod.algebra k l
  haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite
  let N : Subgroup G := χ.ker ⊓ ψ.ker
  have hNo : IsOpen (N : Set G) := by
    show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)
    rw [Subgroup.coe_inf]
    exact hχ.inter hψ
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI := hΦ N hNo
  let b := Module.finBasis (ZMod l) k
  have mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧
      ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k) := fun a ha => ha
  have hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y := by
    intro a ha x y
    have hx : χ (x : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1
    have hy : ψ (y : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
    rw [(mem a ha).2, hx, hy]
    simp [add_comm]
  let φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l)) :=
    fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by
      intro x y
      simp [hadd a ha x y, ofAdd_add])
  have hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N) := by
    intro a ha i
    have hlc : IsLocallyConstant (fun x : N => b.repr (a x) i) :=
      ((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)
    have e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0} := by
      ext x
      simp [φ, MonoidHom.mem_ker]
    rw [e]
    exact hlc.isOpen_fiber 0
  let F : Z1 χ ψ → (G ⧸ N → k) ×
      (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}) :=
    fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)
  refine Finite.of_injective F ?_
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hN' : ∀ x : N, a x = a' x := by
    intro x
    apply b.repr.injective
    ext i
    exact congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2
  apply Subtype.ext
  funext g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  have e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out := congrFun h1 _
  have hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G) := by
    rw [hn]; simp [mul_assoc]
  show a g = a' g
  rw [hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]

theorem UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ h, MultFree χ h := by
  intro l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj
  refine ⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩
  haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank k (Z1 (χ i) (χ j)) ≤ ∑ j', Module.finrank k (Z1 (χ i) (χ j')) :=
        Finset.single_le_sum (f := fun j' => Module.finrank k (Z1 (χ i) (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Module.finrank k (Z1 (χ i') (χ j')) :=
        Finset.single_le_sum (f := fun i' => ∑ j', Module.finrank k (Z1 (χ i') (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem hom_two {n : ℕ} {A : Type} [CommRing A] (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
  classical
  have hd : ∀ d ∈ P.support, d 0 + d 1 = n := fun d hd => by
    have h := hP (MvPolynomial.mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  refine ⟨fun i => ∑ d ∈ P.support with d 1 = i, P.coeff d, fun S _ _ s t => ?_⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1)) (g := fun d => d 1)
      (fun d h => by have := hd d h; simp only [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d h => ?_
  rw [Finset.mem_filter] at h
  have h0 : d 0 = n - i := by have := hd d h.1; have := h.2; omega
  simp [Fin.prod_univ_two, h0, h.2, mul_assoc]

private theorem lam_two {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E)
    (S : Type) [CommRing S] [Algebra A S] (s t : S) :
    D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (D.lam i x) * s ^ (n - i) * t ^ i := by
  obtain ⟨h1, h2⟩ := d_poly D ![1, x]
  obtain ⟨c, hc⟩ := hom_two _ h1
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
    intro S _ _ s t
    rw [← hc, ← h2]
    simp [Fin.sum_univ_two]
  have hl : ∀ j ∈ Finset.range (n + 1), D.lam j x = c j := by
    intro j hj
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * c i) * X ^ (n - i) := by
      rw [Det.chi, sub_eq_add_neg, ← neg_tmul, key]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
        map_one]
      ring
    rw [Det.lam, hchi, finsetSum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl, ← mul_assoc, ← mul_pow]; simp
    · intro i hi hij
      have : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro h; exact absurd hj h
  rw [key]
  exact Finset.sum_congr rfl fun i hi => by rw [hl i hi]

theorem UpperTheory.V.CA.d_chi :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), D.lam 0 x = 1 ∧ D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) ∧ D.D A[X] (1 + X ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), C (D.lam i x) * X ^ i ∧ D.lam n x = D.val x ∧ (D.chi x).Monic ∧ (D.chi x).natDegree ≤ n ∧ ∀ (a : A) (i : ℕ), i ≤ n → D.lam i (a • x) = a ^ i * D.lam i x := by
  intro n A E _ _ _ D x
  have h0 : D.lam 0 x = 1 := by
    have h := lam_two D x A 1 0
    rw [zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, map_one, Finset.sum_range_succ'] at h
    simpa using h.symm
  have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) := by
    conv_lhs => rw [Det.chi, sub_eq_add_neg, ← neg_tmul, lam_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
      map_one]
    ring
  have h1 : ∀ y : E, D.D A[X] (1 + X ⊗ₜ y) = ∑ i ∈ Finset.range (n + 1), C (D.lam i y) * X ^ i := by
    intro y
    rw [Algebra.TensorProduct.one_def, lam_two]
    simp
  have hdeg : (D.chi x).natDegree ≤ n := by
    rw [hchi]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  refine ⟨h0, hchi, h1 x, ?_, ?_, hdeg, ?_⟩
  · have h := lam_two D x A 0 1
    rw [zero_tmul, zero_add, Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      have : n - i ≠ 0 := by rw [Finset.mem_range] at hi; omega
      simp [this])] at h
    change _ = D.D A (1 ⊗ₜ x)
    rw [h]; simp
  · refine monic_of_natDegree_le_of_coeff_eq_one n hdeg ?_
    simpa [Det.lam] using h0
  · intro a j hj
    have h := h1 (a • x)
    rw [← smul_tmul, Algebra.TensorProduct.one_def, lam_two] at h
    have h' : ∑ i ∈ Finset.range (n + 1), C (a ^ i * D.lam i x) * X ^ i =
        ∑ i ∈ Finset.range (n + 1), C (D.lam i (a • x)) * X ^ i := by
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow,
        smul_eq_C_mul]
      ring
    have h2 := congrArg (fun p => p.coeff j) h'
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hj,
      if_true] at h2
    exact h2.symm
end
