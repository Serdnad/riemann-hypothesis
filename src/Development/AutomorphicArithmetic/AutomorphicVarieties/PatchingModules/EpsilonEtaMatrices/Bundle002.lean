module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem centralizer_rank_le {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (al : Fin n → A) (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    (∀ (N : Type) [AddCommGroup N] [Module A N] (f : N →ₗ[A] Matrix (Fin n) (Fin n) A), Function.Injective f →
      (∀ z, P * f z = f z * P) → Module.finrank A N ≤ n) ∧
    ∀ E Y : Matrix (Fin n) (Fin n) A, P * E = E * P → P * Y = Y * P → E * Y = Y * E := by
  let K := FractionRing A
  have inj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let φ : Matrix (Fin n) (Fin n) A →ₐ[A] Matrix (Fin n) (Fin n) K := (Algebra.ofId A K).mapMatrix
  have φinj : Function.Injective φ := Matrix.map_injective inj
  obtain ⟨h1, h2⟩ := UpperTheory.V.AlgebraTools.centraliser_rank (fun i => algebraMap A K (al i)) (φ P) (inj.comp hal) (by
    have : φ P = P.map (algebraMap A K) := rfl
    rw [this, Matrix.charpoly_map, hP, Polynomial.map_prod]
    simp)
  refine ⟨fun N _ _ f hf hc => ?_, fun E Y hE hY => φinj ?_⟩
  · set U := LinearMap.ker (LinearMap.mulLeft K (φ P) - LinearMap.mulRight K (φ P)) with hU
    let ψ : N →ₗ[A] U :=
      { toFun := fun z => ⟨φ (f z), by
          rw [hU, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            ← map_mul, hc, map_mul, sub_self]⟩
        map_add' := fun y z => Subtype.ext (by simp)
        map_smul' := fun c z => Subtype.ext (by simp) }
    have hψ : Function.Injective ψ := fun y z h => hf (φinj (congrArg Subtype.val h))
    apply Module.finrank_le_of_rank_le
    refine (LinearMap.rank_le_of_injective ψ hψ).trans ?_
    rw [← IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl, ← Module.finrank_eq_rank, h1, Fintype.card_fin]
  · obtain ⟨q, hq⟩ := h2 (φ Y) (by rw [← map_mul, hY, map_mul])
    obtain ⟨r, hr⟩ := h2 (φ E) (by rw [← map_mul, hE, map_mul])
    rw [map_mul, map_mul, hq, hr, ← map_mul, ← map_mul, mul_comm]

private theorem dual_sum_ep_prime_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_eta_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_a_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem finrank_centralizer_W1_le {A : Type} [CommRing A] [IsDomain A] {n a g : ℕ} (al : Fin n → A)
    (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (hev : P ∈ Ev A A n a) (R : Matrix (Fin n) (Fin n) (DD A g)) (hR : ∀ i j, (R i j).a = P i j)
    (N : Submodule A (Matrix (Fin n) (Fin n) (DD A g))) (h1 : N ≤ pairedDualFirstOrderDualMatrixSpace n A A g a) (h2 : ∀ Z ∈ N, R * Z = Z * R) :
    Module.finrank A N ≤ n := by
  obtain ⟨c1, c2⟩ := centralizer_rank_le al P hal hP
  have ha : ∀ Z ∈ N, ∀ i j, (Z i j).a = 0 ∧ (Z i j).ep = 0 := fun Z hZ i j => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · have := (h1 hZ i j).1 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
    · have := (h1 hZ i j).2 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
  have hb : ∀ Z ∈ N, ∀ i j s, (Z i j).ep' s = 0 := fun Z hZ i j s => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact congrFun (((h1 hZ i j).1 h).2.2.1 rfl) s
    · have e := c2 (diagonal fun i => if (i : ℕ) < a then 1 else 0) (Matrix.of fun i j => (Z i j).ep' s) ?_ ?_
      · have e' := congrFun (congrFun e i) j
        rw [diagonal_mul, mul_diagonal, of_apply] at e'
        by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp_all
      · ext u v
        rw [diagonal_mul, mul_diagonal]
        by_cases h' : ((u : ℕ) < a) ↔ ((v : ℕ) < a)
        · simp [h', mul_comm]
        · have : P u v = 0 := (hev u v).2 h'
          simp [this]
      · ext u v
        have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).ep' s) (h2 Z hZ)
        simpa [Matrix.mul_apply, dual_sum_ep_prime_coord, hR, fun i j => (ha Z hZ i j).1] using e'
  have hs : ∀ (c : A) (y : DD A g), (c • y).eta = c * y.eta := fun c y => by
    have hc : c • y = DD.C (algebraMap A A c) * y := rfl
    simp [hc]
  refine c1 N
    { toFun := fun Z => Matrix.of fun i j => (Z.1 i j).eta
      map_add' := fun y z => rfl
      map_smul' := fun c z => by ext i j; simp [hs] } ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro Z hZ
    ext i j
    · exact (ha _ Z.2 i j).1
    · exact congrFun (ha _ Z.2 i j).2 _
    · exact hb _ Z.2 i j _
    · exact congrFun (congrFun hZ i) j
  · rintro ⟨Z, hZ⟩
    change P * (Matrix.of fun i j => (Z i j).eta) = (Matrix.of fun i j => (Z i j).eta) * P
    ext u v
    have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).eta) (h2 Z hZ)
    simpa [Matrix.mul_apply, dual_sum_eta_coord, hR, fun i j => (ha Z hZ i j).1, fun i j => (ha Z hZ i j).2, hb Z hZ] using e'

theorem UpperTheory.V.Pa.h0q :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (σ : F.G₀) (al : Fin n → x.A), Function.Injective al → (mat x.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ k.ρ1 (x.Am m) σ * Y * k.ρ1 (x.Am m) σ⁻¹ = Y}.ncard ≤ Nat.card x.K ^ (m * n + C) := by
  intro l _ F n x k σ al hal hP
  obtain ⟨C, hC⟩ := fixBd l F n x k _ false false false true false false true false Unit (fun _ => 1)
    (fun _ => k.ρ1 x.A σ) (fun _ => k.ρ1 x.A σ⁻¹) false rfl
  refine ⟨C, fun m => ?_⟩
  have red : ∀ g, (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) = k.ρ1 (x.Am m) g := by
    intro g
    change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
    rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
    rfl
  refine le_trans (le_of_eq ?_) ((hC m).trans (Nat.pow_le_pow_right Nat.card_pos ?_))
  · congr 1
    ext Y
    simp only [red, one_smul, Set.mem_setOf_eq, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, true_and]
    rfl
  · refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
    refine finrank_centralizer_W1_le al _ hal hP (x.blk σ) (k.ρ1 x.A σ) (fun i j => ?_) _ (inf_le_left.trans inf_le_left) fun Z hZ => ?_
    · have hc : ∀ c : x.A, algebraMap x.A (DD x.A k.g) c = DD.C c := fun c => rfl
      rw [Kap.ρ1, add_mul, one_mul]
      simp [Matrix.mul_apply, dual_sum_a_coord, DD.epM, NP.ρX, hc]
    · obtain ⟨r1, r2, -⟩ := rho1 l F n x k x.A
      have e : (1 : x.A) • (k.ρ1 x.A σ * (Z * k.ρ1 x.A σ⁻¹)) - Z = 0 := (Submodule.mem_iInf _).1 hZ.2 ()
      rw [one_smul, sub_eq_zero] at e
      conv_rhs => rw [← e]
      rw [mul_assoc, mul_assoc, ← r2, inv_mul_cancel, r1, mul_one]
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def ddEpsCoordAddHom (X : Type) [CommRing X] (g : ℕ) (j : Fin g) : DD X g →+ X where
  toFun y := y.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem commuting_matrix_offdiag_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (i j : Fin n) (hij : i ≠ j) :
    Z i j = 0 := by
  have hmem : Matrix.single j j (1 : x.A) ∈ Ev (PowerSeries x.K) (PowerSeries x.K) n x.a := by
    show ∀ i' j' : Fin n, _
    intro i' j'
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h Iff.rfl
  obtain ⟨s, hs⟩ := x.span _ hmem
  have hcomm : ∀ M ∈ Submodule.span (PowerSeries x.K) (⇑(mat x.ρ) '' ↑F.G'), Z * M = M * Z := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, -, rfl⟩ := hM
      exact (hZ g).symm
    | zero => simp
    | add M N _ _ hM hN => rw [Matrix.mul_add, Matrix.add_mul, hM, hN]
    | smul c M _ hM => rw [Matrix.mul_smul, Matrix.smul_mul, hM]
  have h1 := hcomm _ hs
  rw [Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 := congrFun (congrFun h1 i) j
  simpa [hij, PowerSeries.X_ne_zero] using h2

private theorem skew_commuting_matrix_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (ht : Zᵀ = -Z) : Z = 0 := by
  have h2u : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    have h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    have hl' : l ∣ 2 := by exact_mod_cast h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hl')
  have hu : IsUnit (2 : x.A) := by
    have := h2u.map ((algebraMap x.K (PowerSeries x.K)).comp (algebraMap ℤ_[l] x.K))
    rwa [map_ofNat] at this
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    have h1 := congrFun (congrFun ht i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
    have h2 : (2 : x.A) * Z i i = 0 := by linear_combination h1
    simpa using hu.mul_right_eq_zero.mp h2
  · exact commuting_matrix_offdiag_zero x Z hZ i j hij

private theorem rho1_map_ddBaseRingHom_eq_mat_rho {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseRingHom x.A k.g) = mat x.ρ g := by
  have ha : ∀ y, ddBaseRingHom x.A k.g y = y.a := fun _ => rfl
  have hb : ∀ y : x.A, (algebraMap x.A (DD x.A k.g) y).a = y := fun _ => rfl
  have h0 : (0 : DD x.A k.g).a = 0 := rfl
  rw [Kap.ρ1, Matrix.map_mul]
  refine Matrix.ext fun i j => ?_
  simp [ha, hb, h0, DD.epM, NP.ρX, Matrix.mul_apply, Matrix.one_apply, apply_ite DD.a, DD.one_a]

private theorem map_ep_mul_eq_leibniz {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (M * N).map (fun y => y.ep j) = M.map DD.a * N.map (fun y => y.ep j) + M.map (fun y => y.ep j) * N.map DD.a := by
  refine Matrix.ext fun r c => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]

  rw [show (∑ t, M r t * N t c).ep j = ∑ t, (M r t * N t c).ep j from map_sum (ddEpsCoordAddHom X g j) _ _]
  simp [DD.mul_ep]

private theorem map_a_mul_eq_map_a_mul_map_a {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) :
    (M * N).map DD.a = M.map DD.a * N.map DD.a :=
  Matrix.map_mul (f := ddBaseRingHom X g)

private theorem skew_invariant_M1_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (hm : Z ∈ k.M1 x.A) (ht : Zᵀ = -Z)
    (hZ : ∀ g, k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹ = Z) : Z = 0 := by
  have hA0 : ∀ g : F.G₀, (k.ρ1 x.A g).map DD.a = mat x.ρ g := fun g => rho1_map_ddBaseRingHom_eq_mat_rho k g
  have hinv : ∀ g : F.G₀, mat x.ρ g⁻¹ * mat x.ρ g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have comm_of : ∀ W : Matrix (Fin n) (Fin n) x.A, (∀ g, mat x.ρ g * W * mat x.ρ g⁻¹ = W) →
      ∀ g, mat x.ρ g * W = W * mat x.ρ g := by
    intro W hW g
    calc mat x.ρ g * W = mat x.ρ g * W * (mat x.ρ g⁻¹ * mat x.ρ g) := by rw [hinv, Matrix.mul_one]
      _ = W * mat x.ρ g := by rw [← Matrix.mul_assoc, hW]
  have hA : Z.map DD.a = 0 := by
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map DD.a) (hZ g)
      simpa only [map_a_mul_eq_map_a_mul_map_a, hA0] using this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_a]
  have hE : ∀ t : Fin k.g, Z.map (fun y => y.ep t) = 0 := by
    intro t
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map (fun y => y.ep t)) (hZ g)
      simp only [map_ep_mul_eq_leibniz, map_a_mul_eq_map_a_mul_map_a, hA0, hA, Matrix.mul_zero, Matrix.zero_mul, zero_add,
        add_zero] at this
      exact this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_ep]
  refine Matrix.ext fun r c => ?_
  have hm' : (Z r c).ep' = 0 ∧ (Z r c).eta = 0 := by
    obtain ⟨h1, h2⟩ := (show ∀ i j : Fin n, _ from hm) r c
    by_cases hb : (↑r < x.a ↔ ↑c < x.a)
    · obtain ⟨-, -, h3, h4⟩ := h1 hb
      exact ⟨h3 rfl, h4 rfl⟩
    · obtain ⟨-, -, h3, h4⟩ := h2 hb
      exact ⟨h3 rfl, h4 rfl⟩
  rw [Matrix.zero_apply]
  refine DD.ext ?_ (funext fun t => ?_) ?_ ?_
  · simpa using congrFun (congrFun hA r) c
  · simpa using congrFun (congrFun (hE t) r) c
  · exact hm'.1
  · exact hm'.2

private def ddMapRingHom {A X : Type} [CommRing A] [CommRing X] (g : ℕ) (f : A →+* X) : DD A g →+* DD X g where
  toFun y := ⟨f y.a, fun j => f (y.ep j), fun j => f (y.ep' j), f y.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

private theorem rho1_map_ddMapRingHom_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (X : Type) [CommRing X] [Algebra x.A X] (g : F.G₀) :
    (k.ρ1 x.A g).map (ddMapRingHom k.g (algebraMap x.A X)) = k.ρ1 X g := by
  have hr : ∀ y, ddMapRingHom k.g (algebraMap x.A X) y = ⟨algebraMap x.A X y.a, fun j => algebraMap x.A X (y.ep j), fun j => algebraMap x.A X (y.ep' j), algebraMap x.A X y.eta⟩ := fun _ => rfl
  have hb : ∀ (Y : Type) [CommRing Y] [Algebra x.A Y] (y : x.A), algebraMap x.A (DD Y k.g) y = ⟨algebraMap x.A Y y, 0, 0, 0⟩ := fun _ _ _ _ => rfl
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul]
  congr 1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, DD.add_ep, DD.one_ep, DD.add_ep', DD.one_ep', DD.add_a, DD.add_eta, DD.one_eta, DD.one_a]
    · refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, hij, DD.zero_ep, DD.zero_a]
  · refine Matrix.ext fun i j => ?_
    refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, hb, NP.ρX]

theorem UpperTheory.V.Pa.h0G :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧ ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ L G G0 h n x k hl
  obtain ⟨C, hC⟩ := fixBd l G0.frame n x k (k.M1 x.A) true false false false false true false false
    G0.G₀ (fun _ => 1) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A s⁻¹) true rfl
  refine ⟨C, fun m => ?_⟩
  have hfin : ∀ W : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)), W = ⊥ →
      Nat.card x.K ^ (m * Module.finrank x.A W + C) = Nat.card x.K ^ C := by
    rintro W rfl
    simp
  refine le_trans (le_of_eq ?_) ((hC m).trans (le_of_eq (hfin _ ?_)))
  · clear hC hfin
    congr 1
    ext Y
    have hred : ∀ s : G0.G₀, ((k.ρ1 x.A s).map fun y : DD x.A k.g =>
        (⟨(algebraMap x.A (x.Am m)) y.a, fun j => (algebraMap x.A (x.Am m)) (y.ep j),
          fun j => (algebraMap x.A (x.Am m)) (y.ep' j), (algebraMap x.A (x.Am m)) y.eta⟩ : DD (x.Am m) k.g))
        = k.ρ1 (x.Am m) s :=
      fun s => rho1_map_ddMapRingHom_eq_rho1 k (x.Am m) s
    simp only [Set.mem_setOf_eq, one_smul, forall_const, hred]
    exact Iff.rfl
  · rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, ↓reduceIte] at hZ
    obtain ⟨⟨hm, ht⟩, hfix⟩ := hZ
    apply skew_invariant_M1_zero k hl Z hm
    · simpa [add_eq_zero_iff_eq_neg] using ht
    · intro g
      have := hfix g
      simpa [sub_eq_zero, Matrix.mul_assoc] using this
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseCompRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem sandwich_map_smul {R X : Type} [CommRing R] [CommRing X] {n : ℕ} (α : R → X) (φ : R →+ X)
    (c : R) (P Z Q : Matrix (Fin n) (Fin n) R) (h : ∀ i j u, φ (u * Z i j) = α u * φ (Z i j))
    (hα : ∀ u v, α (u * v) = α u * α v) :
    (c • (P * Z * Q)).map φ = α c • (P.map α * Z.map φ * Q.map α) := by
  ext i j

  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
  map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show c * (P i a * Z a b * Q b j) = (c * (P i a * Q b j)) * Z a b by ring, h, hα, hα]
  ring

private theorem rho1_map_ddBaseCompRingHom_eq_mat {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseCompRingHom x.A k.g) = mat x.ρ g := by
  have h1 : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (ddBaseCompRingHom x.A k.g) = 1 := by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact add_eq_left.2 (Matrix.ext fun _ _ => rfl)
  rw [Kap.ρ1, Matrix.map_mul, h1, one_mul]
  exact Matrix.ext fun _ _ => rfl

private theorem rho1_map_algebraMap_am_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (m : ℕ) (g : F.G₀) :
    (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j),
      fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) g := by
  change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
  rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
  refine congrArg₂ (· * ·) (congrArg (1 + ·) (Matrix.ext fun i j => ?_)) (Matrix.ext fun i j => ?_)
  · ext <;> simp [DD.epM]
  · exact (x.redD k.g m).commutes _

private theorem site_vector_first {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (D : Subgroup F.G₀)
    (h4 : x.N4 D) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (ha : ∀ i j, (Z i j).a = 0) (he : ∀ i j, (Z i j).ep = 0)
    (hZ : ∀ g ∈ D, epsD k x.A g • (k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹) = Z) : Z = 0 := by
  have key : ∀ φ : DD x.A k.g →+ x.A, (∀ i j u, φ (u * Z i j) = u.a * φ (Z i j)) → ∀ i j, φ (Z i j) = 0 := by
    intro φ hφ
    have : Z.map φ = 0 := by
      refine h4 _ fun g hg => ?_
      have e := sandwich_map_smul (ddBaseCompRingHom x.A k.g) φ (epsD k x.A g) (k.ρ1 x.A g) Z (k.ρ1 x.A g⁻¹) hφ (map_mul _)
      rw [hZ g hg, rho1_map_ddBaseCompRingHom_eq_mat, rho1_map_ddBaseCompRingHom_eq_mat] at e
      conv_rhs => rw [e]
      rw [smul_mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      rfl
    exact fun i j => congrFun (congrFun this i) j
  have h' : ∀ t i j, (Z i j).ep' t = 0 := fun t =>
    key ⟨⟨fun y => y.ep' t, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).ep' t = u.a * (Z i j).ep' t
      simp [ha]
  have h'' : ∀ i j, (Z i j).eta = 0 :=
    key ⟨⟨fun y => y.eta, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).eta = u.a * (Z i j).eta
      simp [ha, he, h']
  refine Matrix.ext fun i j => ?_
  ext <;> simp [ha, he, h', h'']

theorem UpperTheory.V.Pa.h0v0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (D : Subgroup F.G₀), x.N4 D → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D, epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ F n x k D h4
  obtain ⟨C, hC⟩ := UpperTheory.V.Pa.fixBd l F n x k _ false false false true false false true false D
    (fun s => algebraMap ℤ_[l] x.A (F.ε (s : F.G₀) : ℤ_[l])) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A (s : F.G₀)⁻¹)
    false rfl
  refine ⟨C, fun m => ?_⟩
  have h := hC m
  rw [(Submodule.eq_bot_iff (_ ⊓ _ ⊓ _)).2 ?_, finrank_bot, mul_zero, zero_add] at h
  · refine le_of_eq_of_le ?_ h
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, rho1_map_algebraMap_am_eq_rho1, Subtype.forall, epsD, algebraMap_smul, Bool.false_eq_true, false_imp_iff,
      true_and]
    rfl
  · rintro Z ⟨⟨h1, -⟩, h2⟩
    refine site_vector_first k D h4 Z (fun i j => ?_) (fun i j => ?_) fun g hg => ?_
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).1 rfl
      · exact ((h1 i j).2 e).1 rfl
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).2.1 rfl
      · exact ((h1 i j).2 e).2.1 rfl
    · have e := (Submodule.mem_iInf _).1 h2 ⟨g, hg⟩
      rw [epsD, algebraMap_smul, mul_assoc, ← sub_eq_zero]
      exact e
end
