module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

section

open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_splits_of_separable_residue (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  have hinj : Function.Injective (algebraMap V Ω) := IsFractionRing.injective V Ω

  have hdegree : ∀ g : Polynomial Ω, Irreducible g → g ∣ q.map (algebraMap V Ω) →
      g.degree = 1 := by
    intro g hg hgd
    obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hq hgd
    have hg0 : g ≠ 0 := hg.ne_zero
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hmap : g₀.map (algebraMap V Ω) = g * C g.leadingCoeff⁻¹ := by
      set c := g.leadingCoeff with hc
      rw [← hg₀, mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
    have hmapm : (g₀.map (algebraMap V Ω)).Monic := by
      rw [hmap]; exact monic_mul_leadingCoeff_inv hg0
    have hg₀m : g₀.Monic := monic_of_injective hinj hmapm
    have hdvd : g₀ ∣ q := by
      rw [← map_dvd_map (algebraMap V Ω) hinj hg₀m, hmap]
      refine dvd_trans (Dvd.intro (C g.leadingCoeff) ?_) hgd
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
    have hsep₀ : (g₀.map (residue V)).Separable :=
      hs.of_dvd (Polynomial.map_dvd _ hdvd)
    have hdeg : (g₀.map (residue V)).natDegree = g.natDegree := by
      rw [hg₀m.natDegree_map, ← natDegree_map_eq_of_injective hinj, hmap,
        natDegree_mul_C (inv_ne_zero hlc)]
    have hgdeg : g.natDegree ≠ 0 := fun h =>
      hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr ((degree_eq_iff_natDegree_eq hg0).mpr h))
    have hder₀ : derivative (g₀.map (residue V)) ≠ 0 := by
      intro h0
      have hu : IsUnit (g₀.map (residue V)) := by
        have := hsep₀
        rw [Polynomial.Separable, h0, isCoprime_zero_right] at this
        exact this
      exact hgdeg (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
    have hder : derivative g ≠ 0 := by
      intro h0
      apply hder₀
      have h1 : derivative (g₀.map (algebraMap V Ω)) = 0 := by
        rw [hmap, derivative_mul, derivative_C, h0]; simp
      rw [derivative_map] at h1 ⊢
      have h2 : derivative g₀ = 0 := by
        apply Polynomial.map_injective _ hinj
        rw [h1, Polynomial.map_zero]
      rw [h2, Polynomial.map_zero]
    exact IsSepClosed.degree_eq_one_of_irreducible Ω hg
      ((separable_iff_derivative_ne_zero hg).mpr hder)
  have hQ : (q.map (algebraMap V Ω)).Splits := by
    by_cases hq0 : q.map (algebraMap V Ω) = 0
    · simp [hq0]
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hq0
    rw [← hu]
    refine (Splits.multisetProd fun f hf ↦ ?_).mul u.isUnit.splits
    let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
    exact Splits.of_degree_eq_one (hdegree f h
      (UniqueFactorizationMonoid.dvd_of_mem_factors hf))
  have hroots : ∀ a ∈ (q.map (algebraMap V Ω)).roots, a ∈ (algebraMap V Ω).range := by
    intro a ha
    have hne : q.map (algebraMap V Ω) ≠ 0 := (hq.map _).ne_zero
    have hr : aeval a q = 0 := by
      rw [mem_roots hne, IsRoot, eval_map_algebraMap] at ha
      exact ha
    have hint : IsIntegral V a := ⟨q, hq, by rwa [← aeval_def]⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).mp hint
    exact ⟨y, hy⟩
  have hqs : q.Splits := Splits.of_splits_map_of_injective hinj hQ hroots
  exact ⟨q.roots, hqs.eq_prod_roots_of_monic hq⟩

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem linearIndepOn_pow_of_isDomain_tensor_purelyInseparable (k B : Type) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] (p : ℕ) (hp : p.Prime) (hk : CharP k p)
    (hdom : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K →
      IsPurelyInseparable k K → IsDomain (K ⊗[k] B))
    (s : Finset (FractionRing B)) (hs : LinearIndepOn k _root_.id (s : Set (FractionRing B))) :
    LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  classical
  haveI : ExpChar k p := ExpChar.prime hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B) s
  have hb : ∀ x : (s : Set (FractionRing B)), ∃ b : B,
      algebraMap B (FractionRing B) b = (d : B) • (x : FractionRing B) := fun x => hd x x.2
  choose b hb using hb
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hd0 : algebraMap B (FractionRing B) (d : B) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  let φ := IsScalarTower.toAlgHom k B (FractionRing B)
  have hφ : ∀ x, φ x = algebraMap B (FractionRing B) x := fun _ => rfl
  have hb' : ∀ x, φ (b x) = algebraMap B (FractionRing B) (d : B) * (x : FractionRing B) := by
    intro x; rw [hφ, hb, Algebra.smul_def]

  have hbli : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine Fintype.linearIndependent_iff.1 hs g ?_ i
    have h2 : φ (∑ j, g j • b j) = 0 := by rw [hg, map_zero]

    simp only [map_sum, map_smul, hb'] at h2
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (g j) _ _).symm, ← Finset.mul_sum] at h2
    exact (mul_eq_zero.1 h2).resolve_left hd0
  unfold LinearIndepOn
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcB : ∑ j, c j • b j ^ p = 0 := by
    apply hinj
    rw [map_zero, ← hφ]

    simp only [map_sum, map_smul, map_pow, hb', mul_pow]
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (c j) _ _).symm, ← Finset.mul_sum]
    simp only [] at hc
    rw [hc, mul_zero]

  have hroot : ∀ j, ∃ y : AlgebraicClosure k, y ^ p = algebraMap k (AlgebraicClosure k) (c j) :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose y hy using hroot
  let K := IntermediateField.adjoin k (Set.range y)
  haveI hfin : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  have hpi : IsPurelyInseparable k K := by
    refine (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p).2 ?_
    rintro z ⟨j, rfl⟩
    exact ⟨1, by rw [pow_one, hy]; exact ⟨c j, rfl⟩⟩
  haveI := hdom K hfin hpi
  haveI : CharP (K ⊗[k] B) p :=
    charP_of_injective_algebraMap (algebraMap k (K ⊗[k] B)).injective p
  haveI : ExpChar (K ⊗[k] B) p := ExpChar.prime hp
  let y' := fun j => (⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩ : K)
  have hy' : ∀ j, y' j ^ p = algebraMap k K (c j) := by
    intro j; apply Subtype.ext; simp [y', hy]
  have hz : (∑ j, y' j ⊗ₜ[k] b j) ^ p = 0 := by
    rw [sum_pow_char]
    simp only [Algebra.TensorProduct.tmul_pow, hy', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, hcB, TensorProduct.tmul_zero]
  have hz0 : ∑ j, y' j • ((1 : K) ⊗ₜ[k] b j) = 0 := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact pow_eq_zero_iff hp.ne_zero |>.1 hz
  have hli := Module.Flat.linearIndependent_one_tmul (S := K) hbli
  have hyi : y' i = 0 := Fintype.linearIndependent_iff.1 hli y' hz0 i
  have : algebraMap k (AlgebraicClosure k) (c i) = 0 := by
    rw [← hy]
    have : y i = 0 := congrArg Subtype.val hyi
    rw [this, zero_pow hp.ne_zero]
  exact (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).1 this

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

theorem not_separable_charpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C] [Algebra F C]
    [FiniteDimensional F C] (n : ℕ) (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    ((minpoly F y).natDegree < n ∨ ((minpoly F y).natDegree = n ∧ ¬ (minpoly F y).Separable)) →
      ¬ (ι y).charpoly.Separable := by
  intro F L C _ _ _ _ _ _ n ι y h hc
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hpm : (minpoly F y).Monic := minpoly.monic hyi
  have h1 : aeval (ι y) ((minpoly F y).map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : minpoly L (ι y) ∣ (minpoly F y).map (algebraMap F L) := minpoly.dvd L _ h1
  have h3 : (ι y).charpoly ∣ (minpoly L (ι y)) ^ Fintype.card (Fin n) :=
    charpoly_dvd_pow_of_aeval_eq_zero _ _ (minpoly.aeval L _)
  have h4 : (ι y).charpoly ∣ minpoly L (ι y) := hc.squarefree.isRadical _ _ h3
  have h5 := h4.trans h2
  have hmm : ((minpoly F y).map (algebraMap F L)).Monic := hpm.map _
  have hdc : (ι y).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdm : ((minpoly F y).map (algebraMap F L)).natDegree = (minpoly F y).natDegree := natDegree_map _
  rcases h with h | ⟨h, hns⟩
  · have := natDegree_le_of_dvd h5 hmm.ne_zero
    omega
  · have e := eq_of_monic_of_dvd_of_natDegree_le (Matrix.charpoly_monic _) hmm h5 (by omega)
    rw [← e] at hc
    exact hns ((separable_map (algebraMap F L)).mp hc)

end GlobalTheory.SepCharpoly
end

section

open Matrix Polynomial

namespace GlobalTheory

open Matrix Polynomial in
private theorem exists_eigenvector_of_isRoot_charpoly {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (r : L) (h : y.charpoly.IsRoot r) :
    ∃ v : Fin n → L, v ≠ 0 ∧ y *ᵥ v = r • v := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hv
  exact hv.symm

open Matrix Polynomial in
private theorem isUnit_of_eigenvector_columns_of_injective {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (μ : Fin n → L) (hμ : Function.Injective μ)
    (v : Fin n → Fin n → L) (hv0 : ∀ j, v j ≠ 0) (hv : ∀ j, y *ᵥ v j = μ j • v j) :
    IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact Module.End.eigenvectors_linearIndependent' (Matrix.toLin' y) μ hμ v
    (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv j), hv0 j⟩)

open Matrix Polynomial in
private theorem eq_diagonal_of_commute_diagonal_injective {L : Type} [Field L] {n : ℕ}
    (μ : Fin n → L) (hμ : Function.Injective μ) (m : Matrix (Fin n) (Fin n) L)
    (hm : m * diagonal μ = diagonal μ * m) : m = diagonal fun i => m i i := by
  ext i j
  have hij := congrFun (congrFun hm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    have hne : μ j - μ i ≠ 0 := sub_ne_zero.mpr fun e => h (hμ e).symm
    have : m i j * (μ j - μ i) = 0 := by rw [mul_sub, hij, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne

open Matrix Polynomial in
private theorem commute_of_commute_of_charpoly_separable_of_isAlgClosed {L : Type} [Field L]
    [IsAlgClosed L] {n : ℕ} (y a b : Matrix (Fin n) (Fin n) L) (hy : y.charpoly.Separable)
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  classical
  set s := y.charpoly.roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hy),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → L := fun i => (e i : L)
  have hμ : Function.Injective μ := fun i j hij => e.injective (Subtype.ext hij)
  have hroot : ∀ i, y.charpoly.IsRoot (μ i) := fun i => by
    have hmem : (μ i) ∈ s := (e i).2
    rw [hs_def, Multiset.mem_toFinset] at hmem
    exact (mem_roots hy.ne_zero).mp hmem
  choose v hv0 hv using fun i => exists_eigenvector_of_isRoot_charpoly y (μ i) (hroot i)
  set P : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v j i with hP
  have hPu : IsUnit P := isUnit_of_eigenvector_columns_of_injective y μ hμ v hv0 hv
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Q := P⁻¹ with hQ
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ' : ∀ X : Matrix (Fin n) (Fin n) L, P * (Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hQP' : ∀ X : Matrix (Fin n) (Fin n) L, Q * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hyP : y * P = P * diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (hv j) i
    simpa [hP, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hD : Q * y * P = diagonal μ := by
    rw [Matrix.mul_assoc, hyP, hQP']
  have hcomm : ∀ m : Matrix (Fin n) (Fin n) L, m * y = y * m →
      (Q * m * P) * diagonal μ = diagonal μ * (Q * m * P) := fun m hm => by
    rw [← hD]
    simp only [Matrix.mul_assoc, hPQ']
    rw [← Matrix.mul_assoc m y P, hm, Matrix.mul_assoc]
  have hA := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm a ha)
  have hB := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm b hb)
  have hAB : (Q * a * P) * (Q * b * P) = (Q * b * P) * (Q * a * P) := by
    rw [hA, hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have key : ∀ c d : Matrix (Fin n) (Fin n) L, c * d = P * ((Q * c * P) * (Q * d * P)) * Q :=
    fun c d => by
      simp only [Matrix.mul_assoc, hPQ', hPQ, Matrix.mul_one]
  rw [key a b, key b a, hAB]


open Matrix Polynomial in
theorem _root_.GlobalTheory.commute_of_commute_separable_charpoly :
    ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable →
      a * y = y * a → b * y = y * b → a * b = b * a := by
  intro K _ n y a b hy ha hb
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hyL : (y.map f).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hy.map
  have haL : a.map f * y.map f = y.map f * a.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ha]
  have hbL : b.map f * y.map f = y.map f * b.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hb]
  have h := commute_of_commute_of_charpoly_separable_of_isAlgClosed _ _ _ hyL haL hbL
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h
  exact Matrix.map_injective f.injective h

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory.AbhyankarRootUnit

open scoped TensorProduct

theorem root_not_isUnit (S : Type) [CommRing S] [IsLocalRing S] (π : S)
    (hπ : π ∈ maximalIdeal S) (e : ℕ) (he : 0 < e) :
    ¬ IsUnit (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) := by
  intro hu
  have hev : (Polynomial.X ^ e - Polynomial.C π : Polynomial S).eval₂
      (algebraMap S (ResidueField S)) 0 = 0 := by
    simp [Polynomial.eval₂_sub, zero_pow he.ne']
    exact hπ
  have := hu.map (AdjoinRoot.lift (algebraMap S (ResidueField S)) 0 hev)
  rw [AdjoinRoot.lift_root] at this
  exact not_isUnit_zero this

theorem root_pow (S : Type) [CommRing S] (π : S) (e : ℕ) :
    AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
      algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h]; rfl

theorem mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow (S L : Type) [CommRing S] [Field L]
    [Algebra S L] (π : S) (hπL : algebraMap S L π ≠ 0) (e : ℕ) (he : 0 < e) (D : Type)
    [CommRing D] [IsLocalRing D] [Algebra S D] (t : D) (ht : t ^ e = algebraMap S D π)
    (htu : ¬ IsUnit t) (Q : Ideal (integralClosure D (D ⊗[S] L))) [Q.IsMaximal] :
    algebraMap D (Localization.AtPrime Q) t ∈ maximalIdeal (Localization.AtPrime Q) ∧
      algebraMap D (Localization.AtPrime Q) t ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  have htDm : t ∈ maximalIdeal D := htu
  haveI hQmax : (Q.comap (algebraMap D (integralClosure D (D ⊗[S] L)))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) Q
  have hcomap : Q.comap (algebraMap D (integralClosure D (D ⊗[S] L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal hQmax
  have htQ : algebraMap D (integralClosure D (D ⊗[S] L)) t ∈ Q := by
    rw [← Ideal.mem_comap, hcomap]; exact htDm
  have hsc : algebraMap D (Localization.AtPrime Q) t =
      algebraMap (integralClosure D (D ⊗[S] L)) (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (D ⊗[S] L)) t) :=
    IsScalarTower.algebraMap_apply D (integralClosure D (D ⊗[S] L)) _ t
  refine ⟨?_, ?_⟩
  · rw [hsc, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    exact htQ
  · rw [hsc]
    apply IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
    have hpow : (algebraMap D (D ⊗[S] L) t) ^ e =
        Algebra.TensorProduct.includeRight (algebraMap S L π) := by
      rw [← map_pow, ht, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.algebraMap_eq_smul_one π, Algebra.algebraMap_eq_smul_one π,
        TensorProduct.smul_tmul]
    have hunit : IsUnit (algebraMap D (D ⊗[S] L) t) := by
      rw [← isUnit_pow_iff he.ne', hpow]
      exact (Ne.isUnit hπL).map _
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_right_eq_zero.1 h1
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_left_eq_zero.1 h1

theorem root_mem_maximalIdeal_and_mem_nonZeroDivisors : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal], algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧ algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ hπ he _ _ Q _
  have hπm : π ∈ maximalIdeal S := hπ.not_isUnit
  have hπL : algebraMap S L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S K L]
    intro h0
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h0
    exact hπ.ne_zero h0
  refine mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow S L π hπL e he D _ ?_ ?_ Q
  · rw [← map_pow, root_pow, AlgEquiv.commutes]
  · intro h
    exact root_not_isUnit S π hπm e he (by simpa using h.map ψ)

end GlobalTheory.AbhyankarRootUnit
end
