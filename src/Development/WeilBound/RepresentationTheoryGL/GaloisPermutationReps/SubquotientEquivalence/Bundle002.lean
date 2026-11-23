module

public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace PairingFactorsThroughPeriods

theorem exactPer_per {q n : ℕ} {z : ℂ} (h : ExactPer q n z) : z ^ q ^ n = z := by
  unfold ExactPer at h
  exact h.2.1

theorem per_mul {q n : ℕ} {z : ℂ} (h : z ^ q ^ n = z) (k : ℕ) : z ^ q ^ (n * k) = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem per_inj {q n : ℕ} {z : ℂ} (hz : ExactPer q n z) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : z ^ q ^ a = z ^ q ^ b) : a = b := by
  have key : ∀ a b : ℕ, a < b → b < n → z ^ q ^ a = z ^ q ^ b → False := by
    intro a b hab hbn h
    apply hz.2.2 (b - a) (by omega) (by omega)
    have h1 : (z ^ q ^ a) ^ q ^ (n - a) = (z ^ q ^ b) ^ q ^ (n - a) := by rw [h]
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega : a ≤ n),
      hz.2.1] at h1
    have h2 : b + (n - a) = n + (b - a) := by omega
    rw [h2, pow_add, pow_mul, hz.2.1] at h1
    exact h1.symm
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hb h).elim
  · exact hab
  · exact (key b a hab ha h.symm).elim

theorem pow_apply_eig {V : Type} [AddCommGroup V] [Module ℂ V] (M : Module.End ℂ V) {v : V} {c : ℂ}
    (hv : M v = c • v) (k : ℕ) : (M ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' M k, Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ c k]

theorem eig_G {V : Type} [AddCommGroup V] [Module ℂ V] {q : ℕ} (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) {v : V} {c : ℂ} (hv : M v = c • v) (k : ℕ) :
    M ((G ^ k) v) = c ^ q ^ k • (G ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have h1 : M (G ((G ^ k) v)) = G ((M ^ q) ((G ^ k) v)) := by
      rw [← Module.End.mul_apply M G, hMG, Module.End.mul_apply]
    rw [pow_succ' G k, Module.End.mul_apply, h1, pow_apply_eig M ih q, map_smul, ← pow_mul,
      ← pow_succ]

theorem basis_side {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q m : ℕ} (M G : Module.End ℂ V) (hG : IsUnit G) (hMG : M * G = G * M ^ q) {z : ℂ}
    (hz : ExactPer q (m + 1) z) (hr : Module.finrank ℂ V = m + 1) {v : V} (hv0 : v ≠ 0)
    (hv : M v = z • v) :
    ∃ b : Module.Basis (Fin (m + 1)) ℂ V, (∀ j : Fin (m + 1), M (b j) = z ^ q ^ (j : ℕ) • b j) ∧
      (∀ k : Fin m, G (b k.castSucc) = b k.succ) ∧
      ∃ μ : ℂ, μ ≠ 0 ∧ G (b (Fin.last m)) = μ • b 0 := by
  have hGinj : ∀ k : ℕ, Function.Injective (G ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG.pow k)).injective
  obtain ⟨f, hf⟩ : ∃ f : Fin (m + 1) → V, ∀ j, f j = (G ^ (j : ℕ)) v := ⟨_, fun _ => rfl⟩
  have hMf : ∀ j : Fin (m + 1), M (f j) = z ^ q ^ (j : ℕ) • f j := fun j => by
    rw [hf]; exact eig_G M G hMG hv j
  have hfne : ∀ j, f j ≠ 0 := fun j h =>
    hv0 (hGinj (j : ℕ) (by rw [map_zero, ← hf]; exact h))
  have hinj : Function.Injective (fun j : Fin (m + 1) => z ^ q ^ (j : ℕ)) :=
    fun a b h => Fin.ext (per_inj hz a.2 b.2 h)
  have hli : LinearIndependent ℂ f :=
    Module.End.eigenvectors_linearIndependent' M _ hinj f
      (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hMf j), hfne j⟩)
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℂ V, ∀ j, b j = f j :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hr]),
      fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) j⟩
  refine ⟨b, fun j => by rw [hb]; exact hMf j, fun k => ?_, ?_⟩
  · rw [hb, hb, hf, hf, Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply]
  · obtain ⟨x, hxdef⟩ : ∃ x, x = G (b (Fin.last m)) := ⟨_, rfl⟩
    have hxG : x = (G ^ (m + 1)) v := by
      rw [hxdef, hb, hf, Fin.val_last, pow_succ', Module.End.mul_apply]
    have hx : M x = z • x := by
      rw [hxG, eig_G M G hMG hv, hz.2.1]
    obtain ⟨c, hcdef⟩ : ∃ c, c = b.repr x := ⟨_, rfl⟩
    have hsum : x = ∑ j, c j • b j := by rw [hcdef]; exact (b.sum_repr x).symm
    have hcoef : ∀ j, c j * z ^ q ^ (j : ℕ) = z * c j := by
      intro j
      have e1 : M x = ∑ j, (c j * z ^ q ^ (j : ℕ)) • b j := by
        conv_lhs => rw [hsum]

        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul, hb j, hMf j, smul_smul]
      have e2 : z • x = ∑ j, (z * c j) • b j := by
        conv_lhs => rw [hsum]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul]
      have e3 : (∑ j, (c j * z ^ q ^ (j : ℕ)) • b j) = ∑ j, (z * c j) • b j :=
        e1.symm.trans (hx.trans e2)
      have e4 := congrArg (fun y => b.repr y j) e3
      simp only [Module.Basis.repr_sum_self] at e4
      exact e4
    have hc0 : ∀ j : Fin (m + 1), j ≠ 0 → c j = 0 := by
      intro j hj
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
      have hne : z ^ q ^ (j : ℕ) ≠ z := hz.2.2 j hjpos j.2
      have h2 : c j * (z ^ q ^ (j : ℕ) - z) = 0 := by
        rw [mul_sub, hcoef j]
        ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    have hx0 : x = c 0 • b 0 := by
      conv_lhs => rw [hsum]
      rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hc0 j hj, zero_smul]) (by simp)]
    refine ⟨c 0, fun h => ?_, ?_⟩
    · have hx00 : G (b (Fin.last m)) = 0 := by rw [← hxdef, hx0, h, zero_smul]
      exact b.ne_zero (Fin.last m)
        (((Module.End.isUnit_iff _).mp hG).injective (by rw [map_zero]; exact hx00))
    · rw [← hxdef]
      exact hx0

end PairingFactorsThroughPeriods

open PairingFactorsThroughPeriods in
theorem st1b : St1b := by
  unfold St1b
  intro V V' _ _ _ _ _ _ q n i M G M' G' z hn hr hr' hG hG' hMG hMG' hz hzM hzM' hdet
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨v, hv⟩ := hzM.exists_hasEigenvector
  obtain ⟨v1, hv1⟩ := hzM'.exists_hasEigenvector
  have hG'inj : ∀ k : ℕ, Function.Injective (G' ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG'.pow k)).injective
  have hv1' : M' v1 = z ^ q ^ i • v1 := Module.End.mem_eigenspace_iff.mp hv1.1
  have hle : i ≤ (m + 1) * i := by
    rw [add_mul, one_mul]
    exact Nat.le_add_left i (m * i)
  have hw : M' ((G' ^ ((m + 1) * i - i)) v1) = z • (G' ^ ((m + 1) * i - i)) v1 := by
    rw [eig_G M' G' hMG' hv1', ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle,
      per_mul (exactPer_per hz)]
  obtain ⟨b, hbM, hbG, μ, hμ, hbl⟩ :=
    basis_side M G hG hMG hz hr hv.2 (Module.End.mem_eigenspace_iff.mp hv.1)
  obtain ⟨b', hbM', hbG', μ', hμ', hbl'⟩ :=
    basis_side M' G' hG' hMG' hz hr'
      (fun h => hv1.2 (hG'inj _ (by rw [map_zero]; exact h))) hw
  obtain ⟨T, hT⟩ : ∃ T : V ≃ₗ[ℂ] V', ∀ j, T (b j) = b' j :=
    ⟨b.equiv b' (Equiv.refl _), fun j => by simp⟩
  have hTs : ∀ j, T.symm (b' j) = b j := fun j => by rw [← hT j, LinearEquiv.symm_apply_apply]
  obtain ⟨G'', hG''⟩ : ∃ G'' : Module.End ℂ V,
      G'' = T.symm.toLinearMap ∘ₗ G' ∘ₗ T.toLinearMap := ⟨_, rfl⟩
  have hdet'' : LinearMap.det G'' = LinearMap.det G' := by
    rw [hG'']
    have h := LinearMap.det_conj G' T.symm
    simpa using h
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1) → ℂ, d = fun j => if j = Fin.last m then μ / μ' else 1 :=
    ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Module.End ℂ V, D = Matrix.toLin b b (Matrix.diagonal d) := ⟨_, rfl⟩
  have hD : ∀ j, D (b j) = d j • b j := fun j => by
    rw [hDdef, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hGD : G = G'' ∘ₗ D := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hD j, map_smul, hG'']
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have h1 : d k.castSucc = 1 := by
        rw [hd]
        simp [Fin.castSucc_lt_last k |>.ne]
      rw [h1, one_smul]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbG', hTs, hbG]
    · have h1 : d (Fin.last m) = μ / μ' := by rw [hd]; simp
      rw [h1]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbl', map_smul, hTs, smul_smul, div_mul_cancel₀ μ hμ', hbl]
  have hdetD : LinearMap.det D = μ / μ' := by
    rw [hDdef, LinearMap.det_toLin, Matrix.det_diagonal, hd]
    simp
  have hμμ : μ = μ' := by
    have h1 : LinearMap.det G = LinearMap.det G' * (μ / μ') := by
      rw [hGD, LinearMap.det_comp, hdet'', hdetD]
    have hne : LinearMap.det G' ≠ 0 := (hG'.map LinearMap.det).ne_zero
    rw [hdet] at h1
    have h2 : μ / μ' = 1 := mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)
    exact (div_eq_one_iff_eq hμ').mp h2
  refine ⟨T, fun v => ?_, fun v => ?_⟩
  · have h : T.toLinearMap ∘ₗ M = M' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hbM, map_smul, hT, hbM']
    exact LinearMap.congr_fun h v
  · have h : T.toLinearMap ∘ₗ G = G' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · rw [hbG, hT, hT, hbG']
      · rw [hbl, map_smul, hT, hT, hbl', hμμ]
    exact LinearMap.congr_fun h v

end PositivityTheory.Rg.DzCount

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace LeviInductionForms

theorem pow_eq_pow_iff_mod {M : Type*} [CommMonoid M] {ζ : M} {N : ℕ} (h : IsPrimitiveRoot ζ N)
    (hN : 0 < N) (a b : ℕ) : ζ ^ a = ζ ^ b ↔ a % N = b % N := by
  have e : ∀ c, ζ ^ c = ζ ^ (c % N) := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c N]
    rw [pow_add, pow_mul, h.pow_eq_one, one_pow, mul_one]
  rw [e a, e b]
  exact ⟨fun H => h.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) H, fun H => by rw [H]⟩

theorem natDegree_minpoly_eq {K F : Type*} [Field K] [Finite K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w) : (minpoly K w).natDegree = n := by
  have hirr := minpoly.irreducible hw
  have hdvd : minpoly K w ∣ (X ^ (Nat.card K) ^ n - X : K[X]) := by
    apply minpoly.dvd
    simp [h1]
  have hd : (minpoly K w).natDegree ∣ n := hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  have hpos : 0 < (minpoly K w).natDegree := minpoly.natDegree_pos hw
  have hself : w ^ (Nat.card K) ^ (minpoly K w).natDegree = w := by
    obtain ⟨r, hr⟩ := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).1 (dvd_refl _)
    have h3 : Polynomial.aeval w (X ^ (Nat.card K) ^ (minpoly K w).natDegree - X : K[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h3
  by_contra hne
  exact h2 _ hpos (lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne) hself

theorem exists_eq_pow_of_aeval {K F : Type*} [Field K] [Fintype K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w w' : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w)
    (hP : Polynomial.aeval w' (minpoly K w) = 0) : ∃ i : ℕ, w' = w ^ (Nat.card K) ^ i := by
  classical
  have hq : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hφ : ∀ (i : ℕ) (x : F), (FiniteField.frobeniusAlgHom K F ^ i) x = x ^ (Nat.card K) ^ i := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, AlgHom.mul_apply, ih]
      show (x ^ Fintype.card K) ^ (Nat.card K) ^ i = _
      rw [hq, ← pow_mul, ← pow_succ']
  have hroot : ∀ i : ℕ, Polynomial.aeval (w ^ (Nat.card K) ^ i) (minpoly K w) = 0 := by
    intro i
    rw [← hφ, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hpw : ∀ a b : ℕ, (w ^ (Nat.card K) ^ a) ^ (Nat.card K) ^ b = w ^ (Nat.card K) ^ (a + b) := by
    intro a b
    rw [← pow_mul, ← pow_add]
  have hlt : ∀ i j : ℕ, i < j → j < n → w ^ (Nat.card K) ^ i ≠ w ^ (Nat.card K) ^ j := by
    intro i j hij hjn H
    have H2 := congrArg (fun x : F => x ^ (Nat.card K) ^ (n - j)) H
    simp only [hpw] at H2
    have e : j + (n - j) = n := by omega
    rw [e, h1] at H2
    exact h2 (i + (n - j)) (by omega) (by omega) H2
  have hinj : Set.InjOn (fun i : ℕ => w ^ (Nat.card K) ^ i) (Finset.range n : Set ℕ) := by
    intro i hi j hj H
    simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd H (hlt i j h hj)
    · exact h
    · exact absurd H.symm (hlt j i h hi)
  by_contra hno
  push_neg at hno
  set S := (Finset.range n).image (fun i : ℕ => w ^ (Nat.card K) ^ i) with hS
  have hcardS : S.card = n := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hw'S : w' ∉ S := by
    rw [hS, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hno i hi.symm
  have hP0 : minpoly K w ≠ 0 := minpoly.ne_zero hw
  have hmap0 : (minpoly K w).map (algebraMap K F) ≠ 0 := Polynomial.map_ne_zero hP0
  have hsub : (insert w' S).val ⊆ ((minpoly K w).map (algebraMap K F)).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_insert] at hx
    rw [Polynomial.mem_roots hmap0, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    rcases hx with rfl | hx
    · exact hP
    · rw [hS, Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hroot i
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem hw'S, hcardS, Polynomial.natDegree_map,
    natDegree_minpoly_eq n hn w hw h1 h2] at hcard
  omega

end LeviInductionForms

open LeviInductionForms in
theorem st3a : St3a := by
  unfold St3a
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqn : 1 < Nat.card K ^ n := Nat.one_lt_pow hn.ne' hq1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.card K ^ n - 1 := ⟨_, rfl⟩
  have hNq : Nat.card K ^ n = N + 1 := by omega
  have hNpos : 0 < N := by omega
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨by
    have hc : ((Nat.card K : ℕ) : K) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K
    have h4 : ((Nat.card K ^ n : ℕ) : K) = (N : K) + 1 := by
      rw [hNq, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_pow, hc, zero_pow hn.ne'] at h4
    intro h0
    rw [h0, zero_add] at h4
    exact zero_ne_one h4⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hNpos.ne'⟩
  have htr : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ ω ^ a = ω ^ b := by
    intro a b
    rw [pow_eq_pow_iff_mod hζ hNpos, pow_eq_pow_iff_mod hω hNpos]
  let jOf : ℂ → ℕ := fun z => if h : ∃ j : ℕ, ζ ^ j = z then h.choose else 0
  have hj : ∀ z : ℂ, ExactPer (Nat.card K) n z → ζ ^ jOf z = z := by
    intro z hz
    unfold ExactPer at hz
    obtain ⟨hz0, hz1, -⟩ := hz
    have hzN : z ^ N = 1 := by
      rw [hNq, pow_succ'] at hz1
      exact mul_right_injective₀ hz0 (hz1.trans (mul_one z).symm)
    have hex : ∃ j : ℕ, ζ ^ j = z := by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hzN
      exact ⟨i, hi⟩
    simp only [jOf, dif_pos hex]
    exact hex.choose_spec
  have hint : ∀ x : AlgebraicClosure K, IsIntegral K x := fun x => Algebra.IsIntegral.isIntegral x
  have hper : ∀ (j m : ℕ), (ζ ^ j) ^ (Nat.card K) ^ m = ζ ^ j ↔
      (ω ^ j) ^ (Nat.card K) ^ m = ω ^ j := by
    intro j m
    rw [← pow_mul, ← pow_mul]
    exact htr _ _
  have hω0 : ω ≠ 0 := hω.ne_zero hNpos.ne'
  refine ⟨fun z => minpoly K (ω ^ jOf z), ?_, ?_⟩
  · intro z hz
    have hzj := hj z hz
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    show (minpoly K (ω ^ jOf z)).Monic ∧ Irreducible (minpoly K (ω ^ jOf z)) ∧
      minpoly K (ω ^ jOf z) ≠ X ∧ (minpoly K (ω ^ jOf z)).natDegree = n
    refine ⟨minpoly.monic hw, minpoly.irreducible hw, ?_, natDegree_minpoly_eq n hn _ hw hw1 hw2⟩
    intro hX
    have h0 := minpoly.aeval K (ω ^ jOf z)
    rw [hX, Polynomial.aeval_X] at h0
    exact pow_ne_zero _ hω0 h0
  · intro z z' hz hz' hlab
    have hzj := hj z hz
    have hzj' := hj z' hz'
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    have hP : Polynomial.aeval (ω ^ jOf z') (minpoly K (ω ^ jOf z)) = 0 := by
      have hlab' : minpoly K (ω ^ jOf z) = minpoly K (ω ^ jOf z') := hlab
      rw [hlab']
      exact minpoly.aeval K _
    obtain ⟨i, hi⟩ := exists_eq_pow_of_aeval n hn _ _ hw hw1 hw2 hP
    refine ⟨i, ?_⟩
    rw [← hzj', ← hzj, ← pow_mul, htr, pow_mul]
    exact hi

end PositivityTheory.Rg.DzCount

end
end
