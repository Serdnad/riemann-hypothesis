module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle006
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

namespace Formalism.L2.Pj

open IsLocalRing

theorem complSt_holds : ComplSt := by
  intro W _ _ _ _
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hl : IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) := inferInstance
  exact ⟨⟨AdicCompletion (maximalIdeal W) W⟩, algebraMap W (AdicCompletion (maximalIdeal W) W), hl, ϖ, hϖ,
    GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hϖ⟩

end Formalism.L2.Pj
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {k : Type} [CommRing k] {d n : ℕ}

theorem div_Lin_add (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f + g) = Lin b v f + Lin b v g := by
  simp only [Lin, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem div_Lin_mul (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f * g) = Lin b v f * g + f * Lin b v g := by
  simp only [Lin, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem div_Lin_C (b : Fin n) (v : Fin d → k) (c : k) : Lin b v (C c : PS k n d) = 0 := by
  simp [Lin, MvPowerSeries.pderiv_C]

theorem Lin_linForm (b b' : Fin n) (v w : Fin d → k) :
    Lin b v (∑ j : Fin d, C (w j) * (X (b', j) : PS k n d)) =
      C (if b = b' then ∑ j : Fin d, v j * w j else 0) := by
  unfold Lin
  by_cases h : b = b'
  · subst h

    simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Finset.mul_sum,
    map_sum, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Pi.single_apply,
      Prod.ext_iff, h]

theorem div_Lin_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (Q : MvPolynomial ι k) :
    Lin (cp l) (u l) (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ (MvPolynomial.pderiv l Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, MvPowerSeries.algebraMap_apply]
    simpa using div_Lin_C (cp l) (u l) a
  | add p q hp hq => rw [map_add (f := _), div_Lin_add, hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p i hp =>
    rw [map_mul, div_Lin_mul, hp, MvPolynomial.aeval_X, hl, Derivation.leibniz, MvPolynomial.pderiv_X]
    by_cases h : l = i
    · subst h
      simp
      ring
    · simp [h, Pi.single_apply]
      ring

theorem div_Lin_iter_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, div_Lin_aeval cp u φ l hl]

theorem div_LinMon_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) (Q : MvPolynomial ι k) :
    LinMon cp u a (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ
      ((Finset.univ : Finset ι).toList.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) Q) := by
  unfold LinMon
  generalize (Finset.univ : Finset ι).toList = L
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases h0 : a l = 0
    · rw [h0]
      rfl
    · exact div_Lin_iter_aeval cp u φ l (hdual l (ha l h0)) (a l) _

theorem div_constCoeff_aeval {ι : Type} (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (Q : MvPolynomial ι k) : constantCoeff (MvPolynomial.aeval φ Q) = MvPolynomial.constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPowerSeries.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp [hp, hφ0]

theorem div_iter_pderiv_monomial {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : s - Finsupp.single i t - Finsupp.single i 1 = s - Finsupp.single i (t + 1) := by
      ext j
      first
        | (simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp [Finsupp.single_apply]; split_ifs <;> omega)
    have h2 : (s - Finsupp.single i t) i = s i - t := by
      first
        | simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        | simp
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial, h1, h2,
      Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

theorem div_listSum_apply_of_notMem {ι : Type} (a : ι →₀ ℕ) (L : List ι) (l : ι) (hl : l ∉ L) :
    (L.map fun l' => Finsupp.single l' (a l')).sum l = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.mem_cons, not_or] at hl
    simp [Finsupp.single_apply, Ne.symm hl.1, ih hl.2]

theorem div_fold_monomial {ι : Type} [DecidableEq ι] (a : ι →₀ ℕ) (L : List ι) (hL : L.Nodup) (s : ι →₀ ℕ)
    (c : k) :
    L.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (L.map fun l => Finsupp.single l (a l)).sum)
        (c * (L.map fun l => ((s l).descFactorial (a l) : k)).prod) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, ih hL.2, div_iter_pderiv_monomial]
    have hx : (s - (L.map fun l => Finsupp.single l (a l)).sum) x = s x := by
      rw [Finsupp.tsub_apply, div_listSum_apply_of_notMem a L x hL.1, Nat.sub_zero]
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hx]
    congr 1
    · rw [tsub_tsub, add_comm]
    · ring

theorem linMon_aeval_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a α : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) :
    constantCoeff (LinMon cp u a (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k)))) =
      if a = α then ((α.prod fun _ e => e.factorial : ℕ) : k) else 0 := by
  classical
  rw [div_LinMon_aeval cp u φ Good hdual a ha, div_fold_monomial a _ (Finset.nodup_toList _),
    div_constCoeff_aeval φ hφ0, MvPolynomial.constantCoeff_monomial]
  have hLs : ∀ (M : Type) [AddCommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).sum = ∑ l, f l := fun M _ f => by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hLp : ∀ (M : Type) [CommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).prod = ∏ l, f l := fun M _ f => by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hS : ((Finset.univ : Finset ι).toList.map fun l => Finsupp.single l (a l)).sum = a := by
    rw [hLs]
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hP : ((Finset.univ : Finset ι).toList.map fun l => ((α l).descFactorial (a l) : k)).prod =
      ∏ l, ((α l).descFactorial (a l) : k) := hLp k _
  rw [hS, hP, one_mul]
  by_cases hEq : a = α
  · subst hEq
    rw [tsub_self, if_pos rfl, if_pos rfl, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
    push_cast
    exact Finset.prod_congr rfl fun l _ => by rw [Nat.descFactorial_self]
  · rw [if_neg hEq]
    split_ifs with h0
    · have hle : α ≤ a := tsub_eq_zero_iff_le.mp h0
      obtain ⟨l, hl⟩ : ∃ l, α l < a l := by
        by_contra hcon
        push_neg at hcon
        exact hEq (le_antisymm (Finsupp.le_def.mpr hcon) hle)
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr hl, Nat.cast_zero])
    · rfl

end Formalism.L2.Pj.Crude
end
end

section

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate

namespace Formalism.L2.Pj.FJ

section Core

variable {r ρ : ℕ}

def cM {m n : Type} (A : Matrix m n ℂ) : Matrix m n ℂ := A.map (starRingEnd ℂ)

theorem cM_cM {m n : Type} (A : Matrix m n ℂ) : cM (cM A) = A := by
  ext i j
  simp [cM]

theorem cM_mul {m n o : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    cM (A * B) = cM A * cM B := by
  simp only [cM]
  exact Matrix.map_mul

theorem cM_transpose {m n : Type} (A : Matrix m n ℂ) : cM Aᵀ = (cM A)ᵀ := by
  simp only [cM]
  exact Matrix.transpose_map

theorem cM_add {m n : Type} (A B : Matrix m n ℂ) : cM (A + B) = cM A + cM B := by
  ext i j
  simp [cM]

theorem cM_one : cM (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cM]
  · simp [cM, Matrix.one_apply, h]

theorem unitary_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hg : (cM g)ᵀ = g) (hiso : Fᵀ * g * cM F = 0)
    (hsk : cM β = -βᵀ) :
    (1 + F * β * (g * cM F)ᵀ)ᵀ * g * cM (1 + F * β * (g * cM F)ᵀ) = g := by
  have hg' : cM g = gᵀ := by
    have := congrArg Matrix.transpose hg
    simpa using this
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, Fᵀ * (g * (cM F * X)) = 0 := by
    intro X
    rw [← Matrix.mul_assoc g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    cM_add, cM_one, cM_mul, cM_transpose, cM_cM, hg', hsk]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul, key, neg_zero, Matrix.mul_zero, add_zero, neg_neg]
  abel

theorem det_ne_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hiso : Fᵀ * g * cM F = 0) :
    (1 + F * β * (g * cM F)ᵀ).det ≠ 0 := by
  have hT : (g * cM F)ᵀ * F = 0 := by
    have := congrArg Matrix.transpose hiso
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  generalize (g * cM F)ᵀ = H at hT ⊢
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, H * (F * X) = 0 := by
    intro X
    rw [← Matrix.mul_assoc, hT, Matrix.zero_mul]
  have hinv : (1 + F * β * H) * (1 - F * β * H) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc, key, Matrix.mul_zero, sub_zero]
    first | abel | skip
  intro h0
  have := congrArg Matrix.det hinv
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Core

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by unfold cc; exact NumberField.IsCMField.complexEmbedding_complexConj E τ x

def Fm (τ : E →+* ℂ) (e : Fin ρ → Fin r → E) : Matrix (Fin r) (Fin ρ) ℂ :=
  Matrix.of fun k a => τ (e a k)

theorem zMatC_eq (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X e τ β = 1 + Fm τ e * β * (X.Gm.map τ * cM (Fm τ e))ᵀ := by
  unfold zMatC
  ext k l
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fm, cM,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gram_eq (X : Data E r) (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm A = Aᵀ * X.Gm.map τ * cM A := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cM, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem herm_g (X : Data E r) (τ : E →+* ℂ) : (cM (X.Gm.map τ))ᵀ = X.Gm.map τ := by
  ext i j
  simp only [Matrix.transpose_apply, cM, Matrix.map_apply]
  rw [← emb_cc', X.4 j i]

theorem iso_F (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ) :
    (Fm τ cu.e)ᵀ * X.Gm.map τ * cM (Fm τ cu.e) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fm, cM, Matrix.of_apply, Matrix.map_apply,
    Matrix.zero_apply, Finset.sum_mul]
  have h := congrArg τ (cu.3 a b)
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h

  simp only [map_sum, map_mul, map_zero, emb_cc'] at h
  rw [Finset.sum_comm]
  exact h

theorem skew_beta (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k)) (τ : E →+* ℂ)
    (t : Fin (nZ X ρ) → ℝ) :
    cM (∑ k, (t k : ℂ) • (zBas X cu k).map τ) = -(∑ k, (t k : ℂ) • (zBas X cu k).map τ)ᵀ := by
  have h' := hb
  unfold IsSkew at h'
  ext a b

  simp only [cM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
  smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, ← emb_cc', h', map_neg, mul_neg, Finset.sum_neg_distrib]

theorem zBas_skew (X : Data E r) (cu : CuspFD X ρ) (h : ∃ bs, IsZBasis X cu bs) (k : Fin (nZ X ρ)) :
    IsSkew (zBas X cu k) := by
  have hs : LinearIndependent ℤ (zBas X cu) ∧
      ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range (zBas X cu)) := Classical.epsilon_spec h
  have hm : zBas X cu k ∈ zGam X cu := (hs.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
  exact hm.1

theorem zAct_mem_dom (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k))
    (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : zAct X cu t x ∈ X.dom := by
  unfold zAct ReciprocityTheory.ChartRestriction.G.FD.Data.dom at *
  unfold GG at *
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  unfold dmin mat at *
  beta_reduce
  set M := zMatC X cu.e (τ : E →+* ℂ) (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map (τ : E →+* ℂ)) with hMdef
  have hU : Mᵀ * X.Gm.map (τ : E →+* ℂ) * cM M = X.Gm.map (τ : E →+* ℂ) := by
    rw [hMdef, zMatC_eq]
    exact unitary_core _ _ _ (herm_g X _) (iso_F X cu _) (skew_beta X cu hb _ t)
  have hD : M.det ≠ 0 := by
    rw [hMdef, zMatC_eq]
    exact det_ne_core _ _ _ (iso_F X cu _)
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Mᵀ * (X.Gm.map (τ : E →+* ℂ) * (cM M * Y)) = X.Gm.map (τ : E →+* ℂ) * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  have hG : ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (M * of (x τ)) =
      ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (of (x τ)) := by
    simp only [gram_eq, Matrix.transpose_mul, cM_mul, Matrix.mul_assoc, hU']
  refine ⟨?_, fun i => ?_⟩
  · show (M * of (x τ)).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hD hdet
  · have := hpos i
    rw [← hG] at this
    exact this

theorem orbDom_of_latZ {Comp : Type} (X : Comp → Data E r) (h : LatZ X ρ) : OrbDom X ρ := by
  intro cu t x hx
  exact zAct_mem_dom (X cu.1) cu.2 (fun k => zBas_skew _ _ (h cu) k) t x hx

theorem rdOrbInt_of_latZ {Comp K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C]
    [Module K C] (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (h : LatZ X ρ) : RdOrbInt σ X ρ rd :=
  rdOrbInt_of σ X rd hc (orbDom_of_latZ X h)

end FD

end Formalism.L2.Pj.FJ
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} (A : Over X)

def powO : ℕ → Over X
  | 0 => 𝟙_ (Over X)
  | k + 1 => A ⊗ powO k

def prj : (k : ℕ) → Fin k → (powO A k ⟶ A)
  | 0, j => j.elim0
  | k + 1, j => Fin.cases (fst A (powO A k)) (fun j' => snd A (powO A k) ≫ prj k j') j

def tup {T : Over X} : (k : ℕ) → (Fin k → (T ⟶ A)) → (T ⟶ powO A k)
  | 0, _ => toUnit T
  | k + 1, a => lift (a 0) (tup k fun j => a j.succ)

variable [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O] (act : OAct O A)

def matMap {k : ℕ} (e : Fin k → Fin k → O) : powO A k ⟶ powO A k :=
  tup A k fun i => psum A (fun j => prj A k j ≫ act.act (e i j)) Finset.univ

abbrev tensSch {k : ℕ} (e : Fin k → Fin k → O) : Scheme.{0} :=
  pullback (lift (matMap A act e) (𝟙 (powO A k))).left (lift (𝟙 (powO A k)) (𝟙 (powO A k))).left

def tensO {k : ℕ} (e : Fin k → Fin k → O) : Over X :=
  Over.mk (pullback.fst _ _ ≫ (powO A k).hom : tensSch A act e ⟶ X)

def tensIncl {k : ℕ} (e : Fin k → Fin k → O) : tensO A act e ⟶ powO A k :=
  Over.homMk (pullback.fst _ _) rfl

def tcoord {k : ℕ} (e : Fin k → Fin k → O) (j : Fin k) : tensO A act e ⟶ A :=
  tensIncl A act e ≫ prj A k j


end Formalism.L2.Pj
end
end
