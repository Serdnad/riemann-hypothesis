module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eabV_of_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W)
    (hgu : inUJ ε g) :
    EabV ε a b f g = -(Lhol (Matrix.single a b 1) F (g⁻¹ * m)) := by
  have h1 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart1 ε (Matrix.single a b 1)) hg hgu
  have h2 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart2 ε (Matrix.single a b 1)) hg hgu
  simp only [EabV, EcV, RdV, Lhol]
  rw [h1.deriv, h2.deriv]
  conv_rhs => rw [← ccb_cpart_sum ε (Matrix.single a b 1)]
  rw [add_mul, smul_mul_assoc, map_add (f := _), map_smul, smul_neg, neg_add]

theorem contDiffOn_of_local [CompleteSpace E] {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) : ContDiffOn ℝ ∞ (fun g => F (g⁻¹ * m)) W := by
  classical
  have hent : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) := by
    intro i j
    fun_prop
  have hdet : ∀ {G : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ},
      (∀ i j, ContDiff ℂ ∞ (fun A => G A i j)) → ContDiff ℂ ∞ (fun A => (G A).det) := by
    intro G hG
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    exact contDiff_prod fun i _ => hG _ _
  have hadj : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate i j) := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine hdet fun k l => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact hent k l
  have hinv : ContDiffOn ℂ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W := by
    intro g hg
    have hdg : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp (hWV g hg).1).ne_zero
    have hid : ContDiffAt ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) g :=
      ((hdet fun i j => hent i j).contDiffAt).inv hdg
    refine ContDiffAt.contDiffWithinAt ?_
    refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
    simp only [Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact ContDiffAt.sum fun k _ => (hid.mul (hadj i k).contDiffAt).mul contDiffAt_const
  have hFc : ContDiffOn ℂ ∞ F V := cca_contDiffOn hV hF
  have hc : ContDiffOn ℂ ∞ (F ∘ fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W :=
    hFc.comp hinv fun g hg => (hWV g hg).2
  exact hc.restrict_scalars ℝ

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma cb_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j) := by
    ext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow]
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a j => A a j • B j)
  have h2 : ∀ f : Fin i → Fin N,
      (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) =
        (∏ a, A a (f a)) * (B.submatrix f id).det := by
    intro f
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  exact h1.trans (Finset.sum_congr rfl fun f _ => h2 f)

private def cbPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

private lemma cbPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cbPar ⟨⟨S, hS⟩, σ⟩) = S := by
  simp only [cbPar]
  rw [← Finset.map_map, Finset.map_univ_equiv]
  exact Finset.map_orderEmbOfFin_univ S hS

private lemma cbPar_bij {i N : ℕ} : Function.Bijective (cbPar (i := i) (N := N)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h
    have hSS : S = S' := by
      rw [← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]
    subst hSS
    have hσ : σ = σ' := by
      ext a
      have h2 := DFunLike.congr_fun h a
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst hσ
    rfl
  · intro g
    have hcard : (univ.map g).card = i := by simp
    have hmem : ∀ a, g a ∈ univ.map g := fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)
    let g' : Fin i ≃ (univ.map g) := Equiv.ofBijective (fun a => ⟨g a, hmem a⟩)
      ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact ⟨a, rfl⟩⟩
    refine ⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    change ((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl

theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f →
      (∏ a, A a (f a)) * (B.submatrix f id).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]
  have hS : ∀ S : {S : Finset (Fin N) // S.card = i},
      ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det =
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    intro S
    have hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det =
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a)) := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hB, Matrix.det_permute]
    change (∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _
    ring
  calc (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        cb_det_mul_fun A B
    _ = ∑ f ∈ univ.filter Function.Injective, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        (Finset.sum_filter_of_ne fun f _ hf => by
          by_contra hni
          exact hf (hz f hni)).symm
    _ = ∑ x : {f : Fin i → Fin N // Function.Injective f},
          (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det :=
        Finset.sum_subtype _ (fun f => by simp) _
    _ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det :=
        Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)
    _ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det :=
        (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm
    _ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det :=
        Fintype.sum_sigma _
    _ = _ := Finset.sum_congr rfl fun S _ => hS S

theorem lead_unitary_diag {U : Matrix (Fin n) (Fin n) ℂ} (d : Fin n → ℂ) (i : ℕ) (hi : i ≤ n) :
    lead i (U * Matrix.diagonal d * Uᴴ) =
      ∑ J : {J : Finset (Fin n) // J.card = i},
        ((‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 : ℝ) : ℂ) * ∏ j ∈ J.1, d j := by
  unfold lead
  rw [dite_eq_left hi]
  have hsub : (U * Matrix.diagonal d * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d) * (U.submatrix (Fin.castLE hi) id)ᴴ := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsub, det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h1 : (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d).submatrix id (J.1.orderEmbOfFin J.2) =
      U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2) *
        Matrix.diagonal (fun a => d (J.1.orderEmbOfFin J.2 a)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  have h2 : (U.submatrix (Fin.castLE hi) id)ᴴ.submatrix (J.1.orderEmbOfFin J.2) id =
      (U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2))ᴴ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hp : ∏ a, d (J.1.orderEmbOfFin J.2 a) = ∏ j ∈ J.1, d j := by
    calc ∏ a, d (J.1.orderEmbOfFin J.2 a)
        = ∏ j ∈ univ.map (J.1.orderEmbOfFin J.2).toEmbedding, d j := (Finset.prod_map _ _ _).symm
      _ = ∏ j ∈ J.1, d j := by rw [Finset.map_orderEmbOfFin_univ]
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hp, hn]
  ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma sub_lower_mul {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (c * M).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      c.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have ha := a.2
  rw [hc _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]

private lemma sub_mul_upper {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c')
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (M * c').submatrix (Fin.castLE hi) (Fin.castLE hi) =
      M.submatrix (Fin.castLE hi) (Fin.castLE hi) * c'.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ (fun k => rfl)
  intro k hk
  have hk' : i ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
  have hb := b.2
  unfold IsUpperTri at hc'
  rw [hc' _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

private lemma lowerTri_sub {i : ℕ} (hi : i ≤ n) {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) :
    (c.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsLowerTriangular := by
  intro a b hab
  have hab' : a < b := hab
  apply hc
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

private lemma upperTri_sub {i : ℕ} (hi : i ≤ n) {c' : Matrix (Fin n) (Fin n) ℂ} (hc' : IsUpperTri c') :
    (c'.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
  intro a b hab
  have hab' : b < a := hab
  apply hc'
  rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
  exact hab'

theorem lead_tri_mul {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c') (i : ℕ) (hi : i ≤ n) :
    lead i (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), c l l * c' l l) * lead i z := by
  have hp : ∀ f : Fin n → ℂ, ∏ a : Fin i, f (Fin.castLE hi a) =
      ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), f l := by
    intro f
    rw [Finset.prod_filter]
    refine Fintype.prod_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ _ ?_ ?_
    · intro k hk
      rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · intro a
      rw [if_pos (by rw [Fin.coe_castLE]; exact a.2)]
  unfold lead
  rw [dite_eq_left hi, dite_eq_left hi, sub_mul_upper hi hc', sub_lower_mul hi hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular _ (lowerTri_sub hi hc), Matrix.det_of_upperTriangular (upperTri_sub hi hc'),
    Finset.prod_mul_distrib, ← hp (fun l => c l l), ← hp (fun l => c' l l)]
  simp only [Matrix.submatrix_apply]
  ring

theorem lead_posDef {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (i : ℕ) (hi : i ≤ n) :
    0 < (lead i x).re ∧ (lead i x).im = 0 := by
  have hp := (hx.submatrix (Fin.castLE_injective hi)).det_pos
  unfold lead
  rw [dite_eq_left hi]
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hp
  exact ⟨h1, h2.symm⟩

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_mu {lam : Fin n → ℝ} (hlam : IsHCParam lam) : ∃ μ : Fin n → ℤ, IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), ?_⟩
  unfold IsMu
  intro a
  have h := hm a
  simp only [rho]
  push_cast
  linarith

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def casCoef (μ : Fin n → ℤ) (a b : Fin n) : ℝ :=
  (if a = b then (μ a : ℝ) ^ 2 else 0) + (if b < a then (μ a : ℝ) - μ b else 0)

theorem sum_casCoef (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∑ a, ∑ b, casCoef μ a b = casVal lam := by
  have hcard : ∀ a : Fin n, (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) -
      (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) = -2 * rho n a := by
    intro a
    rw [Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi, Fin.card_Iio, Fin.card_Ioi]
    have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub ha]
    simp only [rho]
    push_cast
    ring
  have hrow : ∀ a, ∑ b, casCoef μ a b = (μ a : ℝ) ^ 2 +
      ∑ b, ((if b < a then (μ a : ℝ) else 0) - if b < a then (μ b : ℝ) else 0) := by
    intro a
    rw [show (μ a : ℝ) ^ 2 = ∑ b, (if a = b then (μ a : ℝ) ^ 2 else 0) by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold casCoef
    split_ifs <;> ring
  have hswap : ∑ a : Fin n, ∑ b : Fin n, (if b < a then (μ b : ℝ) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) := Finset.sum_comm
  have hA : ∀ a : Fin n, ∑ b : Fin n, (if b < a then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∀ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ a, ∑ b, casCoef μ a b = ∑ a, (μ a : ℝ) ^ 2 + ((∑ a, ∑ b, if b < a then (μ a : ℝ) else 0) -
        ∑ a, ∑ b, if b < a then (μ b : ℝ) else 0) := by
        simp only [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a, ((μ a : ℝ) ^ 2 + (μ a : ℝ) * (-2 * rho n a)) := by
        rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA, hB, ← hcard]
        ring
    _ = casVal lam := by
        simp only [casVal, nsq, dot, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hμ a]
        ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
