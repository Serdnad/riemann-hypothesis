module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_unique_of_lower : ∀ (K : Type) [Field K] (s : ℕ) (y y' : Low s → K) (b : Matrix (Fin s) (Fin s) K),
    (∀ i j, i < j → b i j = 0) → upU y = b * upU y' → y = y' := by
  intro K _ s y y' b hb h
  have key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j := by
    intro i j hk
    rw [h, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [upU]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h1 | h1
      · rw [hk k h1, zero_mul]
      · simp [upU, not_lt.mpr h1.le, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0 := by
    intro i N
    induction N with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hji
      rw [← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]
      simp [upU, not_lt.mpr hji.le, hji.ne']
  have hb1 : b = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hb i j h1, Matrix.one_apply_ne h1.ne]
    · rw [← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]
      simp [upU]
    · rw [low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']
  rw [hb1, Matrix.one_mul] at h
  funext ⟨⟨c, a⟩, hac⟩
  have hac' : a < c := hac
  have := congrFun (congrFun h a) c
  simpa [upU, hac'] using this

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

noncomputable def ptEquiv (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) : V d × (J → ℂ) ≃ᵐ V n :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm (MeasurableEquiv.refl (J → ℂ))).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm).trans
    ((MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)).trans (MeasurableEquiv.toLp 2 (Fin n → ℂ)))

theorem ptEquiv_apply (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (x : V d × (J → ℂ)) :
    ptEquiv n d J ε x = pt ε x.1 x.2 := by
  ext i
  change (Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)
  cases ε i <;> rfl

theorem measurePreserving_pt_split : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J),
    MeasurePreserving (fun x : V d × (J → ℂ) => pt ε x.1 x.2) volume volume ∧
      MeasurableEmbedding (fun x : V d × (J → ℂ) => pt ε x.1 x.2) := by
  intro n d J _ ε
  have e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε) := by
    funext x; exact (ptEquiv_apply n d J ε x).symm
  rw [e]
  refine ⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩
  have h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume := volume_preserving_ofLp_complex (Fin d)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))
  exact h5.comp h4

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2.BaseVol

open GlobalTheory.LocFub.TopDens (dens_smul dens_add dens_zero)

variable {n d : ℕ} {J : Type}

theorem pull_bsL_dz (ε : Fin n ≃ Fin d ⊕ J) (a : Fin d) :
    pull (bsL ε) (dz a) = dz (ε.symm (.inl a)) ∧ pull (bsL ε) (dzb a) = dzb (ε.symm (.inl a)) := by
  rw [(pull_dz _ a).1, (pull_dz _ a).2]
  simp [bsL_apply, coordVec, PiLp.single_apply]

theorem pull_bsL_prod (ε : Fin n ≃ Fin d ⊕ J) (s : Finset (Fin d)) :
    pull (bsL ε) ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev d) : Alt d) =
      ((∏ a ∈ s, (Complex.I / 2) • sym (ε.symm (.inl a), ε.symm (.inl a)) : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]
    congr 1
    simp [sym, (pull_bsL_dz ε a).1, (pull_bsL_dz ε a).2]

theorem prod_mem (g : J → Fin n) (s : Finset J) :
    ((∏ j ∈ s, (Complex.I / 2) • sym (g j, g j) : Ev n) : Alt n) ∈ ⋀[ℂ]^(2 * s.card) (Fin n ⊕ Fin n → ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subalgebra.coe_mul, Finset.card_insert_of_notMem ha,
      show 2 * (s.card + 1) = 1 + 1 + 2 * s.card by ring]
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ih
    rw [Subalgebra.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    change dz (g a) * dzb (g a) ∈ _
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ?_
    · simp [dz, ExteriorAlgebra.exteriorPower]
    · simp [dzb, ExteriorAlgebra.exteriorPower]

theorem dens_pull_bas [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) {T : Finset (Fin (d + d))} (hT : T ≠ Finset.univ) :
    dens (pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = 0 := by
  have hc : T.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
  have hn : n = d + Fintype.card J := by simpa using Fintype.card_congr ε
  have hm : pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) ∈
      ⋀[ℂ]^(T.card + 2 * (Finset.univ : Finset J).card) (Fin n ⊕ Fin n → ℂ) := by
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ (prod_mem _ _)
    rw [bas, ExteriorAlgebra.basis_apply _ T, CxForm.pull, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact Subtype.property _
  have := GlobalTheory.PullTop.repr_eq_zero_of_card_ne
    ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  rw [dens]
  exact div_eq_zero_iff.2 (Or.inl this)

theorem pull_vol_mul [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) :
    pull (bsL ε) (vol d : Alt d) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) = (vol n : Alt n) := by
  rw [vol, pull_bsL_prod, ← Subalgebra.coe_mul, vol, ← ε.symm.prod_comp, Fintype.prod_sum_type]

theorem dens_pull_mul_vol : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  intro n d J _ ε α
  have hα : α ∈ Submodule.span ℂ (Set.range (bas d)) := by rw [(bas d).span_eq]; trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    by_cases hT : T = Finset.univ
    · obtain ⟨c, hc, e⟩ := vol_eq d
      have e' : bas d T = c⁻¹ • (vol d : Alt d) := by rw [e, hT, inv_smul_smul₀ hc]
      rw [e', map_smul, smul_mul_assoc, dens_smul, dens_smul, dens_vol, pull_vol_mul, dens_vol]
    · rw [dens_pull_bas ε hT]
      simp [dens, hT]
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), add_mul, dens_add, dens_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx]

end GlobalTheory.FlagCell2.BaseVol
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagTri

theorem eval_zero_of_const {A : Type} [CommRing A] [Algebra ℂ A] (l : A →ₗ[ℂ] ℂ) (Q : Polynomial A) (c : ℂ)
    (h : ∀ x : ℂ, x ≠ 0 → l (Q.eval (algebraMap ℂ A x)) = c) : l (Q.eval (algebraMap ℂ A 0)) = c := by
  have hc : Continuous fun x : ℂ => l (Q.eval (algebraMap ℂ A x)) := by
    clear h
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, map_add (f := _)]; exact hp.add hq
    | monomial k a =>
      have : (fun x : ℂ => l ((Polynomial.monomial k a).eval (algebraMap ℂ A x))) = fun x => x ^ k * l a := by
        funext x
        rw [Polynomial.eval_monomial, ← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [this]
      fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc (continuous_const (y := c)) (fun x hx => h x hx)
  exact congrFun this 0

variable {n : ℕ}

def scale (c : Fin n → ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.diagonal (Sum.elim c c)))

theorem dens_scale (c : Fin n → ℂ) (β : Alt n) : dens (scale c β) = (∏ a, c a) ^ 2 * dens β := by
  simp only [dens, scale, bas]
  rw [exterior_repr_univ_map, LinearMap.det_toLin', Matrix.det_diagonal, Fintype.prod_sum_type, mul_div_assoc, sq]
  rfl

theorem scale_dz (c : Fin n → ℂ) (a : Fin n) : scale c (dz a) = c a • dz a ∧ scale c (dzb a) = c a • dzb a := by
  simp only [dz, dzb, ← map_smul]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    by_cases h : b = a <;> simp [Matrix.mulVec_diagonal, Pi.single_apply, h]

theorem scale_sym (c : Fin n → ℂ) (a b : Fin n) :
    scale c (sym (a, b) : Ev n) = (c a * c b) • ((sym (a, b) : Ev n) : Alt n) := by
  change scale c (dz a * dzb b) = (c a * c b) • (dz a * dzb b)
  rw [map_mul, (scale_dz c a).1, (scale_dz c b).2, smul_mul_smul_comm]

theorem scale_pull {d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (c : Fin n → ℂ) (hc : ∀ a, c (ε.symm (.inl a)) = 1)
    (α : Alt d) : scale c (pull (bsL ε) α) = pull (bsL ε) α := by
  have key (a : Fin d) (b : Fin n) : c b * bsL ε (coordVec b) a = bsL ε (coordVec b) a ∧
      c b * (starRingEnd ℂ) (bsL ε (coordVec b) a) = (starRingEnd ℂ) (bsL ε (coordVec b) a) := by
    rw [bsL_apply]
    by_cases h : ε.symm (.inl a) = b
    · subst h
      simp [hc]
    · simp [coordVec, h]
  rw [scale, pull, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
  congr 3
  ext (i | i) (j | j) <;> simp [Matrix.diagonal_mul, key]

theorem map_prod_pow {T : Type} (φ : Alt n →ₐ[ℂ] Alt n) (x y : T → Ev n) (r : T → ℕ)
    (h : ∀ t, φ (x t) = y t) (s : Finset T) :
    φ ((∏ t ∈ s, x t ^ r t : Ev n) : Alt n) = ((∏ t ∈ s, y t ^ r t : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih,
      Subalgebra.coe_pow, Subalgebra.coe_pow, map_pow, h]

theorem dens_blockTri : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  intro n d J T _ _ ε lev ρ K r hr hK α
  let wt : Fin n → ℕ := fun a => (ε a).elim (fun _ => 0) fun j => ρ (lev j) + 1
  have w0 (a) : wt (ε.symm (.inl a)) = 0 := by simp [wt]
  have w1 (j) : wt (ε.symm (.inr j)) = ρ (lev j) + 1 := by simp [wt]
  have hw (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) :
      wt a < ρ t + 1 ∨ ∃ j : {j // lev j = t}, ε.symm (.inr j.1) = a := by
    obtain ⟨a | j, rfl⟩ := ε.symm.surjective a
    · left; rw [w0]; omega
    · by_cases e : lev j = t
      · exact .inr ⟨⟨j, e⟩, rfl⟩
      · left
        rw [w1]
        by_contra hn
        obtain ⟨b, hb⟩ := h
        have := hK t j e (by omega) b
        tauto
  have hw' (t : T) (a : Fin n) (h : ∃ b, K t a b ≠ 0 ∨ K t b a ≠ 0) : wt a ≤ ρ t + 1 := by
    rcases hw t a h with h | ⟨j, rfl⟩
    · omega
    · rw [w1, j.2]
  let l : Ev n →ₗ[ℂ] ℂ :=
    { toFun := fun x => dens (pull (bsL ε) α * (x : Alt n))
      map_add' := fun x y => by simp [dens, mul_add, add_div]
      map_smul' := fun c x => by simp [dens, mul_div_assoc] }
  have hl (x : Ev n) : l x = dens (pull (bsL ε) α * (x : Alt n)) := rfl
  let e : T → Fin n → Fin n → ℕ := fun t a b => (ρ t + 1 - wt a) + (ρ t + 1 - wt b)
  let Q : Polynomial (Ev n) := ∏ t, (∑ a, ∑ b, Polynomial.monomial (e t a b) (K t a b • sym (a, b))) ^ r t
  have hQ (x : ℂ) : Q.eval (algebraMap ℂ (Ev n) x) =
      ∏ t, (∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) ^ r t := by
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← map_pow, mul_comm, ← Algebra.smul_def, smul_smul]
  rw [← hl, ← hl, ← eval_zero_of_const l Q (l (∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n)) ?_]
  · rw [hQ]
    refine congrArg l (Finset.prod_congr rfl fun t _ => congrArg (· ^ r t) ?_)
    have inj : Function.Injective fun j : {j // lev j = t} => ε.symm (.inr j.1) :=
      fun i j h => Subtype.ext (Sum.inr_injective (ε.symm.injective h))
    symm
    refine Fintype.sum_of_injective _ inj _ _ (fun a ha => Finset.sum_eq_zero fun b _ => ?_) fun a => ?_
    · by_cases h : K t a b = 0
      · simp [h]
      · rcases hw t a ⟨b, .inl h⟩ with h' | h'
        · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
        · exact absurd h' ha
    · refine Fintype.sum_of_injective _ inj _ _ (fun b hb => ?_) fun b => ?_
      · by_cases h : K t (ε.symm (.inr a.1)) b = 0
        · simp [h]
        · rcases hw t b ⟨_, .inr h⟩ with h' | h'
          · rw [zero_pow (by simp only [e]; omega), zero_mul, zero_smul]
          · exact absurd h' hb
      · simp [e, w1, a.2, b.2]
  · intro x hx
    have h1 := dens_scale (fun a => x⁻¹ ^ wt a)
      (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n))
    rw [map_mul, scale_pull ε _ (fun a => by simp [w0]),
      map_prod_pow _ _ (fun t => (x⁻¹ ^ (ρ t + 1)) ^ 2 • ∑ a, ∑ b, (x ^ e t a b * K t a b) • (sym (a, b) : Ev n)) r ?_,
      ← hl, ← hl] at h1
    · have h2 : ∏ a, x⁻¹ ^ wt a = ∏ t, (x⁻¹ ^ (ρ t + 1)) ^ r t := by
        rw [← ε.symm.prod_comp, Fintype.prod_sum_type]
        simp only [w0, w1, pow_zero, Finset.prod_const_one, one_mul]
        rw [← Fintype.prod_fiberwise lev]
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [Finset.prod_congr rfl (g := fun _ => x⁻¹ ^ (ρ t + 1)) fun j _ => by rw [j.2], Finset.prod_const, hr]
        simp
      simp only [smul_pow, Finset.prod_smul] at h1
      rw [map_smul, ← hQ, h2, ← Finset.prod_pow, smul_eq_mul] at h1
      simp only [← pow_mul, mul_right_comm _ (r _) 2] at h1
      refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (inv_ne_zero hx)) h1
    · intro t

      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, map_sum, map_smul, scale_sym, Finset.smul_sum,
      smul_smul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      by_cases h : K t a b = 0
      · simp [h]
      · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le (hw' t a ⟨b, .inl h⟩)
        obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hw' t b ⟨a, .inr h⟩)
        have : e t a b = p + q := by simp only [e]; omega
        rw [this, sq]
        nth_rw 1 [hp]
        rw [hq]
        simp only [inv_pow]
        field_simp
        ring

end GlobalTheory.FlagTri
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullGram_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  intro F _ σ X Y ι _ m E E' φ f hf hR _c A u H hH z hz
  obtain ⟨hA, hB⟩ := hz
  funext τ
  rw [(GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH z).2 A hA _ hB τ]
  have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := fun τ => by
    change ((A τ).map φ).det ≠ 0
    have := RingHom.map_det (φ : X.Fn →+* Y.Fn) (A τ)
    rw [RingHom.mapMatrix_apply] at this
    change ((A τ).map (φ : X.Fn →+* Y.Fn)).det ≠ 0
    rw [← this]
    exact (map_ne_zero _).2 (Fr.det_ne hA τ)
  have e : upM u * A.map φ * (A.map φ)⁻¹ = upM u := by rw [mul_assoc, Mat.mul_inv hd, mul_one]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have h0 : ratVal (0 : Y.Fn) z = 0 := by simpa using hψ 0
  have h1 : ratVal (1 : Y.Fn) z = 1 := by simpa using hψ 1
  have hv : (upM u).map (ratVal · z) τ = upM (fun j => ratVal (u j) z) τ := by
    ext a b
    simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [h0, h1]
  rw [e, hv]

end GlobalTheory.FlagCell2
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)


theorem _root_.GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  first | exact @GlobalTheory.LocPlTau.exists_splitPrime_locPl | exact GlobalTheory.LocPlTau.exists_splitPrime_locPl | (intros; apply GlobalTheory.LocPlTau.exists_splitPrime_locPl <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.squareNu_inv_hasInfinityType_cmType : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | exact GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_hasInf <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.squareNu_inv_unramified_over_inert_prime : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | exact GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ <;> assumption)
end
