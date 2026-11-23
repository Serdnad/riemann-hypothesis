module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle072
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle902
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.RowSubstTransvection

theorem natDegree_rowGen_le (O : Type) [CommRing O] (N : ℕ) (a b : Fin N)
    (f : MvPolynomial (Fin N × Fin N) O) :
    (rowGen O (n := N) a b f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]

  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [rowGen, aeval_monomial]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (algebraMap O (Polynomial (MvPolynomial (Fin N × Fin N) O)) (f.coeff m)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add]
  have hg : ∀ v : Fin N × Fin N, (Polynomial.C (X v : MvPolynomial (Fin N × Fin N) O) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)).natDegree ≤ 1 := by
    intro v
    split_ifs
    · refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le
    · simp
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum]
  apply Finset.sum_le_sum
  intro v _
  refine (Polynomial.natDegree_pow_le).trans ?_
  simpa using Nat.mul_le_mul_left (m v) (hg v)

theorem rowSubst_transvection (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f.totalDegree ≤ D) :
    rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  have key : (rowSubst O N R (Matrix.transvection a b r)).toRingHom =
      (Polynomial.evalRingHom (C r : MvPolynomial (Fin N × Fin N) R)).comp
        ((Polynomial.mapRingHom (MvPolynomial.map (σ := Fin N × Fin N) (algebraMap O R))).comp
          (rowGen O (n := N) b a).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowSubst, rowGen, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowSubst, rowGen, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      by_cases h : v.1 = a
      · have h' : a = v.1 := h.symm
        simp only [h', true_and, if_true]
        simp [apply_ite C, ite_mul, Finset.sum_ite_eq']
        ring
      · have h' : ¬ a = v.1 := fun e => h e.symm
        simp [h, h']
  have h1 := DFunLike.congr_fun key f
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
    Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom] at h1
  rw [h1, Polynomial.eval_eq_sum_range' (n := D + 1)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_map, smul_eq_C_mul, C_pow, mul_comm]
    rfl
  · exact Nat.lt_succ_of_le ((Polynomial.natDegree_map_le).trans ((natDegree_rowGen_le O N b a f).trans hf))

end GlobalTheory.RowSubstTransvection
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

namespace GlobalTheory.DiagRowSubst

theorem diag_var (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (v : Fin N × Fin N) :
    (∑ b : Fin N, C (Matrix.diagonal d v.1 b) * X (b, v.2) : MvPolynomial (Fin N × Fin N) R) = C (d v.1) * X v := by
  simp only [Matrix.diagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem weight_prod (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (m : Fin N × Fin N →₀ ℕ) :
    ∏ a, d a ^ Finsupp.weight (rowW N N) m a = m.prod (fun v e => d v.1 ^ e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ v.1]
  simp

theorem weight_le (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a ≤ m.sum (fun _ e => e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> omega

theorem mono (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R)
    (m : Fin N × Fin N →₀ ℕ) (c : O) :
    rowSubst O N R (Matrix.diagonal d) (monomial m c) =
      monomial m (algebraMap O R c * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
  rw [weight_prod, rowSubst, aeval_monomial]
  simp_rw [diag_var, mul_pow]
  rw [Finsupp.prod_mul, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow, MvPolynomial.algebraMap_apply, mul_assoc]

theorem rowSubst_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  intro O _ N R _ _ d D f hf
  classical
  have hL : rowSubst O N R (Matrix.diagonal d) f = ∑ m ∈ f.support,
      monomial m (algebraMap O R (AddMonoidAlgebra.coeff f m) * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
    conv_lhs => rw [f.as_sum]

    rw [map_sum]
    simp_rw [mono]
  rw [hL]

  simp_rw [weightedHomogeneousComponent_apply, map_sum, map_monomial, Finset.smul_sum, smul_monomial, smul_eq_mul,
  Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_ite_eq, if_pos, mul_comm]
  rw [Fintype.mem_piFinset]
  intro a
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (weight_le N m a).trans ((le_totalDegree hm).trans hf)

end GlobalTheory.DiagRowSubst
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenCoef

theorem rowSubst_mul_comp (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O) :
    rowSubst O N R (Y * Y') f = rowSubst R N R Y' (rowSubst O N R Y f) := by
  have h : (rowSubst O N R (Y * Y')) = ((rowSubst R N R Y').restrictScalars O).comp (rowSubst O N R Y) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp only [rowSubst, AlgHom.comp_apply, AlgHom.restrictScalars_apply, aeval_X, map_sum, map_mul,
    algHom_C, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [h]; rfl

theorem rowSubst_self_map (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y' : Matrix (Fin N) (Fin N) R) (q : MvPolynomial (Fin N × Fin N) O) :
    rowSubst R N R Y' (MvPolynomial.map (algebraMap O R) q) = rowSubst O N R Y' q := by
  have h : ((rowSubst R N R Y').restrictScalars O).comp (MvPolynomial.mapAlgHom (Algebra.ofId O R)) = rowSubst O N R Y' := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowSubst]
  have := congrArg (fun φ => φ q) h
  simpa using this

theorem expr_mul (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (hY : Expr O N ν R Y) (hY' : Expr O N ν R Y') :
    Expr O N ν R (Y * Y') := by
  obtain ⟨n, r, p, hp, hf⟩ := hY
  obtain ⟨n', r', p', hp', hf'⟩ := hY'
  refine ⟨n * n', fun k => r (finProdFinEquiv.symm k).1 * r' (finProdFinEquiv.symm k).2,
    fun k => p' (finProdFinEquiv.symm k).2 * p (finProdFinEquiv.symm k).1, fun k => Subalgebra.mul_mem _ (hp' _) (hp _), ?_⟩
  intro f

  rw [rowSubst_mul_comp, hf f, map_sum]
  have e := (finProdFinEquiv (m := n) (n := n')).symm.sum_comp
    (fun x : Fin n × Fin n' => (r x.1 * r' x.2) • MvPolynomial.map (algebraMap O R)
      (((p' x.2 * p x.1) f : dualWeyl O N N ν) : MvPolynomial (Fin N × Fin N) O))
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rowSubst_self_map, hf' (p i f), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Module.End.mul_apply]

end GlobalTheory.GenCoef
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenCoef.RowSubstSum

def evY (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial (Fin N × Fin N) R :=
  eval₂Hom (MvPolynomial.map (algebraMap O R)) (fun v => C (Y v.1 v.2))

theorem evY_genSub (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) O) : evY O N R Y (GlobalTheory.HighWt.genSub O N f) = rowSubst O N R Y f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [evY, GlobalTheory.HighWt.genSub, rowSubst, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [GlobalTheory.HighWt.genSub, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [GlobalTheory.HighWt.genSub, map_mul] at hp ⊢
    rw [hp]
    congr 1

    simp [evY, rowSubst, map_sum]

theorem evY_eq_sum (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) :
    evY O N R Y P = ∑ m ∈ P.support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) (P.coeff m) := by
  simp only [evY, coe_eval₂Hom, MvPolynomial.eval₂, Finsupp.sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (m.prod fun v k => (C (Y v.1 v.2) : MvPolynomial (Fin N × Fin N) R) ^ k) = C (m.prod fun v k => Y v.1 v.2 ^ k) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h, mul_comm, C_mul']

theorem main : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  intro O _ N R _ _ Y f
  rw [← evY_genSub, evY_eq_sum]

end GlobalTheory.GenCoef.RowSubstSum

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem algHom_eq_subst {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : constantCoeff (f X) = 0) (a : O⟦X⟧) : f a = a.subst (f X) := by
  have hs : HasSubst (f X) := HasSubst.of_constantCoeff_zero' hf
  have e : f = substAlgHom hs :=
    GlobalTheory.CycFr.algHom_ext_X f (substAlgHom hs) (X_dvd_iff.2 hf) (by rw [coe_substAlgHom, subst_X hs])
  conv_lhs => rw [e]
  rw [coe_substAlgHom]

theorem mem_mu_of_isOfFinOrder {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]ˣ)
    (hx : IsOfFinOrder x) : (x : ℤ_[l]) ∈ mu l := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  rw [mu, Polynomial.mem_nthRootsFinset hl]
  have h := GlobalTheory.TorsionCard.eq_one_of_red h2 (x ^ (l - 1)) hx.pow
    (by rw [map_pow, ZMod.units_pow_card_sub_one_eq_one])
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isUnit_sub_one_padicInt {l : ℕ} [Fact l.Prime] : IsUnit (((l - 1 : ℕ) : ℤ_[l])) := by
  have h1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have e : ((l - 1 : ℕ) : ℤ_[l]) = -(1 - (l : ℤ_[l])) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [e, IsUnit.neg_iff]
  exact isUnit_one_sub_self_of_mem_nonunits _ (PadicInt.irreducible_p (p := l)).not_isUnit

section Situation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n)

theorem wach_φ₀_X : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, P.PD_p K]

theorem wach_φ₀_eq (a : (↥(OL LL))⟦X⟧) : W.φ₀ a = phi l ↥(OL LL) a := by
  have hc : constantCoeff (W.φ₀ X) = 0 := by rw [wach_φ₀_X]; simp
  rw [algHom_eq_subst W.φ₀ hc a, wach_φ₀_X]; rfl

theorem wach_q₀_eq : W.q₀ = q l ↥(OL LL) := by
  have e1 := W.q₀_def
  rw [P.PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e1
  exact mul_left_cancel₀ X_ne_zero e1

theorem wach_γ₀_eq (g : W.Gam) (z : ℤ_[l]) (hz : (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) z)
    (a : (↥(OL LL))⟦X⟧) : W.γ₀ g a = act l ↥(OL LL) z a := by
  have e := GlobalTheory.CycFr.eq_act_of_comm W.φ₀ (W.γ₀ g) z (wach_φ₀_X W) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hz])
  rw [e, GlobalTheory.CycFr.act_apply]; rfl

theorem wach_χΓ_onto (hK : K.1 ≤ MaximalUnramifiedExtension l) (z : ℤ_[l]ˣ) :
    ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) := by
  obtain ⟨σ, hσ, hσz⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K hK z
  refine ⟨W.resΓ ⟨σ, hσ⟩, Subtype.val_injective ?_⟩
  have e := W.χΓ_res ⟨σ, hσ⟩
  rw [P.PD_χ K ⟨σ, hσ⟩] at e
  change algebraMap ↥(OL LL) ↥LL.1 _ = algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) _)
  rw [e]
  change algebraMap ℚ_[l] ↥LL.1 (P.χQ σ : ℚ_[l]) = _
  rw [hσz]; rfl

theorem wach_torsion_mem_mu (h2 : l ≠ 2) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    ∃ d ∈ mu l, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 hδ
  refine ⟨(χ δ : ℤ_[l]), mem_mu_of_isOfFinOrder h2 _ ?_, (hχ δ).symm⟩
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← map_pow, hδk, map_one]⟩

theorem wach_mu_mem_torsion (hK : K.1 ≤ MaximalUnramifiedExtension l) (d : ℤ_[l]) (hd : d ∈ mu l) :
    ∃ δ ∈ W.DelF, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hd1 : d ^ (l - 1) = 1 := (Polynomial.mem_nthRootsFinset hl (1 : ℤ_[l])).1 hd
  have hu : IsUnit d := IsUnit.of_pow_eq_one hd1 hl.ne'
  obtain ⟨g, hg⟩ := wach_χΓ_onto W hK hu.unit
  rw [hu.unit_spec] at hg
  refine ⟨g, (W.DelF_def g).2 ⟨l - 1, hl, W.χΓ_inj ?_⟩, hg⟩
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hg, ← map_pow, hd1, map_one, map_one, Units.val_one]

theorem wach_invariants (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) (a : (↥(OL LL))⟦X⟧) :
    (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ↔ ∃ y, inc l ↥(OL LL) y = a := by
  have R := fixed_relation_holds l ↥(OL LL) h2 a
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := R.1 (fun d hd => by
      obtain ⟨δ, hδ, hδd⟩ := wach_mu_mem_torsion W hK d hd
      rw [← wach_γ₀_eq W δ d hδd a, ha δ hδ])
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩ δ hδ
    obtain ⟨d, hd, hδd⟩ := wach_torsion_mem_mu W h2 δ hδ
    rw [wach_γ₀_eq W δ d hδd]
    exact R.2 ⟨y, hy.symm⟩ d hd

theorem wach_card_isUnit (h2 : l ≠ 2) (hK : K.1 ≤ Ks K 1) : IsUnit (W.DelF.card : ↥(OL LL)) := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W h2 hK
  have hu := (isUnit_sub_one_padicInt (l := l)).map (algebraMap ℤ_[l] ↥(OL LL))
  rw [map_natCast, ← hc, Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Situation

theorem ringFacts_of_caseA {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) : RingFacts (H.W K 1 LL hA.2.2) :=
  ⟨wach_φ₀_eq _, wach_q₀_eq _, wach_γ₀_eq _, wach_χΓ_onto _ hA.1, wach_invariants _ hA.1 hA.2.1,
    wach_card_isUnit _ hA.2.1 hA.2.2.2.2.1⟩

end GlobalTheory.WachPlace

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  first | exact @GlobalTheory.ValuePullback.valAt_abPull | exact GlobalTheory.ValuePullback.valAt_abPull | (intros; apply GlobalTheory.ValuePullback.valAt_abPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field : GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Hodge → ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧ Module.finrank k (Fil A) = g := by
  first | exact @GlobalTheory.finrank_HdR_Fil_of_field | exact GlobalTheory.finrank_HdR_Fil_of_field | (intros; apply GlobalTheory.finrank_HdR_Fil_of_field <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_remainder_and_flat | exact GlobalTheory.PeriodFamily.taylor_remainder_and_flat | (intros; apply GlobalTheory.PeriodFamily.taylor_remainder_and_flat <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = GlobalTheory.PeriodFamily.taylor N t f + GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → GlobalTheory.PeriodFamily.taylor N t f = GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (GlobalTheory.PeriodFamily.taylor N t f) = GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_formal_properties | exact GlobalTheory.PeriodFamily.taylor_formal_properties | (intros; apply GlobalTheory.PeriodFamily.taylor_formal_properties <;> assumption)
end

section

namespace GlobalTheory

theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockOperators_lie_representation_commute : ∀ (p q r s : ℕ), (∀ Y Z, omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y) ∧ IsLieAct (fockAct1 p q r s) ∧ IsLieAct (fockAct2 p q r s) ∧ ∀ Y Z, fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  first | exact @GlobalTheory.FockAlg.fock_lie_and_commute | exact GlobalTheory.FockAlg.fock_lie_and_commute | (intros; apply GlobalTheory.FockAlg.fock_lie_and_commute <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.unitaryPQCover_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧ LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G := by
  first | exact @GlobalTheory.coverUnitary_unimodular | exact GlobalTheory.coverUnitary_unimodular | (intros; apply GlobalTheory.coverUnitary_unimodular <;> assumption)
end
