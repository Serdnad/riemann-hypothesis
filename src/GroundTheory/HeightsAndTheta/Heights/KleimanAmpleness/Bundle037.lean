module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import Mathlib.Algebra.Group.ForwardDiff
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

namespace VeryAmpleHilbert

theorem exists_slice (Q : MvPolynomial (Fin 2) ℚ) (e : ℕ) (hQ : Q.totalDegree ≤ e) (c : ℚ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ e ∧ p.coeff e = Q.coeff (Finsupp.single 0 e) ∧
      ∀ a : ℚ, p.eval a = MvPolynomial.eval ![a, c] Q := by
  have hdeg : ∀ m ∈ Q.support, m 0 + m 1 ≤ e := fun m hm => by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  refine ⟨∑ m ∈ Q.support, Polynomial.C (Q.coeff m * c ^ m 1) * Polynomial.X ^ m 0, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := hdeg m hm
    omega
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 e)]
    · simp
    · intro m hm hne
      rw [if_neg]
      intro hme
      apply hne
      have := hdeg m hm
      ext i
      fin_cases i
      · simp [hme]
      · simp
        omega
    · intro h
      rw [MvPolynomial.notMem_support_iff.mp h]
      simp
  · intro a
    rw [Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem fwdDiff_iter_eval (p : Polynomial ℚ) (e : ℕ) (hp : p.natDegree ≤ e) (y : ℚ) :
    (fwdDiff 1)^[e] p.eval y = e.factorial * p.coeff e := by
  rcases hp.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rw [Polynomial.leadingCoeff, mul_comm]

theorem sum_subsets_eq_fwdDiff (e : ℕ) (f : ℚ → ℚ) :
    ∑ T : Finset (Fin e), (-1 : ℚ) ^ (e - T.card) * f T.card = (fwdDiff 1)^[e] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun m => (-1 : ℚ) ^ (e - m) * f m), Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_const (Q : SubSystem k x Ω) {n : ℕ} (l : List (Fin n)) (m : ℕ) :
    l.foldl (fun F _ => F.twist Q) (Q.pow m) = Q.pow (m + l.length) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    change l.foldl _ (Q.pow (m + 1)) = _
    rw [ih]
    congr 1
    omega

theorem tensorSub_const (Q : SubSystem k x Ω) {n : ℕ} (T : Finset (Fin n)) :
    tensorSub (fun _ : Fin n => Q) T = Q.pow T.card := by
  have h := foldl_twist_const Q ((List.finRange n).filter (· ∈ T)) 0
  rw [zero_add] at h
  unfold tensorSub
  refine h.trans ?_
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

end VeryAmpleHilbert


open VeryAmpleHilbert in
theorem VeryAmpleHilbert.proof (hS : VeryAmpleSnapper.Statement.{u, w}) : VeryAmpleHilbert.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hN
  obtain ⟨hfin, Q, c₀, hdeg, hQ, hQ0⟩ := hS k Ω N x e Nb hZ hN
  have hpow : ∀ n : ℕ, twistMul Nb.toSubSystem n 0 = Nb.toSubSystem.pow n := fun n =>
    SubSystem.twist_twistSys_zero _
  refine ⟨fun n => hpow n ▸ hfin n 0, ?_⟩
  obtain ⟨P, hPdeg, hPe, hPev⟩ := exists_slice Q e hdeg 0
  refine ⟨P, hPdeg, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hZ.relevant
    have hxj : x j ≠ 0 := fun h0 => hj ((mem_primeOf_of_isHomogeneous x
      (MvPolynomial.isHomogeneous_X k j)).mpr (by rw [MvPolynomial.aeval_X, h0]))
    have hsum : ∀ c : ℕ, c₀ ≤ c → (interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c : ℚ) =
        e.factorial * Q.coeff (Finsupp.single 0 e) := by
      intro c hc
      obtain ⟨p, hpd, hpe, hpv⟩ := exists_slice Q e hdeg c
      rw [← hpe, ← fwdDiff_iter_eval p e hpd 0, funext hpv, ← sum_subsets_eq_fwdDiff, interSum]
      push_cast
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [tensorSub_const, SectionsOverLocalization.restrLen_primeOf_eq_finrank x hxj, Int.cast_natCast]
      congr 1
      have h := hQ T.card c hc
      rw [Int.cast_natCast] at h
      exact h
    set z := interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c₀.toNat
    have hz : ∀ c : ℕ, c₀.toNat ≤ c →
        interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c = z := fun c hc => by
      have h1 := hsum c (by omega)
      rw [← hsum c₀.toNat (by omega)] at h1
      exact_mod_cast h1
    have hlim : interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) = z :=
      (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨c₀.toNat, fun c hc => (hz c hc).symm⟩)).limUnder_eq
    rw [hlim, hsum c₀.toNat (by omega), hPe, mul_comm]
  · filter_upwards [hQ0] with n hn
    rw [hn, hPev]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver mConeMapOver chartRingOver quotPart)

namespace CechPointVanish

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

theorem constD_congr {V : Type} [AddCommGroup V] (G : ∀ k, Finset (ι k)) (n : ℕ) {f f' : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → V}
    (h : ∀ J : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, (∀ k, J.1 k ⊆ G k) → f J = f' J) (I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) (hI : ∀ k, I.1 k ⊆ G k) :
    constD K ι V n f I = constD K ι V n f' I := by
  unfold constD
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))
  · rfl

variable {S : Type} [CommRing S]

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']


open Classical in
theorem cechD_apply {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

end Cells

section Point

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω}

end Point

end CechPointVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeDecomp

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨Finsupp.single ⟨k, i⟩ 1, rfl, fun q hq => ?_⟩
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hi
  | one => exact ⟨0, by rw [← C_1, C_apply], by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨u, rfl, hu⟩ := hf
    obtain ⟨v, rfl, hv⟩ := hg
    refine ⟨u + v, by rw [monomial_mul, one_mul], fun q hq => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact hu q h
    · exact hv q h

section Frac

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]

theorem overDen_apply (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl

end Frac

theorem quot_mk_smul (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem mk_monomial_eq (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by
  classical
  have hneg : ∀ k, negSet (fun q => (v q : ℤ) - u q) k ⊆ I k := by
    intro k i hi
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hu ⟨k, i⟩ (Finsupp.mem_support_iff.mpr (by omega))
  have hexp : negExp (fun q => (v q : ℤ) - u q) + v = u + posExp (fun q => (v q : ℤ) - u q) := by
    ext q
    simp only [Finsupp.add_apply, posExp, negExp, Finsupp.coe_equivFunOnFinite_symm]
    omega
  rw [monoFrac, dite_eq_left hneg, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    monomial_mul, mul_one]
  rw [hexp]

theorem locPart_le (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, AddMonoidAlgebra.coeff p v • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]

    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm

theorem embed_apply_cell [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by
  classical
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rw [LinearMap.zero_apply, monoFrac, dite_eq_right h, smul_zero]

end KHFreeDecomp


open KHFreeDecomp in
theorem KHFreeDecomp.full : KHFreeDecomp.Statement := by
  intro S _ K _ _ ι _ _ c d n φ hφ
  classical
  have hI : ∀ I : KH.Cell K ι n, ∃ l : ((Σ k, ι k) → ℤ) →₀ S,
      l ∈ Finsupp.supported S S {a | blockSum a = c + d} ∧
        Finsupp.linearCombination S (monoFrac S I.1) l = φ I := by
    intro I
    have hx : φ I ∈ KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d))
        (KH.cellMon S I.1) c := hφ I (Set.mem_univ _)
    exact (Finsupp.mem_span_image_iff_linearCombination S).mp (locPart_le I.1 c d hx)
  choose l hl hlφ using hI
  let _ : Fintype (KH.Cell K ι n) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.biUnion fun I => (l I).support, fun a J => l J.1 a, ?_, ?_⟩
  · intro a ha
    obtain ⟨I, -, haI⟩ := Finset.mem_biUnion.mp ha
    exact hl I haI
  · funext I
    rw [Finset.sum_apply, ← hlφ I, Finsupp.linearCombination_apply, Finsupp.sum]
    beta_reduce
    refine (Finset.sum_subset (s₁ := (l I).support) (s₂ := Finset.univ.biUnion fun I => (l I).support)
      (f := fun a => l I a • monoFrac S I.1 a) (fun a ha => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, ha⟩) ?_).trans
      (Finset.sum_congr rfl fun a _ => (embed_apply_cell a n (fun J => l J a) I).symm)
    intro a _ ha
    rw [Finsupp.mem_support_iff, not_not] at ha
    rw [ha, zero_smul]

end

end GroundTheory.Heights₂.Heights.Kleiman
end
