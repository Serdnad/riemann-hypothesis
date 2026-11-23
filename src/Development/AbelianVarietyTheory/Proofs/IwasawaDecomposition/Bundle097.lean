module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TeichmullerTiltMinusOneDvdOfThetaFrobeniusZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.DualLattices.Bundle010
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem theta_ker_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θ l) ∧ IsDomain (Per.Ainf l) ∧ ((l : ℕ) : Per.Ainf l) ≠ 0 ∧ ∀ e : Per.Fl l, IsEps e → RingHom.ker (Per.θ l) = Ideal.span {xi e} ∧ xi e ≠ 0 := by
  intro l _
  have hv := PadicComplexInt.integers l
  haveI : IsDomain (Per.Fl l) := PreTilt.isDomain _ _ _ hv l
  have hl : ((l : ℕ) : Per.Ainf l) ≠ 0 := fun h => by
    have h1 := congrArg (Per.θ l) h
    rw [map_natCast, map_zero] at h1
    exact GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h1)
  refine ⟨ReciprocityTheory.PGsh.Ainf.theta_surj l _ hv, inferInstance, hl, fun e he => ?_⟩
  have hε : IsPrimitiveRoot (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) l := by
    have h1 : (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) ^ l = 1 := by
      rw [← map_pow, frobeniusEquiv_symm_pow_p]; exact he.1
    have h2 := he.2
    generalize ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = y at h1 h2 ⊢
    have h3 := IsPrimitiveRoot.orderOf y
    rwa [orderOf_eq_prime h1 h2] at h3
  refine ⟨ReciprocityTheory.PGsh.Ainf.ker_theta l _ hv e hε, fun h => ?_⟩
  exact one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd l _ hv e hε 1 (by rw [one_mul]; exact h))

theorem tilt_facts : ∀ (l : ℕ) [Fact l.Prime], (∀ x : ℕ → Per.OC l, (∀ n, x (n + 1) ^ l = x n) → ∃ e : Per.Fl l, ∀ n, rootT e n = x n) ∧ (∀ e : Per.Fl l, (∀ n, rootT e n = 1) → e = 1) ∧ (∀ (e : Per.Fl l) (m n : ℕ), rootT (e ^ m) n = rootT e n ^ m) := by
  intro l _
  have key : ∀ (e : Per.Fl l) (n : ℕ), Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) =
      PreTilt.coeff n e := by
    intro e n
    rw [rootT, PreTilt.mk_untilt_eq_coeff_zero]
    exact PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e |>.trans (by rw [zero_add])
  refine ⟨fun x hx => ?_, fun e he => ?_, fun e m n => ?_⟩
  · let e : Perfection (ModP (Per.OC l) l) l :=
      ⟨fun n => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (x n), fun n => by
        rw [← map_pow, hx]⟩
    have hp : ∀ n k, x (n + k) ^ l ^ k = x n := by
      intro n k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, hx, ih]
    refine ⟨e, fun n => ?_⟩
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun k => ⟨x (n + k), ?_, ?_⟩
    · refine Eq.trans ?_ (PreTilt.coeff_iterate_frobeniusEquiv_symm (O := Per.OC l) k n e).symm
      rw [add_comm]; rfl
    · rw [hp]
  · refine Perfection.ext fun n => ?_
    have := key e n
    rw [he, map_one] at this
    exact this.symm.trans (map_one (PreTilt.coeff n)).symm
  · rw [rootT, rootT, ← map_pow]
    congr 1
    exact iterate_map_pow (frobeniusEquiv (Per.Fl l) l).symm.toRingHom n e m

theorem thetaP_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θP l) ∧ RingHom.ker (Per.θP l) = Per.kerP l ∧ (∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l])) ∧ (∀ a : Per.AinfP l, Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) ∧ ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  intro l _
  obtain ⟨hs, hdom, hl, hk⟩ := theta_ker_facts l
  have hle : Submonoid.powers ((l : ℕ) : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl
  have hA : ∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l]) :=
    fun a => GlobalTheory.RingIface.fontaineTheta_algebraMap l a
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hsurj : ∀ y : Per.AinfP l, ∃ (n : ℕ) (a : Per.Ainf l),
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y => by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    exact ⟨n, a, by rwa [map_natCast] at h⟩
  have hz : ∀ y : Per.AinfP l, Per.θP l y = 0 → ∃ (n : ℕ) (a : Per.Ainf l), Per.θ l a = 0 ∧
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y hy => by
    obtain ⟨n, a, h⟩ := hsurj y
    refine ⟨n, a, Subtype.ext ?_, h⟩
    rw [← hA, ← h, map_mul, hy, zero_mul]
    rfl
  have hker : RingHom.ker (Per.θP l) = Per.kerP l := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one]))
    obtain ⟨n, a, ha, h⟩ := hz y hy
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
    exact GlobalTheory.RingIface.alg_mem_kerP l ha
  refine ⟨fun x => ?_, hker, hA, fun a => ?_, IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
    IsLocalization.injective _ hle, fun e he => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖x * ((l : ℕ) : ℂ_[l]) ^ n‖ ≤ 1 := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (GlobalTheory.RingBasics.norm_p_lt (p := l))).const_mul ‖x‖
      rw [mul_zero] at h1
      obtain ⟨n, hn⟩ := (h1.eventually (eventually_le_nhds one_pos)).exists
      exact ⟨n, by rwa [norm_mul, norm_pow]⟩
    obtain ⟨a, ha⟩ := hs ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
    obtain ⟨d, hd⟩ := (hu.pow n).exists_right_inv
    refine ⟨algebraMap _ _ a * d, ?_⟩
    have h2 := congrArg (Per.θP l) hd
    rw [map_mul, map_pow, map_natCast, map_one] at h2
    rw [map_mul, hA, ha, mul_assoc, h2, mul_one]
  · exact GlobalTheory.RingIface.thetaD_alg l a
  · obtain ⟨h1, -⟩ := hk e he
    refine le_antisymm (fun y hy => ?_) ?_
    · rw [← hker] at hy
      obtain ⟨n, a, ha, h⟩ := hz y hy
      rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
      have h2 : a ∈ Ideal.span {xi e} := h1 ▸ ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h2
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, ← hker, RingHom.mem_ker, hA, Model.theta_xi he]
      rfl

end GlobalTheory.MemLoc
end

section

noncomputable section
namespace GlobalTheory.MemLoc.SecUniq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem root_eq {K R C : Type} [Field K] [CommRing R] [Field C] (θ : R →+* C)
    (hu : ∀ y : R, θ y ≠ 0 → IsUnit y) (o : K →+* R) (x : K) (y : R) (f : Polynomial K)
    (hy : θ y = θ (o x)) (h0 : f.eval x = 0) (h1 : f.derivative.eval x ≠ 0)
    (h2 : (f.map o).eval y = 0) : y = o x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map o) (o x) (y - o x)
  rw [add_sub_cancel, h2, Polynomial.derivative_map, Polynomial.eval_map_apply,
    Polynomial.eval_map_apply, h0, map_zero, zero_add] at hk
  have hθ : θ (y - o x) = 0 := by rw [map_sub, hy, sub_self]
  have hun : IsUnit (o (f.derivative.eval x) + k * (y - o x)) := by
    apply hu
    rw [map_add (f := _), map_mul, hθ, mul_zero, add_zero]
    exact (map_ne_zero (θ.comp o)).2 h1
  have : (o (f.derivative.eval x) + k * (y - o x)) * (y - o x) = 0 := by
    rw [hk]; ring
  exact sub_eq_zero.1 ((hun.mul_right_eq_zero).1 this)

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {((l : ℕ) : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {((l : ℕ) : R)}) inferInstance _ fun n => ?_)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f w - g w, ?_⟩
  have h1 := congrArg f hz
  have h2 := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at h1 h2
  rw [h1, h2]
  ring

theorem sigA_zA (g : Per.Gq l) (z : ℤ_[l]) : Per.σA g (Per.zA l z) = Per.zA l z := by
  haveI : IsAdicComplete (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  exact padicInt_hom_ext_pt ((Per.σA g).comp (Per.zA l)) (Per.zA l) z

theorem sigDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply]
  rw [GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem sec_root (o : Om l →+* Per.BdRp l) (ho : IsSec o) (x : Om l) (y : Per.BdRp l)
    (f : Polynomial (Om l)) (hy : Per.θD l y = (x : ℂ_[l])) (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x ≠ 0) (h2 : (f.map o).eval y = 0) : y = o x :=
  root_eq (Per.θD l) (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.1 o x y f (by rw [hy, ho.th]) h0 h1 h2

theorem sec_uniq (o : Om l →+* Per.BdRp l) (ho : IsSec o) (o' : Om l →+* Per.BdRp l) (ho' : IsSec o') :
    o' = o := by
  have hq : o'.comp (algebraMap ℚ_[l] (Om l)) = o.comp (algebraMap ℚ_[l] (Om l)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => ?_)
    exact (ho'.z z).trans (ho.z z).symm
  refine RingHom.ext fun x => ?_
  have hs : IsSeparable ℚ_[l] x := Algebra.IsSeparable.isSeparable ℚ_[l] x
  refine sec_root o ho x (o' x) ((minpoly ℚ_[l] x).map (algebraMap ℚ_[l] (Om l))) (ho'.th x) ?_ ?_ ?_
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]
  · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hs (minpoly.aeval _ _)
  · rw [Polynomial.map_map, ← hq, ← Polynomial.map_map, Polynomial.eval_map_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]

theorem sec_equiv (o : Om l →+* Per.BdRp l) (ho : IsSec o) (g : Per.Gq l) (x : Om l) :
    Per.σDp g (o x) = o (g x) := by
  have h : IsSec (((Per.σDp g).comp o).comp (g.symm : Om l →+* Om l)) := by
    constructor
    · intro x
      change Per.θD l (Per.σDp g (o (g.symm x))) = _
      rw [(GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2, ho.th, GlobalTheory.RingBasics.σC_coe, AlgEquiv.apply_symm_apply]
    · intro z
      change Per.σDp g (o (g.symm (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])))) = _
      rw [AlgEquiv.commutes, ho.z, sigDp_aDp, sigA_zA]
  have := RingHom.congr_fun (sec_uniq o ho _ h) (g x)
  rw [← this]
  change _ = Per.σDp g (o (g.symm (g x)))
  rw [AlgEquiv.symm_apply_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) :=
  fun _ _ o ho => ⟨sec_root o ho, sec_uniq o ho, sec_equiv o ho⟩

end GlobalTheory.MemLoc.SecUniq
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem adjoin_dividedPowers_iff_span {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (P : R → Prop) (hP : ∀ a, P a ↔ ξ ∣ a) (s : A) :
    s ∈ Algebra.adjoin R {y : A | ∃ x : R, P x ∧ ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A x ^ n} ↔
      s ∈ Submodule.span R {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} := by
  set S : Set A := {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} with hS
  have hγ : ∀ n : ℕ, ∃ g : A, ((n.factorial : ℕ) : A) * g = algebraMap R A ξ ^ n := fun n => by
    obtain ⟨u, hu'⟩ := (hu n).exists_right_inv
    exact ⟨u * algebraMap R A ξ ^ n, by rw [← mul_assoc, hu', one_mul]⟩
  have hone : (1 : A) ∈ Submodule.span R S := Submodule.subset_span ⟨0, by simp⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S := by
    rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    obtain ⟨g, hg⟩ := hγ (m + n)
    have hf : (((m + n).factorial : ℕ) : A) =
        (((m + n).choose n : ℕ) : A) * (m.factorial : ℕ) * (n.factorial : ℕ) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial m n]; push_cast; ring
    have : x * y = ((m + n).choose n : R) • g := by
      refine ((hu m).mul (hu n)).mul_left_cancel ?_
      rw [Algebra.smul_def, map_natCast]
      rw [hf, pow_add, ← hm, ← hn] at hg
      linear_combination -hg
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, hg⟩)
  constructor
  · intro hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨x, hx, n, hn⟩ := hy
      obtain ⟨a, rfl⟩ := (hP x).1 hx
      obtain ⟨g, hg⟩ := hγ n
      have : y = (a ^ n) • g := by
        refine (hu n).mul_left_cancel ?_
        rw [hn, Algebra.smul_def, map_mul, mul_pow, ← hg, map_pow]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hg⟩)
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ hone
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_le.2 ?_ this
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
  · intro hs
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R _))).2 ?_ hs
    rintro y ⟨n, hn⟩
    exact Algebra.subset_adjoin ⟨ξ, (hP ξ).2 dvd_rfl, n, hn⟩

theorem mem_Acris0_iff_span : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l,
    s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  intro l _ e he s
  refine Iff.trans ?_ (adjoin_dividedPowers_iff_span (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (xi e)
    (fun a => Per.θ l a = 0) (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he) s)
  constructor
  · intro hs
    refine (?_ : Per.Acris0 l ≤ _) hs
    refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ fun x n y hx hy => ?_
    exact Algebra.subset_adjoin ⟨x, hx, n, hy⟩
  · intro hs
    refine Algebra.adjoin_le (S := Per.Acris0 l) ?_ hs
    rintro y ⟨x, hx, n, hy⟩
    exact GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n y hx hy

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem exists_isTiltOf (c : Om l) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : c ^ m = 1) :
    ∃ xb : Per.Fl l, IsTiltOf c m xb := by
  have hcC : (c : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hc
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(c : ℂ_[l])‖ = 1 := by
    have := congrArg norm hcC
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  let C : Per.OC l := ⟨(c : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩
  have hC : C ^ m = 1 := Subtype.ext (by simpa using hcC)
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (Nat.totient m - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hcop
  let y : ℕ → Per.OC l := fun k => C ^ (a ^ k)
  have hy : ∀ k, y (k + 1) ^ l = y k := by
    intro k
    simp only [y]
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [pow_succ, mul_assoc]
    simpa using ha.mul_left (a ^ k)
  have hy0 : ∀ k, y k ^ (l ^ k) = C := by
    intro k
    induction k with
    | zero => simp [y]
    | succ k ih => rw [pow_succ', pow_mul, hy, ih]
  refine ⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (Per.OC l) l) l), fun k => ⟨y k, ?_, ?_, rfl⟩⟩
  · rw [← map_pow, hy]
  · have := congrArg Subtype.val (hy0 k)
    simpa using this
  · simp only [y]
    rw [← pow_mul, mul_comm, pow_mul, hC, one_pow]

theorem IsTiltOf.pow_eq_one {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) : xb ^ m = 1 := by
  refine Perfection.ext fun k => ?_
  obtain ⟨y, -, h2, h3⟩ := h k
  change PreTilt.coeff k (xb ^ m) = PreTilt.coeff k (1 : Per.Fl l)
  rw [map_pow, map_one, h3, ← map_pow, h2, map_one]

theorem IsTiltOf.untilt_eq {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) :
    ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
  obtain ⟨y0, h0, -, -⟩ := h 0
  rw [pow_zero, pow_one] at h0
  have : xb.untilt = y0 := by
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun n => ?_
    obtain ⟨y, h1, -, h3⟩ := h n
    refine ⟨y, h3.symm, ?_⟩
    have : y ^ l ^ n = y0 := Subtype.ext (by simpa [h0] using h1)
    rw [this]
  rw [this, h0]

theorem rootOfUnity_teichmuller : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  intro l _ o ho c m hm hl hc
  refine ⟨exists_isTiltOf c m hm hl hc, fun xb h => ⟨IsTiltOf.pow_eq_one h, IsTiltOf.untilt_eq h, ?_⟩⟩
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have h1 : aDp l (Per.tm xb) ^ m = 1 := by
    rw [← map_pow, ← map_pow, IsTiltOf.pow_eq_one h, map_one, map_one]
  have h2 : o c ^ m = 1 := by rw [← map_pow, hc, map_one]
  have t1 : Per.θD l (aDp l (Per.tm xb)) = (c : ℂ_[l]) := by
    rw [hθ, WittVector.fontaineTheta_teichmuller, IsTiltOf.untilt_eq h]
  have t2 : Per.θD l (o c) = (c : ℂ_[l]) := ho.th c
  generalize aDp l (Per.tm xb) = y at h1 t1 ⊢
  have hc0 : (c : ℂ_[l]) ≠ 0 := by
    intro h0
    have := congrArg (Per.θD l) h2
    rw [map_pow, map_one, t2, h0, zero_pow hm.ne'] at this
    exact zero_ne_one this
  have hg := (Commute.all y (o c)).geom_sum₂_mul m
  rw [h1, h2, sub_self] at hg
  have hS : IsUnit (∑ i ∈ Finset.range m, y ^ i * o c ^ (m - 1 - i)) := by
    apply hu

    rw [map_sum]
    simp only [map_mul, map_pow, t1, t2]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hc0)
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 hg)

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_frobenius_fixed_eq_padicInt : ∀ (l : ℕ) [Fact l.Prime], ∀ x : Per.Acris l, phiA l x = x → ∃ z : ℤ_[l], x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) := by
  first | exact @GlobalTheory.MemLoc.phi_fixed_eq_padicInt | exact GlobalTheory.MemLoc.phi_fixed_eq_padicInt | (intros; apply GlobalTheory.MemLoc.phi_fixed_eq_padicInt <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  first | exact @GlobalTheory.MemLoc.fil_dense | exact GlobalTheory.MemLoc.fil_dense | (intros; apply GlobalTheory.MemLoc.fil_dense <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  first | exact @GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | exact GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi | (intros; apply GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, (∀ n : ℕ, Per.θ l ((Per.φA l)^[n] a) = 0) → mu e ∣ a := by
  first | exact @GlobalTheory.MemLoc.mu_dvd_of_theta_frob | exact GlobalTheory.MemLoc.mu_dvd_of_theta_frob | (intros; apply GlobalTheory.MemLoc.mu_dvd_of_theta_frob <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.idele_character_trivial_on_local_units : ∀ (L : Type) [Field L] [NumberField L] (ψ : Neutral.B1.Ideles L →* ℂˣ), Continuous ψ → ∀ a : Neutral.B1.Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (Neutral.B1.localIdele L v x) = 1) → ψ a = 1 := by
  first | exact @GlobalTheory.Mem.LocTriv.eq_one_of_local | exact GlobalTheory.Mem.LocTriv.eq_one_of_local | (intros; apply GlobalTheory.Mem.LocTriv.eq_one_of_local <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

def canonList {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : List (GlobalTheory.GLq.Pc g) :=
  (List.finRange s).map fun c =>
    ⟨Fintype.card {i // b i = c}, fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩

theorem canonList_length {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : (canonList b lam).length = s := by
  simp [canonList]

end GlobalTheory.SerCmp
end
end
