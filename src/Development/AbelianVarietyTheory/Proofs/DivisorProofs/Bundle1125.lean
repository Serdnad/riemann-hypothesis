module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCS

theorem norm_sum_sq_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (X lam : Fin N → ℂ) :
    ‖∑ j, X j * lam j‖ ^ 2 ≤ (∑ i, ‖(A⁻¹.mulVec X) i‖ ^ 2) * ∑ a, ‖∑ m, A m a * lam m‖ ^ 2 := by
  set Y := A⁻¹.mulVec X with hY
  have hX : X = A.mulVec Y := by
    rw [hY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
  have e : ∑ j, X j * lam j = ∑ a, Y a * ∑ m, A m a * lam m := by
    rw [hX]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  calc ‖∑ a, Y a * ∑ m, A m a * lam m‖ ^ 2 ≤ (∑ a, ‖Y a‖ * ‖∑ m, A m a * lam m‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
        simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end GlobalTheory.FrameCS


open GlobalTheory.FrameCS in
theorem GlobalTheory.frame_semilinear_sq_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  intro K V _ _ _ _ _ _ Nm W N n b g A c gw σ ℓ hF hg hc hℓ x
  set lam : Fin N → ℂ := fun j => ∑ k, σ (c k j) * ℓ (gw k) with hlam

  have h2 : ∀ k, ℓ (gw k) = ∑ j, σ (g j k) * lam j := by
    intro k
    set e : Fin n → K := fun l => ∑ j, g j k * c l j with he
    have hexp : (gw k : V) = ∑ l, e l • (gw l : V) := by
      rw [hg k]
      simp_rw [hc, he, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (Finset.univ.image e)
    choose β hβ using fun l => hd _ (Finset.mem_image_of_mem e (Finset.mem_univ l))
    have hβ' : ∀ l, ((β l : 𝓞 K) : K) = ((d : 𝓞 K) : K) * e l := fun l => by
      rw [← Algebra.smul_def, ← hβ l]
    have hx1 : (((d : 𝓞 K) • gw k : W) : V) = ∑ l, β l • (gw l : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul K, hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← algebraMap_smul K (β l), smul_smul]
      congr 1
      exact (hβ' l).symm
    have hx2 : (((d : 𝓞 K) • gw k : W) : V) = ∑ _i : Fin 1, (d : 𝓞 K) • (gw k : V) := by
      simp
    have e1 := hℓ n β gw _ hx1
    have e2 := hℓ 1 (fun _ => (d : 𝓞 K)) (fun _ => gw k) _ hx2
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    have hd0 : σ ((d : 𝓞 K) : K) ≠ 0 := by
      rw [map_ne_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero d
    apply mul_left_cancel₀ hd0
    rw [← e2, e1]
    simp only [hβ', map_mul, hlam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_

    simp only [he, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hxmem : (x : V) ∈ Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) := by
    have := hF.span
    have hfun : (fun k => ∑ j, g j k • b j) = fun k => (gw k : V) := funext fun k => (hg k).symm
    rw [hfun] at this
    rw [this]; exact x.2
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hxmem
  have h3 : ℓ x = ∑ j, σ (b.repr x j) * lam j := by
    rw [hℓ n β gw x hβ.symm]
    have hr : ∀ j, b.repr x j = ∑ k, (β k : K) * g j k := by
      intro j
      have hk : ∀ k, β k • (gw k : V) = ∑ j, ((β k : K) * g j k) • b j := by
        intro k
        rw [← algebraMap_smul K, hg k, Finset.smul_sum]
        simp_rw [smul_smul]
      rw [← hβ, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      rw [Module.Basis.repr_sum_self]

    simp only [hr, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hN : Nm σ x ^ 2 = ∑ i, ‖((A σ)⁻¹.mulVec fun j => σ (b.repr x j)) i‖ ^ 2 := by
    rw [← hF.norm σ x, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have hu : ∀ a, ∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k) = ∑ m, A σ m a * lam m := by
    intro a
    simp only [hlam, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [hu, hN, h3]
  exact norm_sum_sq_le (A σ) (hF.herm σ) _ lam
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointLow

set_option autoImplicit false in
open MvPolynomial in
private lemma natDegree_aeval_le_totalDegree_of_natDegree_le_one {R S σ : Type} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) (s : σ → Polynomial S) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (MvPolynomial.aeval s p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]

  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  have h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add, Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hs i)


set_option autoImplicit false in
open MvPolynomial in
theorem _root_.GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  intro K _ _ N δ y j f hyj hf
  classical
  set E := IntermediateField.adjoin K (Set.range y) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [← AlgHom.card K E (AlgebraicClosure K)]
  let yE : Fin N → E := fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩
  let pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K := fun σ k => σ (yE k)
  have hpj : ∀ σ, pt σ j = 1 := by
    intro σ
    have : yE j = 1 := Subtype.ext hyj
    simp only [pt, this, map_one]
  have hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0 := by
    intro σ g hg
    have hy := _root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg
    have hE0 : MvPolynomial.aeval yE g = 0 := by
      apply Subtype.ext
      have := MvPolynomial.comp_aeval_apply yE E.val g
      show E.val (MvPolynomial.aeval yE g) = E.val 0
      rw [this, map_zero]
      exact hy
    have := MvPolynomial.comp_aeval_apply yE σ g
    rw [hE0, map_zero] at this
    exact this.symm
  have hinj : Function.Injective pt := by
    intro σ τ h
    refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    exact congrFun h k
  set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ
  have hfΩ0 : fΩ ≠ 0 := by
    intro h
    exact hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective
      (by rw [← hfΩ, h, map_zero]))
  let lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) →
      MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K) :=
    fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)
  have hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K),
      eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k := by
    intro σ τ a

    simp only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]
  set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) =>
    st.1 ≠ st.2 with hpairs
  set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)
    have hne : st.1 ≠ st.2 := (Finset.mem_filter.mp hst).2
    have hpne : pt st.1 ≠ pt st.2 := fun h => hne (hinj h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hpne
    intro h0
    have := congrArg (eval (Pi.single (0, k) 1)) h0
    rw [hlin_eval, map_zero] at this
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact hk (sub_eq_zero.mp this)
  obtain ⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  have hfa : eval a fΩ ≠ 0 := fun h => ha (by rw [hQ, eval_mul, h, zero_mul])
  let c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun σ => ∑ k, a (0, k) * pt σ k
  have hdist : Function.Injective c := by
    intro σ τ h
    by_contra hne
    apply ha
    rw [hQ, eval_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)
    rw [hlin_eval]
    exact sub_eq_zero.mpr h
  let s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K) :=
    fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0
  set g := MvPolynomial.aeval s f with hg
  have heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f := by
    intro t
    have := MvPolynomial.comp_aeval_apply s
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f
    rw [hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) =
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K)
        (MvPolynomial.aeval s f) from rfl, this]
    refine congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)
    simp only [s]
    split_ifs <;> simp
  have hg0 : g ≠ 0 := by
    intro h
    have := heval 0
    rw [h, Polynomial.eval_zero] at this
    have h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a := by
      funext ik; split_ifs <;> simp
    rw [h2] at this
    apply hfa
    rw [hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this.symm
  have hroot : ∀ σ, g.eval (-c σ) = 0 := by
    intro σ
    rw [heval]
    refine (hf.zero_iff _).mpr
      ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hpj σ, mul_one]
    simp [c]
  have hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hg0]
      exact hroot σ
    · intro σ _ τ _ h
      exact hdist (neg_injective h)
  have hhom := ((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp
    hf.homog).isHomogeneous)
  have htot : f.totalDegree = δ := by
    rw [hhom.totalDegree hf.ne_zero]
    simp
  calc Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := hcard
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ f.totalDegree := natDegree_aeval_le_totalDegree_of_natDegree_le_one f s fun ik => by
        simp only [s]
        split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        · simp
    _ = δ := htot

end GlobalTheory.CompHt.PointLow
end
end

section

set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
end

section

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal Topology

namespace GlobalTheory.GrowthShift

theorem eventually_mul_inv_pow_le (D e : ℕ) {a : ℝ≥0∞} (ha : a < 1) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ≥0∞) ^ D)⁻¹ ≤ (((k + e : ℕ) : ℝ≥0∞) ^ D)⁻¹ := by
  lift a to NNReal using ha.ne_top
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) / (k + (e : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (e : ℝ)).pow D
  filter_upwards [h1.eventually (lt_mem_nhds ha'), eventually_gt_atTop 0] with k hk hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  have hke : (0 : ℝ) < ((k : ℝ) + e) ^ D := by positivity
  rw [div_pow, lt_div_iff₀ hke] at hk
  have h2 : (a : ℝ≥0∞) * ((k + e : ℕ) : ℝ≥0∞) ^ D ≤ (k : ℝ≥0∞) ^ D := by
    have h3 : a * ((k + e : ℕ) : NNReal) ^ D ≤ (k : NNReal) ^ D := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hk.le
    exact_mod_cast h3
  have n0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hk0.ne')
  have nt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv, ENNReal.div_le_iff n0 nt, one_mul]
  exact h2

theorem growth_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  intro D e r
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rw [growth, growth, ← ENNReal.limsup_const_mul_of_ne_top ha.ne_top,
    ← Filter.limsup_nat_add (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) e]
  refine limsup_le_limsup ((eventually_mul_inv_pow_le D e ha).mono fun k hk => ?_)
  simp only [div_eq_mul_inv]
  rw [mul_left_comm]
  exact mul_le_mul_right hk _

end GlobalTheory.GrowthShift
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.CompHt

theorem finrank_quotPiece_coneIdeal_eq_finrank_map {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) (n : ℕ) :
    Module.finrank K (quotPiece (coneIdeal K y) n) =
      Module.finrank K ((homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap) := by
  have e1 := finrank_quotPiece_add (coneIdeal K y) n
  have e2 := GradedHilbert.finrank_map_add_finrank_inf_ker
    (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)
  have e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _)
      = homogeneousSubmodule (Fin N) K n ⊓
        LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
    ext g
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule,
      LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩
  rw [e3] at e1
  omega

theorem aeval_mem_map_homogeneousSubmodule {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) {j : Fin N} (hj : y j = 1) (g : MvPolynomial (Fin N) K) {n : ℕ}
    (hn : g.totalDegree ≤ n) :
    aeval y g ∈ (homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by

  rw [← sum_homogeneousComponent g, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := by
    have := Finset.mem_range.1 hi
    omega
  refine ⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩
  have := (homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))
  rw [one_mul, Nat.add_sub_cancel' hi'] at this
  exact this

theorem idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin (K : Type) [Field K] (N : ℕ)
    (y : Fin N → AlgebraicClosure K) (j : Fin N) (hj : y j = 1) :
    GlobalTheory.idealHilbertPoly (coneIdeal K y) =
      Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  have halg : ∀ x ∈ Set.range y, IsAlgebraic K x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  set S : Submodule K (AlgebraicClosure K) :=
    Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS
  have hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x := by
    intro x
    rw [hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hfin : Module.Finite K S := ‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap := by
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (hs ▸ Submodule.subset_span hx)
    filter_upwards [eventually_ge_atTop g.totalDegree] with n hn
    exact aeval_mem_map_homogeneousSubmodule y hj g hn
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev]
    with n h1 h2
  have hW : (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S := by
    apply le_antisymm
    · rintro _ ⟨g, -, rfl⟩
      exact (hmem _).2 ⟨g, rfl⟩
    · rw [← hs, Submodule.span_le]
      exact fun x hx => h2 x hx
  rw [← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]
  rfl

end GlobalTheory.CompHt
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.vanishes_on_etale_neighbourhood : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.exists_etale_kill_of_indEt) | (exact GlobalTheory.EtC.exists_etale_kill_of_indEt) | (intros; apply GlobalTheory.EtC.exists_etale_kill_of_indEt  <;> assumption)
end
