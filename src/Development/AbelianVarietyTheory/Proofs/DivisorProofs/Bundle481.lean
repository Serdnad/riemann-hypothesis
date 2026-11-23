module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Formalism.FormalDegreeBessel.StatementDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti
public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.EulerLocVol

noncomputable def invPowHom (i : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ i)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

theorem inv_zeta_le_prod_primes : ∀ (i : ℕ), 2 ≤ i → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := by
  intro i hi P hP
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hs' : Summable (invPowHom i) := by
    have := Real.summable_one_div_nat_pow.2 (by omega : 1 < i)
    simpa [invPowHom] using this
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invPowHom i p‖ < 1 := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt P).2
  have hfilt : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  rw [hfilt] at hE
  have hfac : ∀ p ∈ P, 0 < 1 - ((p : ℝ) ^ i)⁻¹ := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast (hP p hp).one_lt) (by omega)
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1)
  have hpos : 0 < ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := Finset.prod_pos hfac
  have hle : ∏ p ∈ P, (1 - invPowHom i p)⁻¹ ≤ ∑' n : ℕ, invPowHom i n := by
    rw [← hE.tsum_eq]
    exact Summable.tsum_subtype_le (⇑(invPowHom i)) _ (fun n => by change 0 ≤ ((n : ℝ) ^ i)⁻¹; positivity) hs'
  have hz : ∑' n : ℕ, invPowHom i n = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    rw [hs'.tsum_eq_zero_add]
    simp [invPowHom, show i ≠ 0 by omega]
  rw [hz, Finset.prod_inv_distrib] at hle
  simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  calc (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ((∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hpos) hle
    _ = _ := inv_inv _

theorem le_locFactor_of_not_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    ¬ (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  intro E _ _ _ r v hr hnp
  let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold locFactor resOrder
  rw [if_neg hnp]
  have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

theorem tprod_locFactor_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧
      (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, g (Ideal.absNorm v.asIdeal) ≤ locFactor E r v := by
    intro v
    by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
    · exact GlobalTheory.T.local_factor_lower_bound E r v (by omega) hp
    · exact le_locFactor_of_not_prime E r v (by omega) hp
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, locFactor E r v := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, locFactor E r v := by
      refine Finset.prod_le_prod₀ (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => (g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)).trans (hloc v)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod₀ (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
      refine inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
      _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
      _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
      _ ≤ _ := s3
      _ = _ := s2.symm
      _ ≤ _ := s1
  have hle : (Z ^ fdeg E)⁻¹ ≤ ∏' v, locFactor E r v :=
    ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)
  have hpos : 0 < (Z ^ fdeg E)⁻¹ := by positivity
  refine ⟨hpos.trans_le hle, ?_⟩
  calc (∏' v, locFactor E r v)⁻¹ ≤ ((Z ^ fdeg E)⁻¹)⁻¹ := inv_anti₀ hpos hle
    _ = Z ^ fdeg E := inv_inv _

end GlobalTheory.EulerLocVol
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

namespace CocycleSum

theorem four {M N : Type} [CommMonoid M] [AddCommGroup N] (c : M → M → N)
    (h : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (hs : ∀ x y, c x y = c y x)
    (a b a' b' : M) :
    c (a * b) (a' * b') = c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b') := by
  have h1 := h a b (a' * b')
  have h2 := h a a' (b * b')
  have h3 := h a' b' b
  rw [show b * (a' * b') = a' * (b * b') from mul_left_comm _ _ _] at h1
  rw [show b' * b = b * b' from mul_comm _ _, hs (a' * b') b, hs b' b] at h3
  rw [← sub_eq_zero]
  have e : c (a * b) (a' * b') - (c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b')) =
      -(c b (a' * b') - c (a * b) (a' * b') + c a (a' * (b * b')) - c a b) +
      (c a' (b * b') - c (a * a') (b * b') + c a (a' * (b * b')) - c a a') -
      (c b b' - c b (a' * b') + c a' (b * b') - c a' b') := by abel
  rw [e, h1, h2, h3]
  simp

variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]

def val (x y : WithConv (A →ₐ[R] X)) : A ⊗[R] A →ₐ[R] X :=
  Algebra.TensorProduct.lift x.ofConv y.ofConv fun _ _ => .all ..

@[simp] theorem val_tmul (x y : WithConv (A →ₐ[R] X)) (a b : A) :
    val x y (a ⊗ₜ b) = x.ofConv a * y.ofConv b := rfl

theorem mul_apply (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by
  rw [val]
  exact AlgHom.convMul_apply x y a

theorem lift_cobTwo (x y z : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..) (cobTwo R A c) =
      val y z c - val (x * y) z c + val x (y * z) c - val x y c := by
  have hA : ∀ (t : A ⊗[R] A) (b : A),
      Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..)
        (TensorProduct.assoc R A A A (t ⊗ₜ b)) = val x y t * z.ofConv b := by
    intro t b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' => simp [mul_assoc]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv, add_mul]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [cobTwo_apply]
    simp only [map_sub, map_add (f := _), TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.flip_apply, Algebra.TensorProduct.lift_tmul, val_tmul, hA,
      mul_apply, map_one, one_mul, mul_one]
  | add u v hu hv =>
    simp only [map_add (f := _), hu, hv]
    abel

theorem val_comm (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val x y (TensorProduct.comm R A A c) = val y x c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.comm_tmul, val_tmul, val_tmul, mul_comm]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem val_push {Y : Type} [CommRing Y] [Algebra R Y] (u : X →ₐ[R] Y)
    (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val (ptsPush A u x) (ptsPush A u y) c = u (val x y c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, map_mul]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

variable {B : Type} [CommRing B] [Bialgebra R B]

theorem val_include (x y : WithConv (A →ₐ[R] B)) (c : A ⊗[R] A) :
    val (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) x)
      (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) y) c =
      TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem include_mul (f : A →ₐc[R] B) :
    ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) *
      ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) =
      ptsPush A (comulAlgHom R B) (toConv (f : A →ₐ[R] B)) := by
  apply WithConv.ext
  ext a
  rw [mul_apply, val_include]
  simp only [ptsPush_ofConv, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  exact CoalgHomClass.map_comp_comul_apply f a

end CocycleSum


open CocycleSum in
theorem pullTwo_convMul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A]
    [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) :
    pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c +
      cobOne R B (LinearMap.mul' R B
        (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  obtain ⟨hc2, hcs⟩ := mem_symCocycles.1 hc
  have hv : ∀ (x y : WithConv (A →ₐ[R] B)) (t : A ⊗[R] A), val x y t =
      LinearMap.mul' R B (TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap t) := by
    intro x y t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have key := four (M := WithConv (A →ₐ[R] B ⊗[R] B)) (fun x y => val x y c)
    (fun x y z => (lift_cobTwo x y z c).symm.trans (by rw [hc2, map_zero]))
    (fun x y => by rw [← val_comm, hcs])
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
  rw [← map_mul (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)),
    ← map_mul (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)),
    include_mul f, include_mul g, val_include, val_include, val_include, val_push, val_push,
    val_push] at key
  have hl : ∀ h : A →ₐc[R] B, (h : A →ₗ[R] B) = (h : A →ₐ[R] B).toLinearMap := fun _ => rfl
  have hfg : ((toConv f * toConv g).ofConv : A →ₐ[R] B) =
      (toConv (f : A →ₐ[R] B) * toConv (g : A →ₐ[R] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (toConv f) (toConv g))
  have hv' : LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c) =
      val (toConv (f : A →ₐ[R] B)) (toConv (g : A →ₐ[R] B)) c := by
    rw [hv, hl, hl]
  unfold pullbackTwo
  rw [hl, hfg, key, cobOne_apply, hv', Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, hl, hl]
  rfl

end PDiv

end GlobalTheory
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEG

def GapNum : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ),
    (∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j) →
    Formalism.QuantumDeterminants.IsHCParam (fun a => (lam a : ℝ)) ∧ StdGap ε (fun a => (lam a : ℝ)) ∧ Gap3 ε (fun a => (lam a : ℝ)) ∧
      ∃ h : ℝ, GapAtLeast ε (fun a => (lam a : ℝ)) h ∧ thrStar ε < h

end GlobalTheory.PsCo.PcEG

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG (GapNum)

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end

section

namespace GlobalTheory

open MeasureTheory

theorem unitarySigns_haar_isMulRightInvariant :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : MeasureTheory.Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
      μ.IsMulRightInvariant := by
  intro n ε μ _
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  infer_instance

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

theorem _root_.GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  first | exact @GlobalTheory.RatFix.ratfix | exact GlobalTheory.RatFix.ratfix | (intros; apply GlobalTheory.RatFix.ratfix <;> assumption)
end
