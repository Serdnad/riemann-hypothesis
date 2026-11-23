module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem coeff1_mul {σ E : Type} [CommRing E] (j : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single j 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single j 1) g +
        MvPowerSeries.coeff (Finsupp.single j 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
    Finset.Nat.antidiagonal_succ]
  simp

private theorem exists_den {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ a, ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
  classical
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (RingHom.ker x) : (RingHom.ker x).FG)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) T D
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h0 : D 0 = 0 := by simpa using halg 0
  have key : ∀ a ∈ Submodule.span R (T : Set R), ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨o, ho⟩ := hc a ha
      exact ⟨o, by rw [ho, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp [h0]⟩
    | add a b _ _ ha hb =>
      obtain ⟨o, ho⟩ := ha
      obtain ⟨o', ho'⟩ := hb
      exact ⟨o + o', by rw [map_add (f := _), ho, ho', hadd, mul_add]⟩
    | smul r a ha' ha =>
      obtain ⟨o, ho⟩ := ha
      rw [hT] at ha'
      have hx : x a = 0 := ha'
      exact ⟨x r * o, by rw [map_mul, ho, smul_eq_mul, hmul, hx, map_zero]; ring⟩
  intro a
  have hm : a - algebraMap O R (x a) ∈ RingHom.ker x := by
    simp [RingHom.mem_ker]
  rw [← hT] at hm
  obtain ⟨o, ho⟩ := key _ hm
  refine ⟨o, ?_⟩
  have : D a = D (a - algebraMap O R (x a)) := by
    conv_lhs => rw [← sub_add_cancel a (algebraMap O R (x a))]
    rw [hadd, halg, add_zero]
  rw [this, ho]

private def dualHom {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (d : R → O)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = x a * d b + d a * x b)
    (halg : ∀ o, d (algebraMap O R o) = 0) : R →ₐ[O] DualNumber O where
  toFun a := TrivSqZeroExt.inl (x a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have : d 1 = 0 := by simpa using halg 1
    ext <;> simp [this]
  map_mul' a b := by
    ext <;> simp [hmul, mul_comm]
  map_zero' := by
    have : d 0 = 0 := by simpa using halg 0
    ext <;> simp [this]
  map_add' a b := by
    ext <;> simp [hadd]
  commutes' o := by
    ext <;> simp [halg, TrivSqZeroExt.algebraMap_eq_inl]

private theorem der_zero {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) (S : Type) (e : S → R)
    (hsep : ∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f')
    (hs : ∀ s, D (e s) = 0) (a : R) : D a = 0 := by
  obtain ⟨c, hc, h⟩ := exists_den x D hadd hmul halg
  choose d hd using h
  have inj := IsFractionRing.injective O E
  have hc' : algebraMap O E c ≠ 0 := fun h => hc (inj (by rw [h, map_zero]))
  have := hsep
    (dualHom x d (fun a b => inj (by rw [map_add (f := _), hd, hd, hd, hadd, mul_add]))
      (fun a b => inj (by rw [map_add (f := _), map_mul, map_mul, hd, hd, hd, hmul]; ring))
      (fun o => inj (by rw [hd, halg, mul_zero, map_zero])))
    (dualHom x (fun _ => 0) (by simp) (by simp) (by simp))
    (fun s => by
      have : d (e s) = 0 := inj (by rw [hd, hs, mul_zero, map_zero])
      ext <;> simp [dualHom, this])
  have h3 : d a = 0 := by
    simpa [dualHom] using congrArg TrivSqZeroExt.snd (DFunLike.congr_fun this a)
  have h4 := hd a
  rw [h3, map_zero] at h4
  exact (mul_eq_zero.mp h4.symm).resolve_left hc'

theorem UpperTheory.V.Loc.chartSpan :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (S : Type) (e : S → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f') → ∃ u : Fin n → S, Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (e (u i)))) = ⊤ := by
  intro O R E _ _ _ _ _ _ _ _ n I x φ S e h hsep
  classical
  let L : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E) :=
    LinearMap.pi fun j => MvPowerSeries.coeff (Finsupp.single j 1)
  have hL : ∀ f j, L f j = MvPowerSeries.coeff (Finsupp.single j 1) f := fun _ _ => rfl
  have hLmul : ∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f := by
    intro f g
    funext j
    simp only [hL, coeff1_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, L f = 0 := by
    have hm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E), MvPowerSeries.constantCoeff f = 0 := by
      intro f hf
      by_contra hne
      exact hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (Ne.isUnit hne))
    intro f hf
    rw [pow_two] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [hLmul, hm a ha, hm b hb]; simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have hspan : Submodule.span E (Set.range fun s => L (φ (e s))) = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hD := der_zero x (fun a => lam (L (φ a))) (fun a b => by simp)
      (fun a b => by
        rw [map_mul, hLmul, h.const, h.const]
        simp only [map_add (f := _), map_smul, smul_eq_mul]
        ring)
      (fun o => by
        have : L (φ (algebraMap O R o)) = 0 := by
          funext j
          rw [AlgHom.commutes, hL, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp
        rw [this, map_zero])
      S e hsep (fun s => hker (Submodule.subset_span ⟨s, rfl⟩))
    apply hlam
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    obtain ⟨a, c, hc, hca⟩ := h.dense 2 (MvPowerSeries.X j)
    have h1 := hm2 _ hca
    have hX : L (MvPowerSeries.X j) = Pi.basisFun E (Fin n) j := by
      funext i
      rw [hL, MvPowerSeries.coeff_index_single_X]
      simp [Pi.single_apply]
    rw [map_sub, ← algebraMap_smul E c, map_smul, hX, sub_eq_zero] at h1
    have h2 := hD a
    simp only [← h1, map_smul, smul_eq_mul] at h2
    have hc' : algebraMap O E c ≠ 0 := fun h => hc (IsFractionRing.injective O E (by rw [h, map_zero]))
    exact (mul_eq_zero.mp h2).resolve_left hc'
  obtain ⟨b, hb, hbs, hbi⟩ := exists_linearIndependent E (Set.range fun s => L (φ (e s)))
  rw [hspan] at hbs
  have hfin : b.Finite := hbi.set_finite_of_isNoetherian
  haveI := hfin.fintype
  let B : Module.Basis b E (Fin n → E) := Module.Basis.mk hbi (by simp [hbs])
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis B]; simp
  let q : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose u hu using fun i : Fin n => hb (q i).2
  refine ⟨u, ?_⟩
  rw [eq_top_iff, ← hbs]
  refine Submodule.span_mono fun v hv => ⟨q.symm ⟨v, hv⟩, ?_⟩
  have := hu (q.symm ⟨v, hv⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this
end

section

open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem cg_max {E σ : Type} [Field E] : maximalIdeal (MvPowerSeries σ E) = GlobalTheory.germIdeal σ E := by
  ext g
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  simp [GlobalTheory.germIdeal, RingHom.mem_ker]

private theorem cg_ext {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    [IsFractionRing O E] {n : ℕ} {I : Ideal R} {x : R →ₐ[O] O} {φ : R →ₐ[O] MvPowerSeries (Fin n) E}
    (hφ : UpperTheory.V.Loc.IsCompl I x φ) {z : Fin n → R} (hz : ∀ i, φ (z i) = MvPowerSeries.X i)
    (α β : R →ₐ[O] MvPowerSeries (Fin n) E)
    (hα : ∀ a, MvPowerSeries.constantCoeff (α a) = algebraMap O E (x a))
    (hβ : ∀ a, MvPowerSeries.constantCoeff (β a) = algebraMap O E (x a))
    (hI : ∀ a ∈ I, α a = β a) (hzz : ∀ i, α (z i) = β (z i)) (a : R) : α a = β a := by
  classical
  have hm := cg_max (E := E) (σ := Fin n)
  have hA : ∀ (γ : R →ₐ[O] MvPowerSeries (Fin n) E),
      (∀ a, MvPowerSeries.constantCoeff (γ a) = algebraMap O E (x a)) →
      ∀ N, ∀ b ∈ RingHom.ker x ^ N, γ b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro γ hγ N b hb
    have h1 : Ideal.map γ (RingHom.ker x) ≤ GlobalTheory.germIdeal (Fin n) E := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hγ, RingHom.mem_ker.mp hc, map_zero]
    have h2 : Ideal.map γ (RingHom.ker x ^ N) ≤ GlobalTheory.germIdeal (Fin n) E ^ N := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' h1 N
    exact h2 (Ideal.mem_map_of_mem γ hb)
  have hB : ∀ N, ∀ b ∈ RingHom.ker x ^ N ⊔ I, α b - β b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    have hv0 : α v - β v = 0 := sub_eq_zero.mpr (hI v hv)
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm, hv0, add_zero]
    exact Ideal.sub_mem _ (hA α hα N u hu) (hA β hβ N u hu)
  have hC : ∀ p : MvPolynomial (Fin n) O, α (MvPolynomial.aeval z p) = β (MvPolynomial.aeval z p) := by
    intro p
    have hcomp : α.comp (MvPolynomial.aeval z) = β.comp (MvPolynomial.aeval z) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hzz i]
    exact AlgHom.congr_fun hcomp p
  have hP : ∀ p : MvPolynomial (Fin n) O, φ (MvPolynomial.aeval z p) =
      ((MvPolynomial.map (algebraMap O E) p : MvPolynomial (Fin n) E) : MvPowerSeries (Fin n) E) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C, AlgHom.commutes, MvPolynomial.map_C, MvPolynomial.coe_C,
        MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, MvPolynomial.coe_add]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, hz i, MvPolynomial.map_X, MvPolynomial.coe_mul,
        MvPolynomial.coe_X]
  have hmain : ∀ N, ∃ e : O, e ≠ 0 ∧ e • (α a - β a) ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N
    set s := (Finsupp.finite_of_degree_lt (σ := Fin n) N).toFinset with hs
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
      (fun d => MvPowerSeries.coeff d (φ a))
    have hb' : ∀ d ∈ s, ∃ k : O, algebraMap O E k = (b : O) • MvPowerSeries.coeff d (φ a) :=
      fun d hd => RingHom.mem_rangeS.mp (hb d hd)
    choose! k hk using hb'
    set p : MvPolynomial (Fin n) O := ∑ d ∈ s, MvPolynomial.monomial d (k d) with hp
    set y : R := (b : O) • a - MvPolynomial.aeval z p with hy
    have hφy : φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
      rw [hm, GlobalTheory.mem_germIdeal_pow_iff]
      intro d hd
      have hds : d ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        exact hd
      have hcp : AddMonoidAlgebra.coeff p d = k d := by
        rw [hp, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_monomial]
        rw [Finset.sum_ite_eq' s d (fun e => k e), if_pos hds]
      rw [hy, map_sub, map_smul, hP, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_map, hcp,
        hk d hds]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc0, hc⟩ := hφ.inj N y hφy
    refine ⟨c * b, mul_ne_zero hc0 (nonZeroDivisors.ne_zero b.2), ?_⟩
    have heq : α (c • y) - β (c • y) = (c * (b : O)) • (α a - β a) := by
      rw [hy]
      simp only [map_smul, map_sub]
      rw [hC p, ← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, mul_smul]
    rw [← heq]
    exact hB N _ hc
  rw [← sub_eq_zero]
  ext d
  obtain ⟨e, he0, he⟩ := hmain (d.degree + 1)
  rw [GlobalTheory.mem_germIdeal_pow_iff] at he
  have h1 := he d (Nat.lt_succ_self _)
  change e • MvPowerSeries.coeff d (α a - β a) = 0 at h1
  rw [Algebra.smul_def, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).mpr he0)
  · rw [map_zero]
    exact h1

theorem UpperTheory.V.Loc.chartGraded :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R) (w : Fin n → ℤ) (θ : R →ₐ[O] R) (t : Oˣ), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, φ (z i) = MvPowerSeries.X i) → x.comp θ = x → (∀ a ∈ I, θ a ∈ I) → (Function.Injective fun j : ℤ => t ^ j) → (∀ i, θ (z i) = algebraMap O R ((t ^ w i : Oˣ) : O) * z i) → ∀ (j : ℤ) (a : R), θ a = algebraMap O R ((t ^ j : Oˣ) : O) * a → φ a ∈ wtPart E w j := by
  intro O R E _ _ _ _ _ _ _ n I x φ z w θ t hφ hz hxθ hθI hinj hθz j a ha
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin n → E, c = fun i => algebraMap O E ((t ^ w i : Oˣ) : O) := ⟨_, rfl⟩
  have hρC : ∀ e : E, MvPowerSeries.rescale c (MvPowerSeries.C e) = MvPowerSeries.C e := by
    intro e
    ext m
    rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
    split_ifs with hm
    · subst hm
      simp
    · simp
  let β : R →ₐ[O] MvPowerSeries (Fin n) E :=
    AlgHom.mk ((MvPowerSeries.rescale c).comp φ.toRingHom) (fun r => by
      show MvPowerSeries.rescale c (φ (algebraMap O R r)) = _
      rw [AlgHom.commutes, MvPowerSeries.algebraMap_apply, hρC])
  have hβ_apply : ∀ r, β r = MvPowerSeries.rescale c (φ r) := fun r => rfl
  have hker : ∀ r ∈ I, φ r = 0 := by
    intro r hr
    rw [← RingHom.mem_ker, hφ.ker]
    exact hr
  have key := cg_ext hφ hz (φ.comp θ) β
    (by
      intro r
      rw [AlgHom.comp_apply, hφ.const, ← AlgHom.comp_apply, hxθ])
    (by
      intro r
      rw [hβ_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
        Finsupp.prod_zero_index, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const])
    (by
      intro r hr
      rw [AlgHom.comp_apply, hker _ (hθI r hr), hβ_apply, hker r hr, map_zero])
    (by
      intro i
      rw [AlgHom.comp_apply, hθz i, map_mul, AlgHom.commutes, hz i, hβ_apply, hz i,
        MvPowerSeries.algebraMap_apply]
      ext m
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      split_ifs with hm
      · subst hm
        simp [hc]
      · simp) a
  have hθa : φ (θ a) = MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a := by
    rw [ha, map_mul, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
  have key' : MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a = MvPowerSeries.rescale c (φ a) := by
    rw [← hθa]
    exact key
  have hprod : ∀ m : Fin n →₀ ℕ,
      (m.prod fun i k => c i ^ k) = algebraMap O E ((t ^ (Finsupp.weight w m) : Oˣ) : O) := by
    intro m
    rw [hc, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    simp only [← map_pow, ← map_prod, ← Units.val_pow_eq_pow_val, ← Units.coe_prod]
    congr 2
    have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → ℤ), t ^ (∑ i ∈ s, f i) = ∏ i ∈ s, t ^ f i := by
      intro s f
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
    rw [hsum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← zpow_natCast, ← zpow_mul, nsmul_eq_mul, mul_comm]
  change ∀ (m : Fin n →₀ ℕ), (Finsupp.weight w) m ≠ j → MvPowerSeries.coeff m (φ a) = 0
  intro m hm
  have hcm := congrArg (MvPowerSeries.coeff m) key'
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_rescale, hprod m, ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at hcm
  rcases hcm with h | h
  · exfalso
    apply hm
    rw [sub_eq_zero] at h
    have h3 : t ^ j = t ^ (Finsupp.weight w m) := Units.ext (IsFractionRing.injective O E h)
    exact (hinj h3).symm
  · exact h
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Bcr l) (δ : ℚ_[l]), c ≠ 0 → (PP l).φB c = algebraMap ℚ_[l] (Bcr l) δ * c → (PP l).ιB c ∈ ((PP l).PD (botExt l)).Fil 0 → ‖δ‖ ≤ 1 := by
  intro l _ c δ hc hφ hF
  by_contra hδ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have hv : δ.valuation < 0 := by
    by_contra h
    exact hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation := ⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]
    simp
  let u : ℤ_[l] := ⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩
  have huu : IsUnit u := PadicInt.isUnit_iff.2 hu
  obtain ⟨N, N', hNN, hN, hN', hφN, -⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u)
    (by rw [Matrix.det_fin_one]; exact huu)
  set P := PP l with hP
  set D := P.PD (botExt l) with hD
  have h1 : N 0 0 * N' 0 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply] using this
  have h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0 := by
    have := congrFun (congrFun hφN 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at this
    exact this
  set w := N 0 0
  set w' := N' 0 0 with hw'
  have h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w' := by
    have h := congrArg P.φB h1
    rw [map_mul, map_one, h2] at h
    linear_combination w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1
  have ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t := by
    have := D.t_φ
    rw [P.PD_φ, P.PD_p, Algebra.smul_def] at this
    exact this
  have hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w' := by
    rw [P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]
    rw [map_mul, map_pow] at h3
    linear_combination (c * D.t ^ (a + 1)) * h3
  have ht0 : D.ι D.t ∈ D.Fil 0 := D.Fil_anti 0 D.mem_filtration_one
  have htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one]; exact D.one_mem
    | succ n ih => rw [pow_succ, map_mul]; exact D.Fil_mul 0 0 _ _ ih ht0
  have hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1 := by
    rw [map_mul, map_mul, pow_succ, map_mul]
    have e1 : D.ι c ∈ D.Fil 0 := by rw [P.PD_ι]; exact hF
    have e2 : D.ι w' ∈ D.Fil 0 := by rw [P.PD_ι]; exact hN' 0 0
    exact D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2
  obtain ⟨r, hr⟩ := D.fund _ hb (D.Fil_anti 0 hF1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have hw : IsUnit w' := IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)
    rw [eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero] at hr
    exact hc hr
  have hone : (1 : P.R.BdR) ∈ D.Fil 1 := by
    rw [← hr, P.PD_ι, AlgHom.commutes] at hF1
    have := (D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1
    rwa [algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one] at this
  have := D.Fil_mul 1 1 _ _ D.mem_filtration_one hone
  rw [mul_one] at this
  exact D.not_mem_filtration_two this
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    ext g <;> simp
end
