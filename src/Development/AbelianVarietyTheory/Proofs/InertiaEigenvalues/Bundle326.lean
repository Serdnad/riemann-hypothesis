module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

namespace GlobalTheory.GLq.HcClass

variable {g : ℕ} [Fact g.Prime]

theorem hcT_isClass (a b n : ℕ) (Φ : Gn g a → Gn g b → ℂ) : IsClass (hcT a b Φ n) := by
  intro x w
  unfold hcT
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft w⁻¹) _ _ fun y => ?_
  rw [Equiv.coe_mulLeft, show (w⁻¹ * y)⁻¹ * x * (w⁻¹ * y) = y⁻¹ * (w * x * w⁻¹) * y by group]

variable {a b : ℕ}

theorem conj_blk (P P' : Mt g a) (Q Q' : Mt g b) (M : Mt g (a + b)) (hM : InPar a M) :
    InPar a (blkM P 0 Q * M * blkM P' 0 Q') ∧ tl a (blkM P 0 Q * M * blkM P' 0 Q') = P * tl a M * P' ∧
      br a b (blkM P 0 Q * M * blkM P' 0 Q') = Q * br a b M * Q' := by
  rw [← blkM_eq hM, blkM_mul, blkM_mul, tl_blkM, br_blkM, tl_blkM, br_blkM]
  exact ⟨inPar_blkM _ _ _, rfl, rfl⟩

theorem blkM_one : blkM (1 : Mt g a) 0 (1 : Mt g b) = 1 := by
  rw [blkM, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def dg (u : Gn g a) (v : Gn g b) : Gn g (a + b) :=
  ⟨blkM u.val 0 v.val, blkM (u⁻¹).val 0 (v⁻¹).val, by simp [blkM_mul, blkM_one], by simp [blkM_mul, blkM_one]⟩

theorem dg_mul (u u' : Gn g a) (v v' : Gn g b) : dg u v * dg u' v' = dg (u * u') (v * v') := by
  ext : 1
  simp [dg, blkM_mul]

theorem dg_one : dg (1 : Gn g a) (1 : Gn g b) = 1 := by
  ext : 1
  simp [dg, blkM_one]

theorem dg_inv (u : Gn g a) (v : Gn g b) : (dg u v)⁻¹ = dg u⁻¹ v⁻¹ := by
  symm
  rw [eq_inv_iff_mul_eq_one, dg_mul, inv_mul_cancel, inv_mul_cancel, dg_one]

def Cnd (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) : Prop :=
  InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)

theorem cnd_conj (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) (hx : Cnd h₁ h₂ x) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) := by
  obtain ⟨hp, ht, hb⟩ := hx
  rw [dg_inv]
  have e : ((dg u v * x * dg u⁻¹ v⁻¹ : Gn g (a + b)) : Mt g (a + b)) =
      blkM u.val 0 v.val * x.val * blkM (u⁻¹).val 0 (v⁻¹).val := rfl
  have := conj_blk u.val (u⁻¹).val v.val (v⁻¹).val x.val hp
  refine ⟨e ▸ this.1, ?_, ?_⟩
  · rw [e, this.2.1, ht]; simp
  · rw [e, this.2.2, hb]; simp

theorem cnd_iff (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) ↔ Cnd h₁ h₂ x := by
  refine ⟨fun h => ?_, cnd_conj u v h₁ h₂ x⟩
  have := cnd_conj u⁻¹ v⁻¹ _ _ _ h
  simp only [dg_inv] at this
  have key : dg u⁻¹ v⁻¹ * (dg u v * x * dg u⁻¹ v⁻¹) * dg u⁻¹⁻¹ v⁻¹⁻¹ = x := by
    rw [inv_inv, inv_inv, ← dg_inv]; group
  rwa [key, show u⁻¹ * (u * h₁ * u⁻¹) * u⁻¹⁻¹ = h₁ by group,
    show v⁻¹ * (v * h₂ * v⁻¹) * v⁻¹⁻¹ = h₂ by group] at this

theorem res_conj (χ : Gn g (a + b) → ℂ) (hχ : IsClass χ) (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b χ (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) = res a b χ h₁ h₂ := by
  unfold res
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj (dg u v)).toEquiv _ _ fun x => ?_).symm
  have hc := cnd_iff u v h₁ h₂ x
  unfold Cnd at hc
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc, hχ x (dg u v)]

theorem hc_class : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ Φ : Gn g a → Gn g b → ℂ, IsClass (hcT a b Φ n)) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → (∀ h, IsClass (res a b χ h)) ∧ ∀ h, IsClass (fun x => res a b χ x h) := by
  intro g _ a b n hn
  subst hn
  refine ⟨fun Φ => hcT_isClass _ _ _ Φ, fun χ hχ => ⟨fun h x y => ?_, fun h x y => ?_⟩⟩
  · simpa using res_conj χ hχ 1 y h x
  · simpa using res_conj χ hχ y 1 x h

end GlobalTheory.GLq.HcClass
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.SplitBelow

theorem ef_eq_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P)
    (hN : Ideal.absNorm P = p) : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 1 := by

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmZ : ((p : ℤ) : 𝓞 E) ∈ P := by simpa using hm
  have hU : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd P hP hmZ
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpZ).mpr hmZ
  have hf : P.inertiaDeg ℤ = 1 := by
    have h := Ideal.pow_inertiaDeg p P
    rw [hN] at h
    exact Nat.pow_right_injective hp.two_le (by simpa using h)
  have het := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 F)) P
  have hft := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 F)) P
  rw [he] at het
  rw [hf] at hft
  rw [(mul_eq_one.mp het.symm).2, (mul_eq_one.mp hft.symm).2]
  exact mul_one 1

theorem splits_below_of_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by

  intro E _ _ _ p hp hd hN P hPm
  classical
  by_contra hns
  have hO : ∀ Q : HeightOneSpectrum (𝓞 E), GlobalTheory.CMVal.Over Q (below P) → Q = P := by
    intro Q hQ
    by_contra hne
    exact hns ⟨Q, P, hne, hQ, over_below P⟩
  have hq1 : ∀ q : (below P).asIdeal.primesOver (𝓞 E), q.1 = P.asIdeal := by
    intro q
    have hq := q.2
    have := hq.1
    have := hq.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (below P).ne_bot q.1
    have h := hO ⟨q.1, hq.1, hne⟩ (Ideal.LiesOver.over (P := q.1) (p := (below P).asIdeal)).symm
    exact congrArg HeightOneSpectrum.asIdeal h
  have hterm : ∀ q : (below P).asIdeal.primesOver (𝓞 E),
      q.1.ramificationIdx (OF E) * q.1.inertiaDeg (OF E) = 1 := by
    intro q
    rw [hq1 q]
    have := P.isPrime
    exact ef_eq_one (maximalRealSubfield E) E hp hd P.asIdeal hPm (hN P hPm)
  have hfr : Module.finrank (OF E) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (OF E) (maximalRealSubfield E) (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (below P).asIdeal (𝓞 E)
  rw [Finset.sum_congr rfl (fun q _ => hterm q), hfr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hle : Fintype.card ((below P).asIdeal.primesOver (𝓞 E)) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext ((hq1 a).trans (hq1 b).symm))
  omega

end GlobalTheory.LamTie.SplitBelow
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFun.LatQuot

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) (lam : O)
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hlam : ∀ x, lam • x ∈ P) : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hP g x hx, rfl⟩
  fg := by
    have := StdAdm.finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := StdAdm.finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hlam _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

theorem onto_sub [IsDomain O] [IsPrincipalIdealRing O] (lam : O) (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hi : Function.Injective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)) (hq : Onto T B q) :
    ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hr' : ∀ x, r (f x) = x := fun x => LinearMap.congr_fun hr x
  let P : Submodule O ↥T.L.T := (LinearMap.range (f.restrictScalars O)).comap q
  have hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P := by
    rintro g x ⟨a, ha⟩
    refine ⟨A.ρ g a, ?_⟩
    have ha' : f a = q x := ha
    change f (A.ρ g a) = q _
    rw [hf, ha', hq.2]
  have hlam : ∀ x, lam • x ∈ P := by
    intro x
    refine ⟨0, ?_⟩
    rw [map_zero, map_smul, ← algebraMap_smul k lam, hk, zero_smul]
  let L := subLattice T lam hl P hP hlam
  have hle : L.T ≤ T.L.T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨withLat T L, (r.restrictScalars O).comp (q.comp (Submodule.inclusion hle)), ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := hq.1 (f a)
    refine ⟨⟨x.1, x, ⟨a, hx.symm⟩, rfl⟩, ?_⟩
    change r (q x) = a
    rw [hx, hr']
  · rintro g ⟨_, x, ⟨a, ha⟩, rfl⟩
    have ha' : f a = q x := ha
    change r (q (latRep T.L g x)) = A.ρ g (r (q x))
    rw [hq.2, ← ha', ← hf, hr', hr']

theorem onto_quot (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hs : Function.Surjective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q) :
    Onto T B ((f.restrictScalars O).comp q) := by
  refine ⟨hs.comp hq.1, fun g x => ?_⟩
  change f (q _) = B.ρ g (f (q x))
  rw [hq.2, hf]

theorem onto_sum (A B C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k))
    (hi : IsHom A C i) (hj : IsHom B C j) (hs : Function.Surjective (i.coprod j))
    (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q)
    (T' : LocLat G Qp LL O) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k)) (hq' : Onto T' B q') :
    Onto (StdAdm.prodLat T T') C (((i.coprod j).restrictScalars O).comp
      ((q.prodMap q').comp (StdAdm.prodLatEquiv T T').toLinearMap)) := by
  refine ⟨hs.comp ((hq.1.prodMap hq'.1).comp (StdAdm.prodLatEquiv T T').surjective), fun g x => ?_⟩
  change i (q (latRep T.L g (StdAdm.prodLatEquiv T T' x).1)) + j (q' (latRep T'.L g (StdAdm.prodLatEquiv T T' x).2)) =
    C.ρ g (i (q (StdAdm.prodLatEquiv T T' x).1) + j (q' (StdAdm.prodLatEquiv T T' x).2))
  rw [hq.2, hq'.2, hi, hj, map_add (f := _)]

theorem onto_one [IsDomain O] (hs : Function.Surjective (algebraMap O k)) (T : LocLat G Qp LL O) (e₀ : ↥T.L.T)
    (hρ : ∀ g x, T.ρ g x = x) (h0 : e₀ ≠ 0) (hsp : Submodule.span O {e₀} = ⊤) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  have := T.L.free
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    refine ⟨smul_left_injective O h0, ?_⟩
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hsp]
  let e := LinearEquiv.ofBijective _ hb
  have he : e 1 = e₀ := one_smul O e₀
  refine ⟨(LinearMap.pi fun _ => Algebra.linearMap O k).comp e.symm.toLinearMap, ⟨?_, fun g x => ?_⟩, ?_⟩
  · intro y
    obtain ⟨c, hc⟩ := hs (y 0)
    refine ⟨e c, funext fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change algebraMap O k (e.symm (e c)) = y 0
    rw [e.symm_apply_apply, hc]
  · have h1 : latRep T.L g x = x := Subtype.ext (hρ g x)
    rw [h1]
    exact (one_smul k _).symm
  · funext i
    change algebraMap O k (e.symm e₀) = 1
    rw [← he, e.symm_apply_apply, map_one]

theorem lattice_quotients : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk hs _
  refine ⟨?_, ?_, ?_, onto_one hs⟩
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact onto_sub lam hl hk A B f hf hi T q hq
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact ⟨T, _, onto_quot A B f hf hi T q hq⟩
  · rintro A B C i j hi hj h ⟨T, q, hq⟩ ⟨T', q', hq'⟩
    exact ⟨_, _, onto_sum A B C i j hi hj h T q hq T' q' hq'⟩

end GlobalTheory.RedFun.LatQuot
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

theorem defect_mem {R : Type} [CommRing R] (S : Subring R) (a b : R)
    (ha : ∀ i : ℕ, ∃ g ∈ S, ((i.factorial : ℕ) : R) * g = a ^ i)
    (hb : ∀ j : ℕ, ∃ g ∈ S, ((j.factorial : ℕ) : R) * g = b ^ j) (n : ℕ) :
    ∃ e ∈ S, truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : R) * e := by
  choose A hAS hA using ha
  choose B hBS hB using hb
  have hD : ∀ d : Fin 2 →₀ ℕ, ∃ D : ℤ, (((d 0).factorial * (d 1).factorial : ℕ) : ℤ) *
      AddMonoidAlgebra.coeff (logDefect n) d = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * D := by
    intro d
    have hd : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
      ext x; fin_cases x <;> simp
    by_cases h : d 0 + d 1 < n
    · have := GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt n (d 0) (d 1) h
      rw [hd] at this
      exact ⟨0, by rw [this]; simp⟩
    · obtain ⟨D, hD⟩ := GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd n (d 0) (d 1) (by omega)
      rw [hd] at hD
      exact ⟨D, hD⟩
  choose D hD using hD
  refine ⟨∑ d ∈ (logDefect n).support, (D d : R) * (A (d 0) * B (d 1)),
    Subring.sum_mem _ fun d _ => Subring.mul_mem _ (intCast_mem S _)
      (Subring.mul_mem _ (hAS _) (hBS _)), ?_⟩
  rw [← aeval_logDefect, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc := congrArg (Int.cast : ℤ → R) (hD d)
  push_cast at hc
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, eq_intCast]
  rw [← hA, ← hB]
  push_cast
  linear_combination (A (d 0) * B (d 1)) * hc

theorem isLogJ_add : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a →
    GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  intro l _ a b y y' ha hb hy hy' r
  have hl : l.Prime := Fact.out
  obtain ⟨N1, hN1⟩ := hy r
  obtain ⟨N2, hN2⟩ := hy' r
  refine ⟨max (max N1 N2) (2 * l ^ r + 1), fun n hn => ?_⟩
  obtain ⟨sa, hsa, za, hza⟩ := hN1 n (le_of_max_le_left (le_of_max_le_left hn))
  obtain ⟨sb, hsb, zb, hzb⟩ := hN2 n (le_of_max_le_right (le_of_max_le_left hn))
  have hn' : 2 * l ^ r + 1 ≤ n := le_of_max_le_right hn
  have hA : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) a ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow ha i
    exact ⟨g, g.2, hg⟩
  have hB : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) b ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow hb i
    exact ⟨g, g.2, hg⟩
  obtain ⟨e, he, hE⟩ := defect_mem _ _ _ hA hB n
  have hdvd : l ^ r ∣ ((n - 1) / 2).factorial := by
    refine Nat.dvd_factorial (pow_pos hl.pos r) ?_
    generalize l ^ r = L at hn' ⊢
    omega
  obtain ⟨q, hq⟩ := hdvd
  let E : Per.Acris0 l := ⟨e, he⟩
  refine ⟨sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E, ?_,
    za + zb - (q : Per.Acris l) * algebraMap (Per.Acris0 l) (Per.Acris l) E, ?_⟩
  · rw [hq] at hE
    simp only [truncLogF] at hE
    have hEe : ((E : Per.Acris0 l) : Per.AinfP l) = e := rfl
    have hc : (((sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E : Per.Acris0 l)) : Per.AinfP l) =
        (sa : Per.AinfP l) + (sb : Per.AinfP l) + ((l ^ r * q : ℕ) : Per.AinfP l) * e := by
      simp [hEe]
    rw [hc]
    simp only [map_add (f := _), map_mul]
    push_cast at hE ⊢
    linear_combination hsa + hsb - hE
  · set_option synthInstance.maxHeartbeats 200000 in
    simp only [map_add (f := algebraMap (Per.Acris0 l) (Per.Acris l)), map_mul, map_natCast]
    push_cast
    linear_combination hza + hzb

end GlobalTheory.LogU
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_acris_log_one_add : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), GlobalTheory.LogU.InJ w → ∃ y : Per.Acris l, GlobalTheory.LogU.IsLogJ w y := by
  first | exact @GlobalTheory.LogU.exists_isLogJ | exact GlobalTheory.LogU.exists_isLogJ | (intros; apply GlobalTheory.LogU.exists_isLogJ <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.kap_mem_inC_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL), IsActC act → IsIdempotentElem e → (∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) → ∀ k, kap o e k ∈ inC K.1 := by
  first | exact @GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | exact GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | (intros; apply GlobalTheory.Cyc.Decomp.kap_idem_mem_inC <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  first | exact @GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | exact GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | (intros; apply GlobalTheory.Cyc.Decomp.lam_mul_of_isMat <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  first | exact @GlobalTheory.Cyc.Decomp.rank_count | exact GlobalTheory.Cyc.Decomp.rank_count | (intros; apply GlobalTheory.Cyc.Decomp.rank_count <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.norm_lt_rho1_of_mem_ideal_power : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  first | exact @GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow | exact GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow | (intros; apply GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
end
