module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle236
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle232
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.Tensor
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

theorem localDecomp_core : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  intro R B _ _ _ Q _ ι _ _ _ C hC hcov hét hann
  have hV := fun i => GlobalTheory.T.exists_subalgebra_atPrime_fractions_equiv R B Q (C i) (hann i)
  choose V hVmem hVeq using hV
  refine ⟨ι, inferInstance, inferInstance, inferInstance, V, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem i x).1 hx
    exact (hVmem j x).2 ⟨a, hC hij ha, s, hC hij hs, hsQ, hxs⟩
  · intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨i1, h1⟩ := hcov a
    obtain ⟨i2, h2⟩ := hcov (s : B)
    obtain ⟨k, hk1, hk2⟩ := directed_of (· ≤ ·) i1 i2
    exact ⟨k, (hVmem k _).2 ⟨a, hC hk1 h1, s, hC hk2 h2, s.2, IsLocalization.mk'_spec _ _ _⟩⟩
  · intro m x hx hu
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem m x).1 hx
    have hsu : IsUnit (algebraMap B (Localization.AtPrime Q) s) :=
      IsLocalization.map_units _ (⟨s, hsQ⟩ : Q.primeCompl)
    have hau : IsUnit (algebraMap B (Localization.AtPrime Q) a) := hxs ▸ hu.mul hsu
    have haQ : a ∉ Q := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q a).1 hau
    refine ⟨↑hu.unit⁻¹, (hVmem m _).2 ⟨s, hs, a, ha, haQ, ?_⟩, hu.mul_val_inv⟩
    calc (↑hu.unit⁻¹ : Localization.AtPrime Q) * algebraMap B _ a
        = ↑hu.unit⁻¹ * (x * algebraMap B _ s) := by rw [hxs]
      _ = algebraMap B _ s := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  · intro m
    obtain ⟨A, i1, i2, i3, q, i4, ⟨e⟩⟩ := hét m
    obtain ⟨f⟩ := hVeq m
    exact ⟨A, i1, i2, i3, q, i4, ⟨e.trans f⟩⟩

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  first | (exact @GlobalTheory.PicLoc.subsingleton_pic_localization) | (exact GlobalTheory.PicLoc.subsingleton_pic_localization) | (intros; apply GlobalTheory.PicLoc.subsingleton_pic_localization <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem surjective_of_trace_of_smul_mem_range (S A B : Type) [CommRing S] [IsLocalRing S]
    [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A]
    [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B]
    [Algebra.Etale S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ) (s : S) (hs : s ≠ 0)
    (hcok : ∀ b : B, s • b ∈ φ.range)
    (htr : ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) : Function.Surjective φ := by
  classical
  have htf : ∀ b : B, s • b = 0 → b = 0 := by
    intro b hb
    let e := Module.Free.chooseBasis S B
    apply e.repr.injective
    ext i
    have := congrArg (fun x => e.repr x i) hb
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    simpa using (mul_eq_zero.mp this).resolve_left hs
  let L : A →ₗ[S] B := φ.toLinearMap
  have hL : Function.Injective L := hφ
  let E : A ≃ₗ[S] LinearMap.range L := LinearEquiv.ofInjective L hL
  let g : B →ₗ[S] LinearMap.range L :=
    { toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun c x => by ext; simp [smul_comm s c] }
  have hg : Function.Injective g := by
    intro x y hxy
    have : s • x = s • y := congrArg Subtype.val hxy
    have h0 : s • (x - y) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf _ h0)
  have h1 : Module.finrank S A ≤ Module.finrank S B :=
    LinearMap.finrank_le_finrank_of_injective hL
  have h2 : Module.finrank S B ≤ Module.finrank S A :=
    LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g)
      (E.symm.injective.comp hg)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) =
      Fintype.card (Module.Free.ChooseBasisIndex S B) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]
    omega
  let eι := Fintype.equivOfCardEq hcard
  let a := (Module.Free.chooseBasis S A).reindex eι
  let bB := Module.Free.chooseBasis S B
  let v : Module.Free.ChooseBasisIndex S B → B := fun i => φ (a i)
  have htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]
  have hdv : Algebra.discr S v = Algebra.discr S a := by
    rw [Algebra.discr_def, Algebra.discr_def, htm]
  let P := bB.toMatrix v
  have hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v := by
    funext j
    rw [← bB.sum_toMatrix_smul_self v j]
    simp [Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  have hu : IsUnit (P.det ^ 2 * Algebra.discr S bB) := by
    rw [← hdisc, hdv]; exact discr_isUnit S A a
  have hPu : IsUnit P.det := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)
  have hbd : IsUnit (bB.det v) := by rw [Module.Basis.det_apply]; exact hPu
  have hspan := ((Module.Basis.is_basis_iff_det bB).mpr hbd).2
  intro y
  have hy : y ∈ Submodule.span S (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span S (Set.range v) ≤ LinearMap.range L := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩
  obtain ⟨x, hx⟩ := hle hy
  exact ⟨x, hx⟩

end GlobalTheory.EtaleCoker
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.FinInterNil

theorem exists_ne_zero_isNilpotent_mul {D E : Type} [CommRing D] [IsDomain D] [CommRing E]
    [Algebra D E] (y : E)
    (hy : ∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → y ∈ Q) :
    ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid E :=
    { carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n}
      mul_mem' := by
        rintro a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩
        exact ⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }
  have h0 : (0 : E) ∉ M := by
    rintro ⟨t, ht, n, hz⟩
    apply hcon t ht
    refine ⟨n + 1, ?_⟩
    calc (algebraMap D E t * y) ^ (n + 1)
        = algebraMap D E t ^ n * y * (algebraMap D E t * y ^ n) := by ring
      _ = 0 := by rw [← hz, mul_zero]
  have hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    have hz0 : z = 0 := by simpa using hz
    exact h0 (hz0 ▸ hzM)
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  have hcomap : Q.comap (algebraMap D E) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Ideal.mem_bot]
    by_contra htne
    have hm : algebraMap D E t ∈ M := ⟨t, htne, 0, by simp⟩
    exact Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm
  have hyQ := hy Q hQ hcomap
  have hm : y ∈ M := ⟨1, one_ne_zero, 1, by simp⟩
  exact Set.disjoint_left.mp hQM hyQ hm

theorem main : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type)
    (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) →
    (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) →
    ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  intro D E _ _ _ _ ι X P hFG hQ
  classical
  have hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) :=
    fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)
  have hJfg : (∏ i ∈ X, P i).FG := by
    refine Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG
    exact ⟨{1}, by simp⟩
  have hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i) := by
    intro g hg
    simp only [Submodule.mem_iInf]
    intro i hi
    exact (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg
  obtain ⟨S, hS⟩ := hJfg
  have hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i) := fun g =>
    hJI g (hS ▸ Submodule.subset_span g.2)
  choose t ht using fun g : S => hstep g.1 (hSI g)
  refine ⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩
  set s := ∏ g : S, t g with hs
  let K : Ideal E := Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)
  have hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z) := by
    intro z
    simp [K, mem_nilradical]
  have hJK : (∏ i ∈ X, P i) ≤ K := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, hK]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))
    have he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g) := by
      rw [hs, hc, map_mul]; ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2
  intro y hy
  have hyN : y ^ X.card ∈ ∏ i ∈ X, P i := by
    have := Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by
      have := hy
      simp only [Submodule.mem_iInf] at this
      exact this i hi)
    simpa [Finset.prod_const] using this
  have hn := (hK _).mp (hJK hyN)
  have hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1)) := by
    have he : (algebraMap D E s * y) ^ (X.card + 1)
        = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left hn
  obtain ⟨k, hk⟩ := hpow
  exact ⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩

end GlobalTheory.FinInterNil
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.ZModFlat

open scoped TensorProduct

theorem exists_mul_eq_zero_of_smul_eq_zero (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M]
    (hdiv : ∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y)
    (a : ULift.{1} (ZMod q)) (y : M) (hy : a • y = 0) :
    ∃ e : ℕ, (e : ULift.{1} (ZMod q)) * a = 0 ∧ ∃ z : M, y = e • z := by
  set n := a.down.val with hn
  have ha : a = (n : ULift.{1} (ZMod q)) := by
    apply ULift.down_injective
    rw [ULift.down_natCast, hn, ZMod.natCast_zmod_val]
  have hq : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simp
  have hgq : Nat.gcd n q ∣ q := Nat.gcd_dvd_right n q
  have hgn : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
  refine ⟨q / Nat.gcd n q, ?_, ?_⟩
  · rw [ha, ← Nat.cast_mul]
    have : q ∣ q / Nat.gcd n q * n := by
      have h := Nat.mul_dvd_mul (dvd_refl (q / Nat.gcd n q)) hgn
      rwa [Nat.div_mul_cancel hgq] at h
    obtain ⟨m, hm⟩ := this
    rw [hm, Nat.cast_mul, hq, zero_mul]
  · apply hdiv (Nat.gcd n q) (q / Nat.gcd n q) (Nat.mul_div_cancel' hgq)
    have h1 : n • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← ha, hy]
    have h2 : q • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hq, zero_smul]
    have hb : ((Nat.gcd n q : ℕ) : ℤ) = n * Nat.gcdA n q + q * Nat.gcdB n q :=
      Nat.gcd_eq_gcd_ab n q
    have h3 : ((n : ℤ) * Nat.gcdA n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h1, smul_zero]
    have h4 : ((q : ℤ) * Nat.gcdB n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h2, smul_zero]
    rw [← natCast_zsmul, hb, add_smul, h3, h4, add_zero]

theorem flat_of_divisibility : ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M],
    (∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y) →
      Module.Flat (ULift.{1} (ZMod q)) M := by
  intro q _ M _ _ hdiv
  haveI : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective
      ((ULift.ringEquiv (R := ZMod q)).symm.toRingHom.comp (Int.castRingHom (ZMod q)))
      (by
        intro x
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
        exact ⟨z, by apply ULift.down_injective; simpa using hz⟩)
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal J).principal
  let b : J := ⟨a, by rw [ha]; exact Submodule.mem_span_singleton_self a⟩
  have hall : ∀ t : J ⊗[ULift.{1} (ZMod q)] M, ∃ y : M, t = b ⊗ₜ y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r x =>
      have hr : (r : ULift.{1} (ZMod q)) ∈ Submodule.span (ULift.{1} (ZMod q)) {a} := ha ▸ r.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
      refine ⟨c • x, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      ext
      simp [b, ← hc]
    | add s t hs ht =>
      obtain ⟨y1, rfl⟩ := hs
      obtain ⟨y2, rfl⟩ := ht
      exact ⟨y1 + y2, (TensorProduct.tmul_add _ _ _).symm⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := hall t
  have hy : a • y = 0 := by
    have := congrArg (TensorProduct.lid (ULift.{1} (ZMod q)) M) ht
    simpa [b] using this
  obtain ⟨e, he, z, rfl⟩ := exists_mul_eq_zero_of_smul_eq_zero q M hdiv a y hy
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← TensorProduct.smul_tmul]
  have : ((e : ULift.{1} (ZMod q))) • b = 0 := by
    ext
    simp [b, he]
  rw [this, TensorProduct.zero_tmul]

end GlobalTheory.ZModFlat
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem lift_square_presentation_of_flat : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  intro O B A k H σ _ _ _ _ _ _ _ _ _ _ _ _ _ ε π ρ εH x hπ hker hρO hε hρ hx hfg g hg hJ
  classical
  set τ : B →+* k := π.comp ((ε : A →+* O).comp (algebraMap B A)) with hτ
  have hτb : ∀ b, τ b = π (ε (algebraMap B A b)) := fun b => rfl
  have hτO : ∀ c, τ (algebraMap O B c) = π c := by
    intro c
    rw [hτb, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  have hτs : Function.Surjective τ := by
    intro y
    obtain ⟨c, rfl⟩ := hπ y
    exact ⟨_, hτO c⟩
  have hρB : ∀ b, ρ (algebraMap B A b) = algebraMap k H (τ b) := by
    intro b
    have h1 : b - algebraMap O B (ε (algebraMap B A b)) ∈ RingHom.ker τ := by
      rw [RingHom.mem_ker, map_sub, hτO, hτb, sub_self]
    have h2 : algebraMap B A (b - algebraMap O B (ε (algebraMap B A b))) ∈ RingHom.ker ρ := by
      rw [hρ]
      exact Ideal.mem_map_of_mem _ h1
    rw [RingHom.mem_ker, map_sub, map_sub, ← IsScalarTower.algebraMap_apply, hρO,
      sub_eq_zero] at h2
    rw [h2, hτb]
  set Ψ : MvPolynomial σ B →ₐ[B] A := MvPolynomial.aeval x with hΨ
  set Φ : MvPolynomial σ k →ₐ[k] H := MvPolynomial.aeval (fun j => ρ (x j)) with hΦ
  set T : MvPolynomial σ B →+* MvPolynomial σ k := MvPolynomial.map τ with hT
  have hcomm : ∀ F, ρ (Ψ F) = Φ (T F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [hΨ, hΦ, hT, hρB]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      simp [hΨ, hΦ, hT]
  have hTs : Function.Surjective T := MvPolynomial.map_surjective τ hτs
  have hTk : RingHom.ker T = (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) :=
    MvPolynomial.ker_map τ
  have hlift : ∀ G, Φ G = 0 → ∃ F, Ψ F = 0 ∧ T F = G := by
    intro G hG
    obtain ⟨F0, rfl⟩ := hTs G
    have h1 : Ψ F0 ∈ ((RingHom.ker τ).map (algebraMap B (MvPolynomial σ B))).map
        (Ψ : MvPolynomial σ B →+* A) := by
      rw [Ideal.map_map, AlgHom.comp_algebraMap, ← hρ, RingHom.mem_ker, hcomm, hG]
    rw [Ideal.mem_map_iff_of_surjective (Ψ : MvPolynomial σ B →+* A) hx] at h1
    obtain ⟨F1, hF1, hF⟩ := h1
    rw [← hTk, RingHom.mem_ker] at hF1
    refine ⟨F0 - F1, ?_, ?_⟩
    · rw [map_sub, sub_eq_zero]
      exact hF.symm
    · rw [map_sub, hF1, sub_zero]
  choose f hf hfT using fun i => hlift (g i) (hg i)
  refine ⟨f, hf, ?_⟩
  let η : MvPolynomial σ B →ₐ[O] O := ε.comp (Ψ.restrictScalars O)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  have hn : ∀ F, F ∈ (IsLocalRing.maximalIdeal O).comap η ↔ εH (Φ (T F)) = 0 := by
    intro F
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, ← hcomm, hε, hη]
  have key : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔
      (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ := by
    have hle : Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp Φ) * RingHom.ker Φ ≤
        (Ideal.span (Set.range f) ⊔
          (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ).map T := by
      rw [Ideal.map_sup, Ideal.map_mul]
      refine sup_le_sup ?_ (Ideal.mul_mono ?_ ?_)
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [← hfT i]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      · intro G hG
        obtain ⟨F, rfl⟩ := hTs G
        exact Ideal.mem_map_of_mem _ ((hn F).2 hG)
      · intro G hG
        obtain ⟨F, hF, rfl⟩ := hlift G hG
        exact Ideal.mem_map_of_mem _ hF
    have hS : Ideal.span (Set.range f) ⊔
        (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ ≤ RingHom.ker Ψ := by
      refine sup_le ?_ Ideal.mul_le_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hf i
    have hp : (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) ≤
        (IsLocalRing.maximalIdeal O).comap η := by
      rw [← hTk]
      intro F hF
      rw [hn, (RingHom.mem_ker).1 hF, map_zero, map_zero]
    intro F hF
    have h1 : T F ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, ← hcomm, (RingHom.mem_ker).1 hF, map_zero]
    obtain ⟨F1, hF1, hF'⟩ := (Ideal.mem_map_iff_of_surjective T hTs).1 (hle (hJ h1))
    have h2 : F - F1 ∈ RingHom.ker Ψ ⊓
        (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) := by
      refine ⟨sub_mem hF (hS hF1), ?_⟩
      rw [← hTk]
      show T (F - F1) = 0
      rw [map_sub, hF', sub_self]
    have h3 := Ideal.mul_mono_left hp
      (GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target B (MvPolynomial σ B) A Ψ hx (RingHom.ker τ) h2)
    have h4 : F = F1 + (F - F1) := by ring
    rw [h4]
    exact add_mem hF1 (Ideal.mem_sup_right h3)
  exact GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section O (MvPolynomial σ B) η _ _ hfg key

end GlobalTheory
end

section

open scoped BigOperators Matrix ComplexConjugate
open Polynomial
theorem _root_.GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (t : FractionRing R), (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧ t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) → ∃ a : R, algebraMap R (FractionRing R) a = t := by
  first | exact @GlobalTheory.integral_of_forall_height_one | exact GlobalTheory.integral_of_forall_height_one | (intros; apply GlobalTheory.integral_of_forall_height_one <;> assumption)
end
