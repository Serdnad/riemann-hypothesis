module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem localFactor_counital_descends :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  intro k A _ _ _ _ ε Δ ⟨hL, hR⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set I : Ideal A := RingHom.ker ε with hI
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun m => OrderDual.toDual (I ^ m), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)
  have hst : ∀ m, n ≤ m → I ^ n = I ^ m := fun m hm => hn m hm
  set N := n + 1 with hN
  set J : Ideal A := I ^ N with hJ
  have hJJ : IsIdempotentElem J := by
    show J * J = J
    rw [hJ, ← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨e', he', hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg J hfg).mp hJJ
  have he'J : e' ∈ J := by rw [hJe]; exact Submodule.mem_span_singleton_self e'
  have hJI : J ≤ I := Ideal.pow_le_self (by omega)
  have he'0 : ε e' = 0 := hJI he'J
  refine ⟨1 - e', by simp [he'0], he'.one_sub, ?_⟩
  have hspan : Ideal.span {1 - (1 - e')} = J := by
    rw [sub_sub_cancel, hJe]
  rw [hspan]
  set mk : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J with hmk
  let ε' : A ⧸ J →ₐ[k] k := Ideal.Quotient.liftₐ J ε (fun a ha => hJI ha)
  have hε' : ∀ a, ε' (mk a) = ε a := fun a => rfl
  have hnil : ∀ y ∈ RingHom.ker ε', IsNilpotent y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J y
    have ha : a ∈ I := by rw [RingHom.mem_ker] at hy ⊢; rw [← hε']; exact hy
    refine ⟨N, ?_⟩
    rw [← map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow ha N)
  let φ : (A ⧸ J) ⊗[k] (A ⧸ J) →ₐ[k] k := Algebra.TensorProduct.productMap ε' ε'
  let Δ'' : A →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := (Algebra.TensorProduct.map mk mk).comp Δ
  have hφ : ∀ t : A ⊗[k] A, φ (Algebra.TensorProduct.map mk mk t)
      = ε (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, hε', mul_comm]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hφΔ : ∀ a, φ (Δ'' a) = ε a := by
    intro a
    show φ (Algebra.TensorProduct.map mk mk (Δ a)) = ε a
    rw [hφ, hR]
  let iL : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeLeft
  let iR : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeRight
  have key : ∀ t : (A ⧸ J) ⊗[k] (A ⧸ J), t - algebraMap k _ (φ t) ∈ nilradical _ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      set u := x - algebraMap k (A ⧸ J) (ε' x) with hu
      set v := y - algebraMap k (A ⧸ J) (ε' y) with hv
      have hu0 : IsNilpotent u := hnil _ (by simp [RingHom.mem_ker, u])
      have hv0 : IsNilpotent v := hnil _ (by simp [RingHom.mem_ker, v])
      have hL : iL u ∈ nilradical _ :=
        mem_nilradical.2 (hu0.map _)
      have hR' : iR v ∈ nilradical _ :=
        mem_nilradical.2 (hv0.map _)
      have heq : x ⊗ₜ[k] y - algebraMap k _ (φ (x ⊗ₜ[k] y)) =
          iL u * iR v
          + algebraMap k _ (ε' y) * iL u
          + algebraMap k _ (ε' x) * iR v := by
        have h1 : x ⊗ₜ[k] y = iL x * iR y := by
          simp [iL, iR, Algebra.TensorProduct.tmul_mul_tmul]
        have h2 : iL x = iL u + algebraMap k _ (ε' x) := by
          rw [← AlgHom.commutes iL, ← map_add (f := _)]; simp [u]
        have h3 : iR y = iR v + algebraMap k _ (ε' y) := by
          rw [← AlgHom.commutes iR, ← map_add (f := _)]; simp [v]
        have h4 : φ (x ⊗ₜ[k] y) = ε' x * ε' y := by simp [φ]
        rw [h4, map_mul, h1, h2, h3]; ring
      rw [heq]
      exact add_mem (add_mem (Ideal.mul_mem_right _ _ hL) (Ideal.mul_mem_left _ _ hL)) (Ideal.mul_mem_left _ _ hR')
    | add s t hs ht =>
      have := add_mem hs ht
      convert this using 1
      simp only [map_add (f := _)]; abel
  have hkill : ∀ a ∈ J, Δ'' a = 0 := by
    have h0 : Δ'' e' = 0 := by
      apply (he'.map Δ'').eq_zero_of_isNilpotent
      have := mem_nilradical.1 (key (Δ'' e'))
      rwa [hφΔ, he'0, map_zero, sub_zero] at this
    intro a ha
    rw [hJe] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  let Δ' : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Ideal.Quotient.liftₐ J Δ'' hkill
  have hΔ' : ∀ a, Δ' (mk a) = Algebra.TensorProduct.map mk mk (Δ a) := fun a => rfl
  refine ⟨ε', Δ', ⟨?_, ?_⟩, ?_⟩
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.lid k (A ⧸ J) (LinearMap.rTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hL]
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.rid k (A ⧸ J) (LinearMap.lTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hR]
  · rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro y hy
    exact mem_nilradical.2 (hnil y hy)

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem divAlg_clear_denominators {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (v : B) (hv : v ∈ Submodule.span ℚ (Set.range ι)) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : O, ι c = (n : ℚ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    exact ⟨1, one_pos, o, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, c₁, hc₁⟩ := hx
    obtain ⟨n₂, hn₂, c₂, hc₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul,
      smul_smul, smul_add]
    push_cast
    rw [mul_comm (n₂ : ℚ) (n₁ : ℚ)]
  | smul q x _ hx =>
    obtain ⟨n, hn, c, hc⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩
    rw [map_mul, map_intCast, hc, smul_smul]
    rw [show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]
    congr 1
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

theorem divAlg_smul_injective {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (hunit : ∀ x : B, x ≠ 0 → IsUnit x) (hinj : Function.Injective ι)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (ρ : O →+* Module.End ℤ X)
    (x : X) (hx : x ≠ 0) (a : O) (ha : ρ a x = 0) : a = 0 := by
  by_contra h0
  have hιa : ι a ≠ 0 := fun h => h0 (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := hunit _ hιa
  obtain ⟨n, hn, c, hc⟩ := divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)
  have hca : c * a = (n : O) := by
    apply hinj
    rw [map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul,
      Algebra.smul_def, mul_one]
    simp
  have h1 : ρ (c * a) x = 0 := by rw [map_mul, Module.End.mul_apply, ha, map_zero]
  rw [hca, map_natCast] at h1
  have h2 : (n : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    simpa [Module.End.natCast_apply] using h1
  rcases smul_eq_zero.mp h2 with h | h
  · omega
  · exact hx h

end GlobalTheory

namespace GlobalTheory

theorem divAlg_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B]
    (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι →
    Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B →
    Module.finrank ℤ X = 0 := by
  intro B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt
  by_contra hne
  have hnt : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)

  let φ : O →ₗ[ℤ] X := (AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha
  let ι' : O →ₗ[ℤ] B := ι.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ι)
  rw [hspan] at hbspan
  let e := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  choose f hf using fun i : b => hbsub i.2
  have li1 : LinearIndependent ℤ (fun i : b => (i : B)) := hbli.restrict_scalars' ℤ
  have li2 : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp ι'
    convert li1 using 1
    funext i
    exact hf i
  have li3 : LinearIndependent ℤ (φ ∘ f) := li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hc := li3.cardinal_le_rank
  rw [Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hc
  have := Nat.cast_le.mp hc
  omega

end GlobalTheory
end

section

open TensorProduct Module

namespace GlobalTheory

open TensorProduct Module in
variable {B A M : Type*} [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A]
  [AddCommGroup M] [Module B M] {r : ℕ} in
private lemma finrank_fiber_eq (hinj : Function.Injective (algebraMap B A))
    (b : Basis (Fin r) A (A ⊗[B] M)) (P : Ideal B) [P.IsMaximal] :
    letI := Ideal.Quotient.field P
    finrank (B ⧸ P) ((B ⧸ P) ⊗[B] M) = r := by
  letI := Ideal.Quotient.field P
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  letI := Ideal.Quotient.field Q
  have h1 : finrank (A ⧸ Q) ((A ⧸ Q) ⊗[A] (A ⊗[B] M)) = r := by
    rw [finrank_eq_card_basis (Algebra.TensorProduct.basis (A ⧸ Q) b), Fintype.card_fin]
  rw [← Module.finrank_baseChange (R := A ⧸ Q),
    (AlgebraTensorModule.cancelBaseChange B (B ⧸ P) (A ⧸ Q) (A ⧸ Q) M).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange B A (A ⧸ Q) (A ⧸ Q) M).finrank_eq, h1]


open TensorProduct Module in
theorem _root_.GlobalTheory.nonempty_basis_of_basis_baseChange {B A M : Type*} [CommRing B] [CommRing A]
    [Finite (MaximalSpectrum B)] [Algebra B A] [Algebra.IsIntegral B A] [AddCommGroup M]
    [Module B M] [Module.Finite B M] {r : ℕ}
    (hinj : Function.Injective (algebraMap B A)) (b : Basis (Fin r) A (A ⊗[B] M)) :
    Nonempty (Basis (Fin r) B M) := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum B)
  have hfib : ∀ P : MaximalSpectrum B, ∃ e : Fin r → M,
      Submodule.span (B ⧸ P.asIdeal) (Set.range fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = ⊤ := by
    intro P
    haveI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    let β := Module.finBasisOfFinrankEq (B ⧸ P.asIdeal) _ (finrank_fiber_eq hinj b P.asIdeal)
    choose e he using fun j => TensorProduct.mk_surjective B M (B ⧸ P.asIdeal)
      Ideal.Quotient.mk_surjective (β j)
    refine ⟨e, ?_⟩
    have : (fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = β := funext he
    rw [this, β.span_eq]
  choose e he using hfib
  have hcrt : ∀ P : MaximalSpectrum B, ∃ c : B,
      ∀ P' : MaximalSpectrum B, c - (if P' = P then 1 else 0) ∈ P'.asIdeal := fun P =>
    Ideal.exists_forall_sub_mem_ideal (I := fun P' : MaximalSpectrum B => P'.asIdeal)
      (fun P₁ P₂ h => by
        haveI := P₁.isMaximal
        haveI := P₂.isMaximal
        exact Ideal.isCoprime_of_isMaximal fun h' => h (MaximalSpectrum.ext h')) _
  choose c hc using hcrt
  let x : Fin r → M := fun j => ∑ P, c P • e P j
  let N := Submodule.span B (Set.range x)
  have key : ∀ P : MaximalSpectrum B, (⊤ : Submodule B (M ⧸ N)) ≤ P.asIdeal • ⊤ := by
    intro P
    have hmk : ∀ P', Ideal.Quotient.mk P.asIdeal (c P') = if P = P' then 1 else 0 := by
      intro P'
      have := hc P' P
      split_ifs at this ⊢ with h
      · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
        exact this
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using this)
    have hsm : ∀ (a : B) (y : (B ⧸ P.asIdeal) ⊗[B] M),
        a • y = Ideal.Quotient.mk P.asIdeal a • y := fun a y =>
      (algebraMap_smul (B ⧸ P.asIdeal) a y).symm
    have hx : ∀ j, (1 : B ⧸ P.asIdeal) ⊗ₜ[B] x j = 1 ⊗ₜ e P j := by
      intro j
      simp only [x, tmul_sum, tmul_smul]
      simp only [hsm, hmk, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    have h0 : N.mkQ.baseChange (B ⧸ P.asIdeal) = 0 := by
      apply LinearMap.ext_on_range (he P)
      intro j
      rw [← hx, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩), tmul_zero,
        LinearMap.zero_apply]
    have hsurj : Function.Surjective (N.mkQ.baseChange (B ⧸ P.asIdeal)) :=
      LinearMap.lTensor_surjective (B ⧸ P.asIdeal) N.mkQ_surjective
    have hsub : Subsingleton ((B ⧸ P.asIdeal) ⊗[B] (M ⧸ N)) := ⟨fun y z => by
      obtain ⟨y', rfl⟩ := hsurj y
      obtain ⟨z', rfl⟩ := hsurj z
      simp [h0]⟩
    have hq := (TensorProduct.quotTensorEquivQuotSMul (M ⧸ N) P.asIdeal).symm.toEquiv.subsingleton
    rw [Submodule.Quotient.subsingleton_iff] at hq
    rw [hq]
  have hann : Module.annihilator B (M ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht1, ht⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P ⊤
      Module.Finite.fg_top (key ⟨P, hP⟩)
    have htP : t ∈ P := hle (Module.mem_annihilator.mpr fun q => ht q trivial)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem htP ht1))
  have hN : N = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h1 : (1 : B) ∈ Module.annihilator B (M ⧸ N) := hann ▸ Submodule.mem_top
    have := Module.mem_annihilator.mp h1 (N.mkQ m)
    simpa [Submodule.Quotient.mk_eq_zero] using this
  let f := Fintype.linearCombination B x
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hN
  let F := f.baseChange A
  have hFs : Function.Surjective F := LinearMap.lTensor_surjective A hfs
  let φ : (Fin r → A) →ₗ[A] (Fin r → A) := b.equivFun.toLinearMap ∘ₗ F ∘ₗ
    (TensorProduct.piScalarRight B A A (Fin r)).symm.toLinearMap
  have hφs : Function.Surjective φ := by
    simpa [φ] using b.equivFun.surjective.comp
      (hFs.comp (TensorProduct.piScalarRight B A A (Fin r)).symm.surjective)
  have hφi := OrzechProperty.injective_of_surjective_endomorphism φ hφs
  have hFi : Function.Injective F := by
    intro y z hyz
    have := @hφi (TensorProduct.piScalarRight B A A (Fin r) y)
      (TensorProduct.piScalarRight B A A (Fin r) z) (by
        simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hyz])
    exact (TensorProduct.piScalarRight B A A (Fin r)).injective this
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : F ((1 : A) ⊗ₜ v) = F 0 := by
      rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, tmul_zero, map_zero]
    have h2 := congrArg (TensorProduct.piScalarRight B A A (Fin r)) (hFi h1)
    rw [Submodule.mem_bot]
    funext i
    exact hinj (by rw [Pi.zero_apply, map_zero, Algebra.algebraMap_eq_smul_one]; simpa using congrFun h2 i)
  exact ⟨Basis.ofEquivFun (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩


open TensorProduct Module in
theorem _root_.GlobalTheory.finrank_eq_mul_of_basis_tensor_self (k B A : Type) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite k A] (r : ℕ)
    (hinj : Function.Injective (algebraMap B A))
    (hb : Nonempty (Module.Basis (Fin r) A (TensorProduct B A A))) :
    Module.finrank k A = r * Module.finrank k B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton A := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), Subsingleton.elim (0 : B) 1]
    simp [Module.finrank_zero_of_subsingleton]
  haveI : Module.Finite k B :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom k B A).toLinearMap hinj
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨β⟩ := _root_.GlobalTheory.nonempty_basis_of_basis_baseChange (M := A) hinj hb.some
  haveI : Module.Free B A := Module.Free.of_basis β
  rw [← Module.finrank_mul_finrank k B A, finrank_eq_card_basis β, Fintype.card_fin, mul_comm]

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
end
