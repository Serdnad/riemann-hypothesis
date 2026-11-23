module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section
namespace GlobalTheory.PBFc

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ n x) := by
  subst hn; subst hi; rfl

theorem cast_cup (q : ℕ) {E : Spc} {n m k a b c : ℤ} (hk : n + m = k) (hc : a + b = c) (x : Ht q E n a) (y : Ht q E m b) :
    Ht.cast hk hc ((twPair q a b).cup E rfl x y) =
      (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
        (twPair q a b) hc).cup E hk x y := by
  subst hk; subst hc; rfl

theorem cls_term (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (j : Fin N)
    (z : Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n,
      γ.1 = (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
        (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) ∧
      pull _ (twIso E V).hom _ n (Ht.cast (by ring) (by ring) (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a))
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) : Ht q _ n i) = CohomologyClass.mk γ := by
  set c := (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
    (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) with hcdef
  have hAW := GlobalTheory.T.cochain_product_alexander_whitney_formula V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1 c (fun M s h => by
    rw [hcdef, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, awChains_f])
  have hδ := aw_cocycle (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _))
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) c (by
      simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW)
  refine ⟨Cocycle.mk c (n + 1) rfl hδ, rfl, ?_⟩
  rw [pull_cast]
  change Ht.cast _ _ (cpull ((chains (ZMod q)).map (twIso E V).hom) _ _ ((twPair q _ _).cup _ rfl _ _)) = _
  rw [Pair.cup_pull, cast_cup]
  change (twPairI q i ((j : ℕ) : ℤ)).cup _ _ (pull _ (twIso E V).hom _ _ (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a)))
    (pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) = _
  rw [← pull_comp, twIso_hom_fst, ← hz]
  refine Pair.cup_spec _ _ _ (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _)) _ _ ?_
  simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW

theorem pbfMap_eq_cpull_aw (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n)
    (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)) :
    pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  choose γ hγ hγc using fun j : Fin N => cls_term q V ℓ n i j (z j) (hz j) (a j)
  have e1 : pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      ∑ j : Fin N, CohomologyClass.mk (γ j) := by
    unfold pbfMap

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hγc j
  have e2 : zcomp (Cocycle.ofHom (awChains (ZMod q) (twX E V))) b (zero_add n) = ∑ j : Fin N, γ j := by
    apply Cocycle.ext
    have hs := map_sum (AddSubgroup.subtype (cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res (ZMod q) (tw q i)) n)) γ Finset.univ
    refine Eq.trans ?_ hs.symm
    change _ = ∑ j, (γ j).1
    simp only [hγ]
    change (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp b.1 (zero_add n) = _
    rw [hb, phi_apply]
    exact map_sum (AddMonoidHom.mk' (fun x : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n =>
      (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp x (zero_add n)) (fun x y => Cochain.comp_add _ _ _ _)) _ _
  rw [e1, cpre_mk, e2]
  exact (map_sum (AddMonoidHom.mk' (CohomologyClass.mk : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n → _)
    (fun x y => CohomologyClass.mk_add x y)) _ _).symm

end GlobalTheory.PBFc
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_split_unif_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E),
    Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) →
    ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧
      modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  classical
  intro E _ _ _ v x hv hx
  obtain ⟨h2, hN⟩ := GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv
  obtain ⟨P₁, P₂, hne, hP₁, hP₂⟩ := hv
  have hx0 : (x : maximalRealSubfield E) ≠ 0 := fun h => by
    have h0 : x = 0 := Subtype.ext h
    have h1 := hx P₁ hP₁
    rw [h0, iota_zero, zero_coord, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let k : (maximalRealSubfield E)ˣ := Units.mk0 (x : maximalRealSubfield E) hx0
  let y : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom (Formalism.L2.Host.upF (maximalRealSubfield E) k)
  have hy : (y : Af E) = iota x := rfl
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hmem : ∀ P, P ∈ S ↔ Over P v := fun P => mem_aboveF P v
  have hin : ∀ P, Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = iota x P := fun P hP => by
    rw [Fibre.prod_single_apply, if_pos ((hmem P).2 hP), hy]
  have hout : ∀ P, ¬ Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = 1 := fun P hP => by
    rw [Fibre.prod_single_apply, if_neg (fun h => hP ((hmem P).1 h))]
  refine ⟨∏ P ∈ S, single P (coord P y), hin, hout, ?_, fun χ hχ => ?_⟩
  · have hS2 : S = {P₁, P₂} := by
      ext R
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h2 P₁ P₂ hP₁ hP₂ hne R, fun h => by rcases h with rfl | rfl <;> assumption⟩
    unfold modF
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => by
      by_contra h
      refine hP ?_
      beta_reduce
      rw [hout P (fun h' => h ((hmem P).2 h'))]
      simp)]
    rw [Finset.prod_congr rfl (g := fun _ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (fun P hP => by
      rw [hin P ((hmem P).1 hP), hx P ((hmem P).1 hP), WithZero.log_exp, (hN P ((hmem P).1 hP)).1, zpow_neg_one])]
    rw [Finset.prod_const, hS2, Finset.card_pair hne]
  · have h1 := hχ.1 v k
    unfold Formalism.L2.Host.HChar.resFin at h1
    rw [MonoidHom.finsetProd_apply] at h1
    rw [map_prod, ← h1]
    exact Finset.prod_congr rfl fun P _ => rfl

end GlobalTheory.CMVal.Euler
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem span_sup_pow_eq_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {x : R}
    (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) (n : ℕ) : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal := by
  have hd : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ∣ v.asIdeal ^ (n + 1) := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow v.prime _).1 hd
  rw [associated_iff_eq] at hi
  have hle : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ≤ v.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) (Ideal.pow_le_self (by omega))
  have hxi : x ∈ v.asIdeal ^ i := hi ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  rw [hi] at hle ⊢
  match i, hle, hxi with
  | 0, hle, _ => exact absurd (top_le_iff.1 (by simpa using hle)) v.isPrime.ne_top
  | 1, _, _ => exact pow_one _
  | i + 2, _, hxi => exact absurd (Ideal.pow_le_pow_right (by omega) hxi) hx2

theorem eq_exp_neg_one_of_le_of_not_le {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by
  have h0 : g ≠ 0 := fun h => h2 (h ▸ zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

theorem locIn_succ_nonunit_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  intro E _ _ _ v hv
  have he := fun P hP => ((GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv).2 P hP).2.1
  obtain ⟨x, hx1, hx2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have hval : ∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ) := fun P hP =>
    eq_exp_neg_one_of_le_of_not_le (by simpa using val_iota_le_of_mem hP 1 hx1)
      (fun h => hx2 ((he P hP x 2).1 ((val_iota_le_iff P 2 x).1 (by simpa using h))))
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨x, hval, fun n π y hπ => ?_⟩
  have hx0 : ∀ P, Over P v → iota x P ≠ 0 := fun P hP h => by
    have := hval P hP
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hq : ∀ P, Over P v → ((π⁻¹ * y : (Af E)ˣ) : Af E) P = (iota x P)⁻¹ * (y : Af E) P := fun P hP => by
    rw [Units.val_mul, mul_coord, inv_coord, hπ P hP]
  constructor
  · intro h
    refine ⟨?_, fun hu => ?_⟩
    · obtain ⟨b, hb⟩ := h
      refine ⟨x * b, fun P hP => ?_⟩
      have h0 := hx0 P hP
      have : (y : Af E) P - iota (x * b) P = iota x P * (((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P) := by
        rw [hq P hP, iota_mul, mul_coord]; field_simp
      rw [this, map_mul, hval P hP]
      refine (mul_le_mul' le_rfl (hb P hP)).trans_eq ?_
      rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · obtain ⟨P, -, -, hP, -⟩ := hv
      have h1 := h.val_le hP
      rw [hq P hP, map_mul, map_inv₀, hval P hP, hu P hP, mul_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h1
      omega
  · rintro ⟨h, hu⟩
    push Not at hu
    obtain ⟨Q, hQ, hyQ⟩ := hu
    have hyQ' : Valued.v ((y : Af E) Q) < 1 := lt_of_le_of_ne (h.val_le hQ) hyQ
    obtain ⟨a, ha⟩ := h
    have hav : a ∈ v.asIdeal := by
      have h2 : Valued.v ((y : Af E) Q - iota a Q) < 1 :=
        ((ha Q hQ).trans (WithZero.exp_le_exp.2 (by push_cast; omega))).trans_lt hlt
      have h3 := Valuation.map_sub_lt _ hyQ' h2
      rw [sub_sub_cancel] at h3
      have h4 : Valued.v (iota a Q) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
        by_cases h0 : Valued.v (iota a Q) = 0
        · rw [h0]; exact zero_le'
        · rw [← WithZero.exp_log h0] at h3 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          rw [WithZero.exp_le_exp]; push_cast; omega
      simpa using (he Q hQ a 1).1 ((val_iota_le_iff Q 1 a).1 h4)
    rw [← span_sup_pow_eq_of_notMem_sq v (by simpa using hx1) hx2 n] at hav
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hav
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine ⟨b, fun P hP => ?_⟩
    have h0 := hx0 P hP
    have : ((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P =
        (iota x P)⁻¹ * (((y : Af E) P - iota (b * x + t) P) + iota t P) := by
      rw [hq P hP, iota_add, iota_mul, add_coord, mul_coord]; field_simp; ring
    rw [this, map_mul, map_inv₀, hval P hP]
    refine (mul_le_mul' le_rfl (Valuation.map_add_le _ (ha P hP) (val_iota_le_of_mem hP (n + 1) ht))).trans_eq ?_
    rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.CMVal.Euler
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.UPel.HT.LieType.DimSum

theorem finrank_eq_two_mul_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hdisc : DiscreteTopology Q.range)
    (hspan : Submodule.span ℝ (Set.range Q) = ⊤) : Module.finrank ℤ La = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  rw [e.finrank_eq, h1, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Finset.sum_const, mul_comm]

theorem trace_real_restrict (g : ℕ) (M : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' M).restrictScalars ℝ) = 2 * M.trace.re := by
  classical
  let b := Pi.basisFun ℂ (Fin g)
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b)]
  have : M.trace = LinearMap.trace ℂ _ (Matrix.toLin' M) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b]; simp [b]
  rw [this, LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul,
    Finset.sum_add_distrib]

theorem trace_int_eq_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ) (A : La →+ La) (hinj : Function.Injective Q)
    (hdisc : DiscreteTopology Q.range) (hspan : Submodule.span ℝ (Set.range Q) = ⊤)
    (hA : ∀ x, Q (A x) = M *ᵥ Q x) :
    ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = M.trace + (starRingEnd ℂ) M.trace := by
  classical
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  have he : ∀ x, ((e x : L) : Fin g → ℂ) = Q x := fun x => rfl
  let b := Module.Free.chooseBasis ℤ La
  let bL := b.map e
  let bR := bL.ofZLatticeBasis ℝ L
  have hbR : ∀ i, bR i = Q (b i) := by
    intro i; simp [bR, bL, Module.Basis.ofZLatticeBasis_apply, he]
  have hmat : LinearMap.toMatrix bR bR ((Matrix.toLin' M).restrictScalars ℝ) =
      (LinearMap.toMatrix b b A.toIntLinearMap).map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : (Matrix.toLin' M).restrictScalars ℝ (bR j) = Q (A (b j)) := by
      rw [hbR, hA]; rfl
    rw [h1]
    have h2 : Q (A (b j)) = ∑ k, (b.repr (A (b j)) k : ℝ) • bR k := by
      conv_lhs => rw [← b.sum_repr (A (b j))]

      simp only [map_sum, map_zsmul, hbR]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [h2, bR.repr_sum_self]
    rfl
  have htr : (LinearMap.trace ℝ _ ((Matrix.toLin' M).restrictScalars ℝ)) =
      ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bR, hmat, LinearMap.trace_eq_matrix_trace ℤ b]
    simp [Matrix.trace]
  rw [trace_real_restrict] at htr
  have : ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = (((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) : ℂ) :=
    (Complex.ofReal_intCast _).symm
  rw [this, ← htr, Complex.add_conj]

theorem coeff_eq_zero_of_sum_embeddings {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℂ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, a τ * τ (c : F) = 0) (τ : F →+* ℂ) : a τ = 0 := by
  let r : (F →+* ℂ) → (𝓞 F →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hr : Function.Injective r := by
    intro σ σ' hs
    have : σ.comp (algebraMap (𝓞 F) F) = σ'.comp (algebraMap (𝓞 F) F) := by
      ext x; exact DFunLike.congr_fun hs x
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) this
  have hli : LinearIndependent ℂ (fun σ : F →+* ℂ => ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ)) :=
    (linearIndependent_monoidHom (𝓞 F) ℂ).comp r hr
  have hsum : ∑ σ, a σ • ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ) = 0 := by
    funext c
    simpa [r, Finset.sum_apply] using h c
  exact (Fintype.linearIndependent_iff.mp hli) a hsum τ

theorem _root_.GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)) (hQ : IsPeriod D' ρ Q)
    (τ : D.F →+* ℂ) :
    Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) +
      Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  set φ := ρ.comp (algebraMap (𝓞 D.F) D.O) with hφ
  let d : (D.F →+* ℂ) → ℕ := fun σ => Module.finrank ℂ (eigSp φ σ)
  obtain ⟨hlin, hinj, hdisc, hspan, -⟩ := hQ

  have hrank : Module.finrank ℤ D'.La = (D.m * D.n) * Module.finrank ℚ D.F := by
    rw [finrank_eq_two_mul_of_period Q hinj hdisc hspan]
    have h2 : Module.finrank ℚ D.F = 2 * InfinitePlace.nrComplexPlaces D.F := IsTotallyComplex.finrank D.F
    unfold Datum.g
    rw [h2]
    rw [show D.m * D.n * (2 * InfinitePlace.nrComplexPlaces D.F) = 2 * (D.m * D.n * InfinitePlace.nrComplexPlaces D.F) by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num)]

  let cj : (D.F →+* ℂ) ≃ (D.F →+* ℂ) :=
    { toFun := fun σ => (starRingEnd ℂ).comp σ
      invFun := fun σ => (starRingEnd ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have key : ∀ c : 𝓞 D.F, ∑ σ : D.F →+* ℂ, (((d σ + d (cj σ) : ℕ) : ℂ) - ((D.m * D.n : ℕ) : ℂ)) * σ (c : D.F) = 0 := by
    intro c
    let A : D'.La →+ D'.La := DistribSMul.toAddMonoidHom D'.La (algebraMap (𝓞 D.F) D.O c)
    have hA : ∀ x, Q (A x) = φ c *ᵥ Q x := fun x => hlin _ x
    have h1 := trace_int_eq_of_period Q (φ c) A hinj hdisc hspan hA
    have h2 := GlobalTheory.T.trace_ringOfIntegers_action_lattice_eq D.F D.O D'.La (D.m * D.n) hrank c
    have h3 := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g φ c
    have hconj : (starRingEnd ℂ) (φ c).trace = ∑ σ : D.F →+* ℂ, (d (cj σ) : ℂ) * σ (c : D.F) := by

      rw [h3, map_sum]
      simp only [map_mul, Complex.conj_natCast]
      exact (Fintype.sum_equiv cj _ _ (fun σ => by
        show (d σ : ℂ) * (starRingEnd ℂ) (σ (c : D.F)) = (d (cj (cj σ)) : ℂ) * (cj σ) (c : D.F)
        have : cj (cj σ) = σ := cj.left_inv σ
        rw [this]; rfl))
    have : ∑ σ : D.F →+* ℂ, ((d σ + d (cj σ) : ℕ) : ℂ) * σ (c : D.F) = ((D.m * D.n : ℕ) : ℂ) * ∑ σ : D.F →+* ℂ, σ (c : D.F) := by
      rw [← h2, h1, hconj, h3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      push_cast; ring
    rw [Finset.mul_sum] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this]
    simp
  have := coeff_eq_zero_of_sum_embeddings _ key τ
  have h' : ((d τ + d (cj τ) : ℕ) : ℂ) = ((D.m * D.n : ℕ) : ℂ) := sub_eq_zero.mp this
  exact_mod_cast h'

end GlobalTheory.UPel.HT.LieType.DimSum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem pullQuasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ _ _ φ hB hq hA
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA (isGrpPullback_pullback A t)
  have hinv : IsMonHom e.inv := inferInstance
  have hinvφ : e.inv.left ≫ φ = pullback.fst A.hom t := by
    rw [← hφ, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hmap : ∀ (X M : Over Y) [MonObj M] (f : X ⟶ M) (n : ℕ),
      (Over.pullback t).map (f ^ n) = ((Over.pullback t).map f) ^ n := fun X M _ f n => by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply]
  have hid : ∀ (M : Over Y) [GrpObj M], (Over.pullback t).map ((𝟙 M) ^ k) = (𝟙 _) ^ k := fun M _ => by
    rw [hmap, CategoryTheory.Functor.map_id]
  refine ⟨(Over.pullback t).obj B, inferInstance, inferInstance, pullback.fst B.hom t,
    e.hom ≫ (Over.pullback t).map ψ, (Over.pullback t).map ψ' ≫ e.inv,
    ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t B hB, isGrpPullback_pullback B t, ⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · calc (e.hom ≫ (Over.pullback t).map ψ) ≫ (Over.pullback t).map ψ' ≫ e.inv
          = e.hom ≫ (Over.pullback t).map (ψ ≫ ψ') ≫ e.inv := by simp
      _ = e.hom ≫ ((𝟙 ((Over.pullback t).obj A)) ^ k) ≫ e.inv := by rw [h1, hid]
      _ = (𝟙 A₁) ^ k := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, e.hom_inv_id]
  · calc ((Over.pullback t).map ψ' ≫ e.inv) ≫ e.hom ≫ (Over.pullback t).map ψ
          = (Over.pullback t).map (ψ' ≫ ψ) := by simp
      _ = (𝟙 _) ^ k := by rw [h2, hid]
  · rw [Over.comp_left, Category.assoc]
    show φ ≫ ψ.left = e.hom.left ≫ pullback.lift _ _ _ ≫ pullback.fst B.hom t
    rw [pullback.lift_fst, ← Category.assoc, hφ]
  · rw [Over.comp_left, Category.assoc, hinvφ]
    show pullback.fst B.hom t ≫ ψ'.left = pullback.lift _ _ _ ≫ pullback.fst A.hom t
    rw [pullback.lift_fst]

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  first | (exact @GlobalTheory.FormsLocus.polys_ker) | (exact GlobalTheory.FormsLocus.polys_ker) | (intros; apply GlobalTheory.FormsLocus.polys_ker  <;> assumption)
end
