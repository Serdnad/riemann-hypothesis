module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle146
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramified
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
import Mathlib.RingTheory.Henselian
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
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_integral_reduction : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  intro K K' d φ hU B ψ hψ hσ hO hl hsep hint s hres
  set S := Algebra.adjoin K.O ({B.g} : Set B.A) with hSdef
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  let f0 : K'.O →+* S := (ψ.comp (algebraMap K'.O K'.E)).codRestrict S hO
  letI : Algebra K'.O S := f0.toAlgebra
  let ι : S →ₐ[K'.O] B.A := { S.val.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ι := Subtype.val_injective
  haveI : Module.Finite K.O S := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : Module.Finite K'.O S := by
    obtain ⟨T, hT⟩ := (inferInstance : Module.Finite K.O S).fg_top
    refine ⟨⟨T, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.O (T : Set S) := hT ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨y', hy'⟩ := GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers K K' d φ hU a
      have h : a • x = y' • x := by
        apply Subtype.ext
        rw [Algebra.smul_def, Algebra.smul_def, MulMemClass.coe_mul, MulMemClass.coe_mul]
        change algebraMap K.O B.A a * (x : B.A) = ψ (algebraMap K'.O K'.E y') * (x : B.A)
        rw [hy', hψ, ← IsScalarTower.algebraMap_apply]
      rw [h]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span K'.E (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun y hy0 => ?_
    clear hy0
    have hy : y ∈ Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) := GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable K B hsep ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨B.g ^ i, pow_mem (Algebra.self_mem_adjoin_singleton K.O B.g) i⟩, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  haveI : IsLocalRing S := hl
  obtain ⟨n, b, hb⟩ := GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq K'.O K'.E B.A S ι hinj hspan
  let x0 : S := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  refine ⟨(LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0)).charpoly, (hb x0).symm, ?_⟩
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← Matrix.charpoly_map]
  set t : S := x0 - algebraMap K'.O S s with ht
  have htm : t ∈ IsLocalRing.maximalIdeal S := by
    rw [ht, ← Ideal.Quotient.eq]; exact hres
  have hsplit : LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0) =
      LinearMap.toMatrix b b (LinearMap.mulLeft K'.O t) + Matrix.scalar (Fin n) s := by
    have : LinearMap.mulLeft K'.O x0 = LinearMap.mulLeft K'.O t + s • LinearMap.id := by
      ext y; simp [ht, Algebra.smul_def, sub_mul]
    rw [this, map_add (f := _), map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]; rfl
  rw [hsplit, Matrix.map_add _ (map_add _)]
  have hsc : (Matrix.scalar (Fin n) s).map (IsLocalRing.residue K'.O) = Matrix.scalar (Fin n) (IsLocalRing.residue K'.O s) := by
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp
  rw [hsc]
  exact GlobalTheory.T.charpoly_nilpotent_add_scalar' _ n _ _ (GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' K'.O S n b t htm)

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResMult

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem not_isRoot_cofactor : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y =
      f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
      p.natDegree = d * r.natDegree →
      p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
      ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  intro K K' d φ hU s hgen p r c hp hr hrbar hdeg heq
  classical
  set φO := intMap hU with hφO
  have hspec : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) :=
    RingHom.ext fun a => intMap_spec hU a
  have hmax : ∀ a ∈ IsLocalRing.maximalIdeal K.O, φO a ∈ IsLocalRing.maximalIdeal K'.O := by
    intro a ha
    rw [← map_maximalIdeal hU]
    exact Ideal.mem_map_of_mem _ ha
  haveI : IsLocalHom φO := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hmax a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
  let k := IsLocalRing.ResidueField K.O
  let k' := IsLocalRing.ResidueField K'.O
  let ψ : k →+* k' := IsLocalRing.ResidueField.map φO
  have hψ : ∀ a : K.O, ψ (IsLocalRing.residue K.O a) = IsLocalRing.residue K'.O (φO a) :=
    fun a => IsLocalRing.ResidueField.map_residue φO a
  letI : Algebra k k' := ψ.toAlgebra
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype k' := Fintype.ofFinite k'
  set Q := Fintype.card k with hQdef
  have hQ : Q = K.q ^ 2 := by rw [hQdef, ← Nat.card_eq_fintype_card]; exact K.card_res
  have hQ' : Fintype.card k' = Q ^ d := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (IsLocalRing.ResidueField K'.O) = _
    rw [K'.card_res, hU.1, hQ, ← pow_mul, ← pow_mul, mul_comm]
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hd : d ≠ 0 := hU.ne_zero
  set F := FiniteField.frobeniusAlgHom k k' with hF
  have hFpow : ∀ (i : ℕ) (x : k'), (F ^ i) x = x ^ (Q ^ i) := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
      show (x ^ Q ^ i) ^ Q = x ^ Q ^ (i + 1)
      rw [← pow_mul, ← pow_succ]

  have hrc : r * c = p.map φO := by
    apply Polynomial.map_injective _ (IsFractionRing.injective K'.O K'.E)
    rw [← heq, Polynomial.map_map, hspec]
  set sb := IsLocalRing.residue K'.O s with hsb
  set P := (r * c).map (IsLocalRing.residue K'.O) with hP
  have hP2 : P = (p.map (IsLocalRing.residue K.O)).map ψ := by
    rw [hP, hrc, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hPmon : P.Monic := by rw [hP2]; exact (hp.map _).map _
  have hP0 : P ≠ 0 := hPmon.ne_zero
  have hPdeg : P.natDegree = d * r.natDegree := by
    rw [hP2, (hp.map _).natDegree_map, hp.natDegree_map, hdeg]
  have hPmul : P = r.map (IsLocalRing.residue K'.O) * c.map (IsLocalRing.residue K'.O) := by
    rw [hP, Polynomial.map_mul]
  have hmu : rootMultiplicity sb P = r.natDegree + rootMultiplicity sb (c.map (IsLocalRing.residue K'.O)) := by
    rw [hPmul, rootMultiplicity_mul (hPmul ▸ hP0), hrbar, rootMultiplicity_X_sub_C_pow]

  have hconj : ∀ i : ℕ, rootMultiplicity sb P ≤ rootMultiplicity (sb ^ (Q ^ i)) P := by
    intro i
    have h := le_rootMultiplicity_map (f := ((F ^ i : k' →ₐ[k] k') : k' →+* k')) (p := P) ?_ sb
    · have hPFi : P.map ((F ^ i : k' →ₐ[k] k') : k' →+* k') = P := by
        rw [hP2, Polynomial.map_map]
        congr 1
        exact RingHom.ext fun x => (F ^ i).commutes x
      rw [hPFi] at h
      simpa [hFpow] using h
    · rw [hP2, Polynomial.map_map]
      have : ((F ^ i : k' →ₐ[k] k') : k' →+* k').comp ψ = ψ := RingHom.ext fun x => (F ^ i).commutes x
      rw [this, ← hP2]; exact hP0

  have hinj : ∀ i j, i < j → j < d → sb ^ (Q ^ i) ≠ sb ^ (Q ^ j) := by
    intro i j hij hjd h
    obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
    have hm : 0 < m := by omega
    have hfix : sb ^ (Q ^ m) = sb := by
      apply RingHom.injective ((F ^ i : k' →ₐ[k] k') : k' →+* k')
      rw [AlgHom.coe_toRingHom, hFpow, hFpow, h, ← pow_mul, pow_add, mul_comm]
    have hall : ∀ y : k', y ^ (Q ^ m) = y := by
      intro y
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨f, z, hz, hy⟩ := hgen y'
      have hy' : y' = f.eval₂ φO s + z := by
        apply IsFractionRing.injective K'.O K'.E
        rw [hy, map_add (f := _), Polynomial.hom_eval₂, hspec]
      have hres : IsLocalRing.residue K'.O y' = f.eval₂ (ψ.comp (IsLocalRing.residue K.O)) sb := by
        rw [hy', map_add (f := _), (IsLocalRing.residue_eq_zero_iff z).2 hz, add_zero, Polynomial.hom_eval₂]
        congr 1
      have hev := Polynomial.hom_eval₂ f (ψ.comp (IsLocalRing.residue K.O))
        ((F ^ m : k' →ₐ[k] k') : k' →+* k') sb
      have hc : ((F ^ m : k' →ₐ[k] k') : k' →+* k').comp (ψ.comp (IsLocalRing.residue K.O)) =
          ψ.comp (IsLocalRing.residue K.O) := RingHom.ext fun a => (F ^ m).commutes (IsLocalRing.residue K.O a)
      rw [hc, AlgHom.coe_toRingHom, hFpow m sb, hfix, hFpow] at hev
      rw [hres]; exact hev
    have hQm : 1 < Q ^ m := Nat.one_lt_pow hm.ne' hQ1
    have hcard : Fintype.card k' ≤ Q ^ m := by
      have h1 := card_le_degree_of_subset_roots (p := (X ^ (Q ^ m) - X : k'[X])) (Z := Finset.univ) (by
        intro y _
        rw [mem_roots (Polynomial.X_pow_sub_X_ne_zero (R := k') hQm)]
        simp [IsRoot, hall y])
      rwa [Polynomial.natDegree_X_pow_sub_X (R := k') hQm, Finset.card_univ] at h1
    rw [hQ'] at hcard
    exact absurd hcard (not_le.2 (Nat.pow_lt_pow_right hQ1 (by omega)))

  let t : ℕ → k' := fun i => sb ^ (Q ^ i)
  have htinj : Set.InjOn t (Finset.range d) := by
    intro i hi j hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hinj i j h' (by simpa using hj))
    · exact h'
    · exact absurd h.symm (hinj j i h' (by simpa using hi))
  set S := (Finset.range d).image t with hSdef
  have hS : S.card = d := by rw [Finset.card_image_of_injOn htinj, Finset.card_range]
  have hsum1 : d * rootMultiplicity sb P ≤ ∑ x ∈ S, P.roots.count x := by
    calc d * rootMultiplicity sb P = ∑ _x ∈ S, rootMultiplicity sb P := by
          rw [Finset.sum_const, hS, smul_eq_mul]
      _ ≤ ∑ x ∈ S, P.roots.count x := Finset.sum_le_sum fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
          rw [count_roots]; exact hconj i
  have hsum2 : ∑ x ∈ S, P.roots.count x ≤ Multiset.card P.roots := by
    calc ∑ x ∈ S, P.roots.count x ≤ ∑ x ∈ S ∪ P.roots.toFinset, P.roots.count x :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
          (Finset.sum_subset Finset.subset_union_right fun x _ hx =>
            Multiset.count_eq_zero.2 (by simpa using hx)).symm
      _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
  have hle : d * rootMultiplicity sb P ≤ d * r.natDegree :=
    hsum1.trans (hsum2.trans ((card_roots' P).trans hPdeg.le))
  have hle' := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hd)
  have hc0 : c.map (IsLocalRing.residue K'.O) ≠ 0 := right_ne_zero_of_mul (hPmul ▸ hP0)
  intro hroot
  have := (rootMultiplicity_pos hc0).2 hroot
  omega

end GlobalTheory.UnitLemma.Unr.ResMult
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem isLat_iff_of_coe_eq {O O' E E' A : Type} [CommRing O] [CommRing O'] [Field E] [Field E'] [CommRing A]
    [Algebra O A] [Algebra O' A] [Algebra E A] [Algebra E' A] {d : ℕ} (u : Fin d → O')
    (h1 : ∀ a : O, ∃ b : O', algebraMap O' A b = algebraMap O A a)
    (h2 : ∀ y : O', ∃ a : Fin d → O, algebraMap O' A y = ∑ i, algebraMap O A (a i) * algebraMap O' A (u i))
    (h3 : ∀ e : E, ∃ e' : E', algebraMap E' A e' = algebraMap E A e)
    (h4 : ∀ e' : E', ∃ (e : E) (b : O'), algebraMap E' A e' = algebraMap E A e * algebraMap O' A b)
    (L : Submodule O' A) (M : Submodule O A) (h : (L : Set A) = (M : Set A)) :
    IsLat O' E' L ↔ IsLat O E M := by
  classical
  have hm : ∀ y, y ∈ L ↔ y ∈ M := fun y => by
    rw [← SetLike.mem_coe, h, SetLike.mem_coe]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨S, hS⟩
    refine ⟨(Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact (hm _).1 (L.smul_mem _ (hS ▸ Submodule.subset_span hp.2))
    · intro x hx
      have hx' : x ∈ Submodule.span O' (S : Set A) := hS ▸ (hm x).2 hx
      set N := Submodule.span O
        ((((Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2 : Finset A)) : Set A) with hN
      have key : ∀ c : O', c • x ∈ N := by
        clear hx
        induction hx' using Submodule.span_induction with
        | mem s hs =>
          intro c
          obtain ⟨a, ha⟩ := h2 c
          rw [Algebra.smul_def, ha, Finset.sum_mul]
          refine N.sum_mem fun i _ => ?_
          rw [mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
          refine N.smul_mem _ (Submodule.subset_span ?_)
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
          exact ⟨(i, s), ⟨Finset.mem_univ _, hs⟩, rfl⟩
        | zero => intro c; simp
        | add x z _ _ hx hz => intro c; rw [smul_add]; exact N.add_mem (hx c) (hz c)
        | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
      simpa using key 1
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, h, ← hS]
      exact Submodule.subset_span
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set A) := hS ▸ (hm x).1 hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem s hs => exact Submodule.subset_span hs
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul e x _ hx =>
        obtain ⟨b, hb⟩ := h1 e
        rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hx
  · intro hL
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E' (L : Set A) := hL ▸ Submodule.mem_top
    have key : ∀ c : E', c • x ∈ Submodule.span E (M : Set A) := by
      induction hx' using Submodule.span_induction with
      | mem s hs =>
        intro c
        obtain ⟨e, b, hb⟩ := h4 c
        rw [Algebra.smul_def, hb, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).1 (L.smul_mem _ hs)))
      | zero => intro c; simp
      | add x z _ _ hx hz => intro c; rw [smul_add]; exact add_mem (hx c) (hz c)
      | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
    simpa using key 1
  · intro hM
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
    induction hx' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ((hm s).2 hs)
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      obtain ⟨b, hb⟩ := h3 e
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx

theorem exists_eq_base_mul_int {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E) :
    ∃ (e : K.E) (b : K'.O), z = φ e * algebraMap K'.O K'.E b := by
  by_cases hz : z = 0
  · exact ⟨0, 0, by simp [hz]⟩
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hφ0 : φ π ≠ 0 := by simpa using hπ0
  set v := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv
  have h1 : WithZero.log (v (φ π)) = -1 := by
    have := hU.2.2.1 π
    unfold val at this
    rw [hπ, WithZero.log_exp, ← hv] at this
    omega
  have hv0 : v (φ π) ≠ 0 := by simpa using hφ0
  have hz0 : v z ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' (z * φ π ^ (WithZero.log (v z))) (by
    unfold val
    rw [← hv, map_mul, map_zpow₀, WithZero.log_mul hz0 (zpow_ne_zero _ hv0), WithZero.log_zpow, h1]
    simp)
  refine ⟨π ^ (-WithZero.log (v z)), b, ?_⟩
  rw [hb, map_zpow₀, zpow_neg]
  have := zpow_ne_zero (WithZero.log (v z)) hφ0
  field_simp

theorem isLat_overExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  intro K K' d φ hU B ψ hψ hσ L M h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  have hO' : ∀ b : K'.O, algebraMap K'.O B.A b = ψ (algebraMap K'.O K'.E b) := fun _ => rfl
  have hE' : ∀ b : K'.E, algebraMap K'.E B.A b = ψ b := fun _ => rfl
  have hO : ∀ a : K.O, algebraMap K.O B.A a = ψ (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hψ, ← IsScalarTower.algebraMap_apply]
  have key := isLat_iff_of_coe_eq (O := K.O) (O' := K'.O) (E := K.E) (E' := K'.E) (A := B.A) u ?_ ?_ ?_ ?_
  · exact key L M h
  · intro a
    obtain ⟨b, hb⟩ := exists_int_image hU a
    exact ⟨b, by rw [hO', hO, hb]⟩
  · intro y
    obtain ⟨a, ha⟩ := hu y
    refine ⟨a, ?_⟩

    rw [hO', ha, map_sum]
    simp only [map_mul, hO, hO']
  · intro e
    exact ⟨φ e, by rw [hE', hψ]⟩
  · intro z
    obtain ⟨e, b, hb⟩ := exists_eq_base_mul_int hU z
    exact ⟨e, b, by rw [hE', hO', ← hψ, ← map_mul, ← hb]⟩

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem isIntegral_overExt_iff (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (a : B.A) : @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  classical
  choose ι hι using fun c => exists_int_image hU c
  have inj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  let f : K.O →+* K'.O :=
    { toFun := ι
      map_one' := inj (by rw [hι]; simp)
      map_mul' := fun x y => inj (by simp [hι])
      map_zero' := inj (by rw [hι]; simp)
      map_add' := fun x y => inj (by simp [hι]) }
  have hf : ∀ c, algebraMap K'.O K'.E (f c) = φ (algebraMap K.O K.E c) := hι
  letI : Algebra K.O K'.O := f.toAlgebra
  letI iC : Algebra K'.O B.A := (overExt φ B ψ hψ hσ).aO
  have hC : ∀ y : K'.O, algebraMap K'.O B.A y = ψ (algebraMap K'.O K'.E y) := fun _ => rfl
  haveI : IsScalarTower K.O K'.O B.A := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A c, RingHom.algebraMap_toAlgebra, hC]
    show _ = ψ (algebraMap K'.O K'.E (f c))
    rw [hf, hψ]
  show IsIntegral K'.O a ↔ IsIntegral K.O a
  constructor
  · intro h
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
    haveI : Module.Finite K.O K'.O := by
      refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
      obtain ⟨c, hc⟩ := hu y
      have hy : y = ∑ i, c i • u i := by
        apply inj

        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
      rw [hy]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp
    haveI : Algebra.IsIntegral K.O K'.O := Algebra.IsIntegral.of_finite K.O K'.O
    exact isIntegral_trans (R := K.O) (A := K'.O) a h
  · intro h
    exact h.tower_top

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | exact GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit <;> assumption)
end
