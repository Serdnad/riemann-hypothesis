module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005

@[expose] public section

section

open NumberField UpperTheory.V.Af.Sol

private theorem exists_proper_nontrivial_normal_of_solvable_not_prime_card (G : Type) [Group G] [Finite G] (hs : IsSolvable G)
    (h1 : Nat.card G ≠ 1) (hp : ¬ (Nat.card G).Prime) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hne
  push_neg at hne
  have hlt : 1 < Nat.card G := by
    have := Nat.card_pos (α := G)
    omega
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hlt
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN => by
        by_cases h : N = ⊥
        · exact Or.inl h
        · exact Or.inr (hne N hN h) }
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hs
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  exact hp (CommGroup.is_simple_iff_prime_card.1 ‹IsSimpleGroup G›)

private theorem rc_of_intermediateField_stable_under_complexConj {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    [IsCMField M] (K : IntermediateField F M)
    (hK : ∀ x ∈ K, IsCMField.complexConj M x ∈ K) : RC K := by
  have hext : ∀ φ : K →+* ℂ, ∃ Φ : M →+* ℂ, ∀ x : K, Φ x = φ x := by
    intro φ
    letI : Algebra K ℂ := φ.toAlgebra
    refine ⟨(IsAlgClosed.lift : M →ₐ[K] ℂ).toRingHom, fun x => ?_⟩
    exact (IsAlgClosed.lift : M →ₐ[K] ℂ).commutes x
  let τ : K ≃+* K :=
    { toFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      invFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      left_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      right_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul])
      map_add' := fun x y => Subtype.ext (by simp [map_add (f := _)]) }
  let σ : Gal(K/ℚ) := τ.toRatAlgEquiv
  have hσ : ∀ x : K, ((σ x : K) : M) = IsCMField.complexConj M x := fun x => rfl
  have hconj : ∀ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ := by
    intro φ
    obtain ⟨Φ, hΦ⟩ := hext φ
    unfold ComplexEmbedding.IsConj
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hΦ]
    show _ = φ (σ x)
    rw [← hΦ, hσ, IsCMField.complexEmbedding_complexConj]
  by_cases h1 : σ = 1
  · left
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    have := hconj w.embedding
    rw [h1] at this
    unfold ComplexEmbedding.IsConj at this
    rw [this]
    rfl
  · right
    haveI : IsTotallyComplex K :=
      ⟨fun w => InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff (hconj _)).1 h1)⟩
    obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hord : Nat.card (Subgroup.zpowers σ) = 2 := by
      rw [Nat.card_zpowers]
      exact ComplexEmbedding.orderOf_isConj_two_of_ne_one (hconj φ0) h1
    haveI : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
    haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    let L : IntermediateField ℚ K := FixedPoints.intermediateField (Subgroup.zpowers σ)
    have hfix : ∀ x : L, σ (x : K) = x := fun x => x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    haveI : IsTotallyReal L := ⟨fun w => by
      obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
      dsimp only
      rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
        ComplexEmbedding.isReal_iff]
      ext x
      have h := RingHom.congr_fun (hconj W.embedding) (x : K)
      rw [ComplexEmbedding.conjugate_coe_eq] at h ⊢
      simp only [RingHom.comp_apply] at h ⊢
      rw [show algebraMap L K x = (x : K) from rfl, h]
      exact congrArg W.embedding (hfix x)⟩
    haveI : Algebra.IsQuadraticExtension L K :=
      ⟨by
        rw [Nat.card_eq_fintype_card] at hord
        rw [← hord]
        exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
    exact IsCMField.ofCMExtension L K

theorem UpperTheory.solvable_cm_extension_tower :
    UpperTheory.V.Af.Sol.Tower := by
  intro F M _ _ _ _ _ _ hs hF hM h1 hp
  obtain ⟨N, hN, hbot, htop⟩ := exists_proper_nontrivial_normal_of_solvable_not_prime_card Gal(M/F) hs
    (by rwa [IsGalois.card_aut_eq_finrank]) (by rwa [IsGalois.card_aut_eq_finrank])
  refine ⟨IntermediateField.fixedField N, ?_, ?_, IsGalois.of_fixedField_normal_subgroup N, ?_⟩
  · intro h
    apply htop
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_bot]
  · intro h
    apply hbot
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_top]
  · rcases hM with hM | hM
    · left
      exact IsTotallyReal.of_algebra (IntermediateField.fixedField N) M
    · apply rc_of_intermediateField_stable_under_complexConj
      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      intro n hn
      obtain ⟨Φ⟩ : Nonempty (M →+* ℂ) := inferInstance
      apply Φ.injective
      have h2 := IsCMField.complexEmbedding_complexConj M (Φ.comp n.toRingHom) x
      change Φ (n (IsCMField.complexConj M x)) = (starRingEnd ℂ) (Φ (n x)) at h2
      rw [h2, hx n hn, IsCMField.complexEmbedding_complexConj]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem rcsup_mem_real {L M' : Type} [Field L] [Field M'] (f : L →+* M') (hL : IsTotallyReal L) (x : L) :
    f x ∈ maximalRealSubfield M' := by
  intro φ
  have h : x ∈ maximalRealSubfield L := by
    rw [IsTotallyReal.maximalRealSubfield_eq_top]; trivial
  exact h (φ.comp f)

private theorem rcsup_map_real {M M' : Type} [Field M] [Field M'] (g : M →+* M') {x : M}
    (hx : x ∈ maximalRealSubfield M) : g x ∈ maximalRealSubfield M' :=
  fun φ => hx (φ.comp g)

private theorem rcsup_cm_of_pair {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (d : K) (hd0 : d ≠ 0)
    (hd : ∀ φ : K →+* ℂ, star (φ d) = - φ d)
    (hspan : ∀ y : K, ∃ a ∈ maximalRealSubfield K, ∃ b ∈ maximalRealSubfield K, y = a + b * d) :
    IsCMField K := by
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h0 : (s : K) + (t : K) * d = 0 := by
      simpa [Subfield.smul_def] using hst
    have h1 : φ s + φ t * φ d = 0 := by
      rw [← map_mul, ← map_add (f := _), h0, map_zero]
    have h2 : φ s - φ t * φ d = 0 := by
      have := congrArg star h1
      rw [star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero] at this
      linear_combination this
    have h3 : φ s = 0 := by linear_combination (h1 + h2) / 2
    have hs : (s : K) = 0 := (map_eq_zero φ).mp h3
    have ht : (t : K) = 0 := by
      rw [hs, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hd0
    exact ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro y _
    obtain ⟨a, ha, b, hb, rfl⟩ := hspan y
    have e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d := by
      simp [Subfield.smul_def]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hrk : Module.finrank (maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }
  exact {}

theorem UpperTheory.solvable_cm_compositum_maximalRealSubfield :
    UpperTheory.V.Af.Sol.RCSup := by
  intro L M M' _ _ _ _ _ _ _ f hL htop hM
  rcases hM with hM | hM
  · left
    rw [← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact rcsup_mem_real f hL z
    | algebraMap r => exact rcsup_mem_real _ hM r
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)
  · right
    haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'
    obtain ⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by
      by_contra h
      apply IsCMField.complexConj_ne_one M
      ext x
      by_contra h'
      exact h ⟨x, h'⟩
    set δ : M := x - IsCMField.complexConj M x with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hx.symm
    have hcδ : IsCMField.complexConj M δ = -δ := by
      rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
    have hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ) := by
      intro φ
      have := IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ
      rw [hcδ, map_neg] at this
      exact this.symm
    have hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M' := by
      intro φ
      rw [map_mul, star_mul', hd φ]; ring
    refine rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_
    intro y
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩
    | algebraMap r =>
      refine ⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_,
        algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]
        field_simp
        ring
      · rw [← map_mul, ← map_add (f := _)]
        congr 1
        field_simp
        ring
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ),
        add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq),
        a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.cyclotomic_char_conj_invariant :
    UpperTheory.V.Af.Sol.CycConj := by
  intro F Ω _ _ _ _ _ l _ c hc
  obtain ⟨j, hj⟩ := hc
  haveI : CharZero Ω := j.charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩
  have hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹ := by
    intro x m hm hx
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm
    have hs : Complex.normSq (j x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]; norm_num
    rw [Complex.inv_def, hs]; simp
  set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg
  have hcyc : cyclotomicCharacter Ω l g = -1 := by
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow]
    have hk : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
    rw [← modularCyclotomicCharacter.unique Ω _ g (c := -1)]
    · simp
    · intro t ht
      have ht' : (t : Ω) ^ (l ^ n) = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      have hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
      obtain ⟨m, hm⟩ := hdvd
      have hne : (t : Ω) ≠ 0 := t.ne_zero
      have key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, hm, pow_mul, ht', one_pow]
      rw [key]
      exact hinv _ (l ^ n) (NeZero.ne _) ht'
  show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1
  have : ReciprocityTheory.Gal.cycZ F Ω l c = -1 := hcyc
  rw [this]
  ext; simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem UpperTheory.semisimple_restriction_normal_subgroup {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : G → V →ₗ[K] V)
    (hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v) (hone : ∀ v, ρ 1 v = v)
    (N : Subgroup G) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hC, hUC⟩ := hss (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases htriv : C = ⊥
  · have hU := hUC.sup_eq_top
    rw [htriv, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    have := hv 1
    rwa [hone] at this
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hC g v hv, htriv, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hUC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  exact fun g => key g s hs

theorem UpperTheory.semisimpleModule_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Sol.SsRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  obtain ⟨W', h1, h2⟩ := UpperTheory.semisimple_restriction_normal_subgroup
    (fun g : Γ => Matrix.mulVecLin (r g : Matrix (Fin n) (Fin n) k))
    (by
      intro a b v
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul])
    (by
      intro v
      simp only [Matrix.mulVecLin_apply, map_one, Units.val_one, Matrix.one_mulVec])
    φ.range hN hss W (by
      rintro _ ⟨g, rfl⟩ v hv
      exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_representation_image_spec :
    UpperTheory.V.Af.Sol.GalRange := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  let ρ : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hker : (resG K M Ω).range = ρ.ker := by
    ext σ
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨τ, rfl⟩
      ext x
      apply (algebraMap M Ω).injective
      rw [show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp [resG]
    · intro h
      have hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x := by
        intro x
        have := AlgEquiv.restrictNormal_commutes σ M x
        rw [show σ.restrictNormal M = ρ σ from rfl, h] at this
        simpa using this.symm
      refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
      ext x
      rfl
  refine ⟨hker ▸ ρ.normal_ker, ?_⟩
  rw [hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic :
    UpperTheory.V.Af.Sol.FrobConj → UpperTheory.V.Af.Sol.EigBasic → UpperTheory.V.Af.Sol.InvSat := by
  intro hFC hEB K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat' hatt
  have hbad := Filter.eventually_cofinite.1 hatt.2
  have himg := hbad.image (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
  have hev := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M) himg.compl_mem_cofinite
  filter_upwards [hev] with w hw w' hw'
  have good : ∀ u : HeightOneSpectrum (𝓞 M), u.under (𝓞 K) = w.under (𝓞 K) →
      ∃ B, sat' u B ∧ FrobEig ι (r.comp (resG K M Ω)) u (algSat n (normV u) B) := by
    intro u hu
    by_contra hn
    exact hw ⟨u, hn, hu⟩
  obtain ⟨B, hB, hE⟩ := good w rfl
  obtain ⟨B', hB', hE'⟩ := good w' hw'
  obtain ⟨hN, hT⟩ := hFC K M Ω l ι n r w w' hw'
  have h1 := hT _ hE
  rw [← hN] at h1
  have hBB : B = B' := (hEB M Ω l ι w').2.2 n _ B B' h1 hE'
  exact ⟨B, hB, hBB ▸ hB'⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem conj_val {K M Ω : Type} [Field K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] (hM : RC M) :
    ∃ s : M → M, ∀ c : _root_.Formalism.ConjugateSelfDual.G K Ω, IsConjEl c → ∀ x : M, c (algebraMap M Ω x) = algebraMap M Ω (s x) := by
  rcases hM with hM | hM
  · refine ⟨id, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    have h : ComplexEmbedding.IsReal (j.comp (algebraMap M Ω)) := IsTotallyReal.complexEmbedding_isReal _
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 h) x
  · refine ⟨fun x => IsCMField.complexConj M x, fun c hc x => ?_⟩
    obtain ⟨j, hj⟩ := hc
    refine j.injective ?_
    rw [hj]
    exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm
end
