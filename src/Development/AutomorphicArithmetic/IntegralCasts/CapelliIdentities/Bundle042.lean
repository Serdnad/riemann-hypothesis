module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g

    rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm
end

section

theorem UpperTheory.Reformulated.B.Qe30.transfer_of_comp_subtype.{u_1} :
    ∀ {Γ : Type u_1} [inst : Group Γ] (H : Subgroup Γ)
    [inst_1 : H.FiniteIndex] (g : Γ),
    ((Abelianization.of.comp H.subtype).transfer : Γ → Abelianization Γ) g =
      (Abelianization.of : Γ → Abelianization Γ) g ^ H.index := by
  intro Γ _ H _ g
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul, map_mul, map_inv, map_pow,
    inv_mul_cancel_comm]
end

section

private theorem UpperTheory.Reformulated.B.Yt3.mem_conj {G : Type} [Group G] {K : Subgroup G} {g y : G} :
    y ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem UpperTheory.Reformulated.B.Yt3.exists_reps :
    ∀ {G : Type} [inst : Group G] {K : Subgroup G} {g : G},
      (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).relIndex K ≠ (0 : ℕ) →
        ∃ (R : Finset G),
          (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
            ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K g h
  classical
  set H : Subgroup K :=
    (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).subgroupOf K with hH
  have hfin : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero h
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (a b : K) (k : G), k ∈ K →
      ((((a : G) * g)⁻¹ * ((b : G) * g * k) ∈ K) ↔ (a : K ⧸ H) = (b : K ⧸ H)) := by
    intro a b k hk
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, UpperTheory.Reformulated.B.Yt3.mem_conj,
      ← mul_assoc, K.mul_mem_cancel_right hk]
    simp [mul_assoc]
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, (mul_one _).symm⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨(((((⟨k₁, hk₁⟩ : K) : K ⧸ H)).out : K) : G) * g,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨k₁, hk₁⟩ k₂ hk₂).2 (QuotientGroup.out_eq' _)
    · rintro γ ⟨hγ, hx⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      have := (key _ ⟨k₁, hk₁⟩ k₂ hk₂).1 hx
      rw [QuotientGroup.out_eq'] at this
      rw [this]
end

section

theorem UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) →
        IsUnit (↑H.index : R) →
          H.index ≠ (0 : ℕ) → ∃ (m : M), ∀ (g : Q), f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH hu hn
  classical
  haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn
  have hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  let F : Q ⧸ H → M := fun x => f x.out
  have hF : ∀ a : Q, F (a : Q ⧸ H) = f a := fun a =>
    hconst _ _ (QuotientGroup.out_eq' _)
  have hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + π g (F x) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H) := rfl
      rw [h2, hF, hF, hf]
  have hcard : Fintype.card (Q ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + π g (∑ x, F x) := by
    intro g
    calc ∑ x, F x = ∑ x, F (g • x) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ x : Q ⧸ H, (f g + π g (F x)) := Finset.sum_congr rfl fun x _ => hstep g x
      _ = _ := by

        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
        Nat.cast_smul_eq_nsmul]
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨-(c • ∑ x, F x), fun g => ?_⟩
  have h3 : (H.index : R) • f g = ∑ x, F x - π g (∑ x, F x) := eq_sub_of_add_eq (hsum g).symm
  calc f g = c • ((H.index : R) • f g) := by rw [smul_smul, hc, one_smul]
    _ = _ := by
      rw [h3, map_neg, map_smul, smul_sub]
      abel
end

section

theorem UpperTheory.Reformulated.B.Qe18.hc_avg :
    ∀ {k D M : Type} [inst : Field k] [inst_1 : Group D]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module k M] (ρ : Representation k D M) (N : Subgroup D),
    (↑N.index : k) ≠ (0 : k) →
      ∀ (z : D → M),
        (∀ (g h : D), z (g * h) = z g + ((ρ : D → M →ₗ[k] M) g : M → M) (z h)) →
          (∀ s ∈ N, z s = (0 : M)) → ∃ (m : M), ∀ (g : D), z g = ((ρ : D → M →ₗ[k] M) g : M → M) m - m := by
  intro k D M _ _ _ _ ρ N hN z hz h0
  have hidx : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : Fintype (D ⧸ N) := Subgroup.fintypeOfIndexNeZero hidx
  have hcos : ∀ a b : D, (a : D ⧸ N) = (b : D ⧸ N) → z a = z b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have h1 := hz a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  have hcard : Fintype.card (D ⧸ N) = N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have key : ∀ g : D, ∑ q : D ⧸ N, z q.out
      = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
    intro g
    have h1 : ∑ q : D ⧸ N, z (g • q).out = ∑ q : D ⧸ N, z q.out :=
      Equiv.sum_comp (MulAction.toPerm g) (fun q : D ⧸ N => z q.out)
    have h2 : ∀ q : D ⧸ N, z (g • q).out = z g + ρ g (z q.out) := by
      intro q
      rw [← hz]
      apply hcos
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.coe_smul_out]
    calc ∑ q : D ⧸ N, z q.out = ∑ q : D ⧸ N, z (g • q).out := h1.symm
      _ = ∑ q : D ⧸ N, (z g + ρ g (z q.out)) := Finset.sum_congr rfl fun q _ => h2 q
      _ = (N.index : k) • z g + ρ g (∑ q : D ⧸ N, z q.out) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  refine ⟨-((N.index : k)⁻¹ • ∑ q : D ⧸ N, z q.out), fun g => ?_⟩
  have h3 : (N.index : k) • z g
      = (∑ q : D ⧸ N, z q.out) - ρ g (∑ q : D ⧸ N, z q.out) :=
    eq_sub_of_add_eq (key g).symm
  calc z g = (N.index : k)⁻¹ • ((N.index : k) • z g) := (inv_smul_smul₀ hN _).symm
    _ = _ := by
      rw [h3, smul_sub, map_neg, map_smul]
      abel
end

section

theorem UpperTheory.Reformulated.B.Qi36.aux :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) → ∃ (m : M), ∀ (g : Q), H.index • f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH
  by_cases h0 : H.index = 0
  · exact ⟨0, fun g => by simp [h0]⟩
  haveI : Finite (Q ⧸ H) := Nat.finite_of_card_ne_zero h0
  letI : Fintype (Q ⧸ H) := Fintype.ofFinite _
  have key : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [hH _ hm, map_zero, add_zero, mul_inv_cancel_left] at h1
    exact h1.symm
  have step : ∀ (g : Q) (x : Q ⧸ H), f (g • x).out = f g + π g (f x.out) := by
    intro g x
    rw [← hf]
    apply key
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
  refine ⟨-∑ x : Q ⧸ H, f x.out, fun g => ?_⟩
  have hs : ∑ x : Q ⧸ H, f (g • x).out = ∑ x : Q ⧸ H, f x.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun x : Q ⧸ H => f x.out)
  simp only [step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs

  rw [← map_sum] at hs
  rw [Subgroup.index, Nat.card_eq_fintype_card, map_neg, sub_neg_eq_add,
    eq_sub_of_add_eq hs]
  abel
end

section

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, hb]
  · simp

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro rfl <;> simp

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g) = g := by
  intro m R _ g
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl]
  rw [mul_assoc, mul_assoc, mul_assoc, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, mul_one, ← mul_assoc,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g * UpperTheory.Reformulated.B.AntidiagonalConjugation.theta h := by
  intro m R _ g h
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m), UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left *
          ((UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h * r g * (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h)⁻¹).left = _
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
    MulAut.one_apply]
end

section

theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
end
