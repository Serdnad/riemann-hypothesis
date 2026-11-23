module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.EtaleCohomology.EtaleSheaves.Bundle001
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import GroundTheory.FunctionField.PlaceBridge
public import GroundTheory.FunctionField.ValuationAevalSubCoeffZeroLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory

set_option backward.isDefEq.respectTransparency false in
private theorem hb_step {C : Type*} [Category C] [Preadditive C] (K D : CochainComplex C ℤ)
    (H : ∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 →
      ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f)
    (n p₀ : ℤ) (z : Cochain K D n) (hz : δ n (n + 1) z = 0)
    (hv : ∀ (p q : ℤ) (hpq : p + n = q), p₀ < p → z.v p q hpq = 0) :
    ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q), p₀ ≤ p →
      (z - δ (n - 1) n γ).v p q hpq = 0 := by
  have hf : z.v p₀ (p₀ + n) rfl ≫ D.d (p₀ + n) (p₀ + n + 1) = 0 := by
    have h0 := congrArg (fun c => Cochain.v c p₀ (p₀ + n + 1) (by omega)) hz
    simp only [Cochain.zero_v] at h0
    rw [δ_v n (n + 1) rfl z p₀ (p₀ + n + 1) (by omega) (p₀ + n) (p₀ + 1) (by omega) rfl,
      hv (p₀ + 1) (p₀ + n + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at h0
    exact h0
  obtain ⟨g, hg⟩ := H p₀ (p₀ + n) (z.v p₀ (p₀ + n) rfl) hf
  refine ⟨Cochain.single g (n - 1), ?_⟩
  intro p q hpq hp
  rw [Cochain.sub_v, δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
    Cochain.single_v_eq_zero g (n - 1) (p + 1) q (by omega) (by omega), comp_zero, smul_zero, add_zero]
  rcases hp.lt_or_eq with hlt | rfl
  · rw [hv p q hpq hlt, Cochain.single_v_eq_zero g (n - 1) p (q - 1) (by omega) (by omega), zero_comp,
      sub_zero]
  · subst hpq
    rw [Cochain.single_v, hg, sub_self]

end UpperTheory

theorem UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift :
    ∀ (K D : Cx ℤ) [K.IsStrictlyLE 0] (a : ℤ) [D.IsStrictlyGE a], (∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 → ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f) → ∀ n : ℤ, Subsingleton (CohomologyClass K D n) := by
  intro K D _ a _ H n
  have hz0 : ∀ (z : Cocycle K D n) (k : ℕ), ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q),
      -(k : ℤ) < p → ((z : Cochain K D n) - δ (n - 1) n γ).v p q hpq = 0 := by
    intro z k
    induction k with
    | zero =>
      refine ⟨0, fun p q hpq hp => ?_⟩
      exact (K.isZero_of_isStrictlyLE 0 p (by simpa using hp)).eq_of_src _ _
    | succ k ih =>
      obtain ⟨γ, hγ⟩ := ih
      obtain ⟨γ', hγ'⟩ := UpperTheory.hb_step K D H n (-(k : ℤ)) ((z : Cochain K D n) - δ (n - 1) n γ)
        (by rw [δ_sub, z.δ_eq_zero, δ_δ, sub_zero]) (fun p q hpq hp => hγ p q hpq hp)
      refine ⟨γ + γ', fun p q hpq hp => ?_⟩
      rw [δ_add, ← sub_sub]
      exact hγ' p q hpq (by push_cast at hp; omega)
  have all : ∀ z : Cocycle K D n, CohomologyClass.mk z = 0 := by
    intro z
    obtain ⟨γ, hγ⟩ := hz0 z (n - a + 1).toNat
    have hk := Int.self_le_toNat (n - a + 1)
    have hzero : (z : Cochain K D n) - δ (n - 1) n γ = 0 := by
      apply Cochain.ext
      intro p q hpq
      rw [Cochain.zero_v]
      by_cases hp : -((n - a + 1).toNat : ℤ) < p
      · exact hγ p q hpq hp
      · exact (D.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, γ, (sub_eq_zero.mp hzero).symm⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [all x, all y]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace UpperTheory.CoverSieveFree

private def coverSieve {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) (x : T ⟶ Y) : Sieve T where
  arrows V g := (∃ u : V ⟶ A, u ≫ a = g ≫ x) ∨ ∃ v : V ⟶ B, v ≫ b = g ≫ x
  downward_closed := by
    rintro V W g (⟨u, hu⟩ | ⟨v, hv⟩) h
    · exact Or.inl ⟨h ≫ u, by simp [hu]⟩
    · exact Or.inr ⟨h ≫ v, by simp [hv]⟩

private theorem coverSieve_mem {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a]
    [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) (x : T ⟶ Y) :
    coverSieve a b x ∈ Scheme.etaleTopology.{0} T := by
  let Xs : Bool → Scheme.{0} := fun i => Bool.casesOn i B A
  let fs : ∀ i, Xs i ⟶ Y := fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a
  have hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩
    · rcases hc y with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · cases i <;> dsimp [fs] <;> infer_instance
  have hS := Precoverage.generate_mem_toGrothendieck hmem
  refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)
  rintro V g ⟨W, h, k, hk, e⟩
  rcases hk with ⟨i⟩
  cases i
  · exact Or.inr ⟨h, e⟩
  · exact Or.inl ⟨h, e⟩

private theorem free_hom_ext (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b)
    {G : Shv R} (φ ψ : (free R).obj (yoneda.obj Y) ⟶ G)
    (ha : (free R).map (yoneda.map a) ≫ φ = (free R).map (yoneda.map a) ≫ ψ)
    (hb : (free R).map (yoneda.map b) ≫ φ = (free R).map (yoneda.map b) ≫ ψ) : φ = ψ := by
  apply free_ext
  intro U x
  refine G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_
  intro V g hg
  change Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)
  rw [map_res, map_res, freeGen_res]
  rcases hg with ⟨u, hu⟩ | ⟨v, hv⟩
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map a).app (op V))) u := hu.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _
    rw [ha]
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map b).app (op V))) v := hv.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _
    rw [hb]

end UpperTheory.CoverSieveFree

open UpperTheory.CoverSieveFree in
theorem UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective :
    ∀ (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y), IsOpenImmersion a → IsOpenImmersion b →
       (∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) → Cover2 R (sch.map a) (sch.map b) := by
  intro R _ Y A B a b ha hb hc
  have hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f) := by
    intro Z f _
    have h1 : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
      (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))
    have h2 : Mono (yoneda.map f) := NatTrans.mono_of_mono_app _
    have h3 : ∀ n, Mono ((sch.map f).app n) := fun n => h2
    exact NatTrans.mono_of_mono_app _
  refine ⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩
  apply free_hom_ext R a b hc φ ψ
  · have e := congrArg (fun k => biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at e
    exact e
  · have e := congrArg (fun k => biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at e
    exact e
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem unit_on_basicOpen (T : Scheme.{0}) (a : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (T.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (T.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((T.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem mem_basicOpen_or (T : Scheme.{0}) (a b : Γ(T, ⊤)) (h : Ideal.span {a, b} = ⊤) (u : T) :
    u ∈ T.basicOpen a ∨ u ∈ T.basicOpen b := by
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span {a, b} := h ▸ Submodule.mem_top
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp h1
  have hu : IsUnit (ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (x * a) +
      ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (y * b)) := by
    rw [← map_add (f := _), hxy, map_one]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hx | hy
  · left
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hx
    exact isUnit_of_mul_isUnit_right hx
  · right
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hy
    exact isUnit_of_mul_isUnit_right hy

theorem UpperTheory.locally_isUnit_or_isUnit_of_span_pair_eq_top :
    ∀ (T : Scheme.{0}) (a b : Γ(T, ⊤)), Ideal.span {a, b} = ⊤ → Loc T fun V g => IsUnit (g.appTop.hom a) ∨ IsUnit (g.appTop.hom b) := by
  intro T a b h
  let U : Bool → T.Opens := fun i => bif i then T.basicOpen a else T.basicOpen b
  have hU : TopologicalSpace.IsOpenCover U := by
    apply eq_top_iff.mpr
    intro u _
    rcases mem_basicOpen_or T a b h u with hu | hu
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hu⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hu⟩
  let C := T.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  cases i
  · right
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T b).map c.appTop.hom
  · left
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T a).map c.appTop.hom
end

section

open GlobalTheory GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace UpperTheory

end UpperTheory

theorem UpperTheory.finite_fiber_of_finiteType_parameter_ring :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
      (d : ℕ) (x : Fin (d + 1) → F), IsPd ℂ x → Algebra.FiniteType ℂ (rB ℂ K x {0}) →
      Finite (fib ℂ K x) := by
  intro F K _ _ _ _ _ _ d x hx hft
  classical
  have hmem : ∀ c : rA ℂ x {0}, algebraMap F K (c : F) ∈ rB ℂ K x {0} := by
    intro c
    show algebraMap F K (c : F) ∈ (integralClosure (rA ℂ x {0}) K).restrictScalars ℂ
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := c)
  let ι : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    ((IsScalarTower.toAlgHom ℂ F K).comp (rA ℂ x {0}).val).codRestrict _ hmem
  have key : ∀ e1 e2 : fib ℂ K x, ∀ c : rA ℂ x {0}, e1.1 (ι c) = e2.1 (ι c) := by
    intro e1 e2 c
    obtain ⟨c, hc⟩ := c
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi
      subst hi
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · have h3 : ∀ (e : fib ℂ K x) (h : x 0 / x 0 ∈ rA ℂ x {0}), e.1 (ι ⟨x 0 / x 0, h⟩) = 1 := by
          intro e h
          have h1 : (⟨x 0 / x 0, h⟩ : rA ℂ x {0}) = 1 := Subtype.ext (div_self (hx.ne 0))
          rw [h1, map_one, map_one]
        exact (h3 e1 _).trans (h3 e2 _).symm
      · exact (e1.2 j').trans (e2.2 j').symm
    | algebraMap r =>
      show e1.1 (ι (algebraMap ℂ (rA ℂ x {0}) r)) = e2.1 (ι (algebraMap ℂ (rA ℂ x {0}) r))
      simp only [AlgHom.commutes]
    | add y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩))
      simp only [map_add (f := _), ihy, ihz]
    | mul y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩))
      simp only [map_mul, ihy, ihz]
  rcases isEmpty_or_nonempty (fib ℂ K x) with hE | hE
  · infer_instance
  obtain ⟨e0⟩ := hE
  obtain ⟨s, hs⟩ := hft.out
  let ψ : rA ℂ x {0} →+* ℂ := (e0.1.comp ι).toRingHom
  have hint : ∀ b : rB ℂ K x {0}, IsIntegral (rA ℂ x {0}) (b : K) := fun b => b.2
  let R : rB ℂ K x {0} → Finset ℂ := fun b => (((hint b).choose).map ψ).roots.toFinset
  have hR : ∀ (e : fib ℂ K x) (b : rB ℂ K x {0}), e.1 b ∈ R b := by
    intro e b
    obtain ⟨hm, hp⟩ := (hint b).choose_spec
    have h0 : Polynomial.eval₂ (ι : rA ℂ x {0} →+* rB ℂ K x {0}) b (hint b).choose = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0})
        (rB ℂ K x {0}).val.toRingHom b
      refine this.trans ?_
      rw [Subalgebra.coe_zero]
      exact hp
    have h1 := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) e.1.toRingHom b
    rw [h0, map_zero] at h1
    have h2 : e.1.toRingHom.comp (ι : rA ℂ x {0} →+* rB ℂ K x {0}) = ψ :=
      RingHom.ext fun c => key e e0 c
    rw [h2] at h1
    have hne : ((hint b).choose.map ψ) ≠ 0 := (hm.map ψ).ne_zero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map]
    exact h1.symm
  let Φ : fib ℂ K x → ((t : s) → (R t : Set ℂ)) := fun e t => ⟨e.1 t, hR e t⟩
  apply Finite.of_injective Φ
  intro e1 e2 h
  apply Subtype.ext
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro t ht
  have := congrFun h ⟨t, ht⟩
  exact congrArg Subtype.val this
end
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem finite_bad_places (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] :
    {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}.Finite := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine (Set.Finite.biUnion s.finite_toSet (fun g _ =>
    Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_
  intro v hv
  by_contra hcon
  apply hv
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring := by
    intro g hg
    by_cases g0 : algebraMap B (FractionRing B) g = 0
    · rw [g0]; exact zero_mem _
    · have h0 : v.ord (algebraMap B (FractionRing B) g) = 0 := by
        by_contra hne
        exact hcon g hg hne
      exact (v.ord_nonneg_iff g0).1 h0.ge
  intro b
  have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hmem x hx
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
    exact v.algebraMap_mem r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem dvd_ord_of_mem_sel (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [IsFunctionField k (FractionRing B)] (q : ℕ) (v : Place k (FractionRing B))
    (hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring) (f : (FractionRing B)ˣ)
    (hf : f ∈ LateralTheory.E.LeafPicCut.sel B q) : (q : ℤ) ∣ v.ord (f : FractionRing B) := by
  have hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩
  obtain ⟨I, hI⟩ := hf
  have hvP := Place.ofHeightOneSpectrum_center B hk v hv
  have hval := Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)
  rw [hvP] at hval
  have h1 := v.valuation_eq_exp_neg_ord f.ne_zero
  rw [hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj] at h1
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) =
      ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q := by
    have := congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ =>
      (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI
    simpa using this.symm
  rw [hspan, FractionalIdeal.count_pow] at h1
  exact ⟨_, h1.symm⟩

theorem UpperTheory.finite_pic_torsion_of_finite_kummerSelmer :
    LateralTheory.E.LeafPicCut.LeafSelPic → ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] (q : ℕ) [NeZero q], FinCls q (SelAll k (FractionRing B) q) → Finite {c : CommRing.Pic B // c ^ q = 1} := by
  intro hS k B _ _ _ _ _ _ q _ hT
  have hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q) := by
    have : Finite {v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} := (finite_bad_places k B).to_subtype
    let φ : LateralTheory.E.LeafPicCut.sel B q →
        ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) :=
      fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)
    let r := Function.invFun φ
    have hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q,
        (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q := by
      intro f v
      have hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) =
          v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B) := by
        rw [Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]
      rw [hdiv]
      by_cases hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring
      · exact dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)
      · have h := congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨T, hT⟩ := hT
    choose t ht u hu using fun f => hT _ (hall f)
    refine Finite.of_injective (β := ({v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T)
      (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_
    intro x y hxy
    have h1 : φ x.out = φ y.out := congrArg Prod.fst hxy
    have h2 : t x.out = t y.out := congrArg (fun p => (p.2 : T).1) hxy
    have hx := hu x.out
    have hy := hu y.out
    rw [div_eq_iff_eq_mul'] at hx hy
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(u x.out)⁻¹ * u y.out, ?_⟩
    simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy, h1, h2, mul_pow, inv_pow]
    group
  have key : Finite {c : ClassGroup B // c ^ q = 1} := hS B q hfin
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))
end
