module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.GoingUp
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Fintype.Fin

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
end

section

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.AdmissibleSchurLemma.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsSmooth ρ ∧
        ∀ (K : Subgroup G), IsOpen (↑K : Set G) → IsCompact (↑K : Set G) → FiniteDimensional k ↥(UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ K)

private theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [_root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ H ↔ ∀ g ∈ H, ρ g v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* kˣ) h : kˣ) : k) • v) ↔ _
  simp

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (N : Type) [inst_3 : AddCommGroup N] [inst_4 : _root_.Module ℂ N] (π : Representation ℂ G N),
            π.IsIrreducible →
              UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible π →
                ∀ (φ : N →ₗ[ℂ] N),
                  (∀ (g : G) (x : N),
                      (φ : N → N) (((π : G → N →ₗ[ℂ] N) g : N → N) x) = ((π : G → N →ₗ[ℂ] N) g : N → N) ((φ : N → N) x)) →
                    ∃ (c : ℂ), φ = c • LinearMap.id := by
  intro G _ _ _ K hKo hKc N _ _ π hirr hadm φ hφ
  obtain ⟨hsm, hfd⟩ := hadm
  rcases subsingleton_or_nontrivial N with hN | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  let S : Subgroup G :=
    { carrier := {g | π g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        change π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : π a v = v := ha
        change π a⁻¹ v = v
        calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hsm v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hfin : FiniteDimensional ℂ (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    hfd (K ⊓ S) (hKo.inter hSo) (hKc.inter_right hSc)
  have hvU : v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) :=
    (UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff π _ v).2 fun g hg => hg.2
  have hnt : Nontrivial (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvU⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S), φ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) := by
    intro x hx
    rw [UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff] at hx ⊢
    intro g hg
    rw [← hφ, hx g hg]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let E : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top E with hE | hE
  · have h1 : Module.End.eigenspace φ c = ⊥ := congrArg Subrepresentation.toSubmodule hE
    have h2 : (w : N) ∈ Module.End.eigenspace φ c := Module.End.mem_eigenspace_iff.2 hwc
    rw [h1] at h2
    exact absurd ((Submodule.mem_bot ℂ).1 h2) hw0
  · have h1 : Module.End.eigenspace φ c = ⊤ := congrArg Subrepresentation.toSubmodule hE
    ext x
    have h2 : x ∈ Module.End.eigenspace φ c := h1 ▸ Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.1 h2
end

section

theorem UpperTheory.Reformulated.B.DYhc4.main :
    ∀ {K A : Type} [inst : Field K] [inst_1 : CommRing A] [inst_2 : Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ)
      (p : Ideal A) [hp : p.IsPrime] {b : A},
      b ∉ p →
        ∃ (ψ : A →+* ℂ), ψ.comp (Algebra.algebraMap K A) = σ ∧ (∀ a ∈ p, (ψ : A → ℂ) a = (0 : ℂ)) ∧ (ψ : A → ℂ) b ≠ (0 : ℂ) := by
  intro K A _ _ _ _ σ p hp b hb
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hj : p.jacobson = p := IsJacobsonRing.out' p hp.isRadical
  have hex : ∃ m : Ideal A, p ≤ m ∧ m.IsMaximal ∧ b ∉ m := by
    by_contra h
    push_neg at h
    apply hb
    rw [← hj]
    refine Ideal.mem_sInf.2 ?_
    rintro J ⟨hpJ, hJ⟩
    exact h J hpJ hJ
  obtain ⟨m, hpm, hm, hbm⟩ := hex
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let f : (A ⧸ m) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f : (A ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m), ?_, ?_, ?_⟩
  · ext x
    have h1 : Ideal.Quotient.mk m (algebraMap K A x) = algebraMap K (A ⧸ m) x := rfl
    have h2 : f (algebraMap K (A ⧸ m) x) = algebraMap K ℂ x := f.commutes x
    exact h2
  · intro a ha
    have : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)
    simp [this]
  · intro h0
    have h1 : f (Ideal.Quotient.mk m b) = 0 := h0
    have h2 : Ideal.Quotient.mk m b = 0 := by
      simpa using (map_eq_zero f).1 h1
    exact hbm (Ideal.Quotient.eq_zero_iff_mem.1 h2)
end

section

theorem UpperTheory.Reformulated.B.Qi28.exists_extend.{u_1, u_2} :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ),
    RingHom.ker (Algebra.algebraMap R A) ≤ RingHom.ker ev → ∃ (χ : A →+* ℂ), χ.comp (Algebra.algebraMap R A) = ev := by
  intro R A _ _ _ _ ev h
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) (RingHom.ker ev) ⊥
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact h)
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker ev) ℂ := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker ev) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) (A ⧸ Q) := inferInstance
  haveI : IsDomain (R ⧸ RingHom.ker ev) := Ideal.Quotient.isDomain _
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) ℂ :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  let φ : (A ⧸ Q) →ₐ[R ⧸ RingHom.ker ev] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(φ : (A ⧸ Q) →+* ℂ).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  exact φ.commutes (Ideal.Quotient.mk (RingHom.ker ev) r)
end

section

theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end

section

namespace UpperTheory.Reformulated.B.Qk43

private lemma esymm_zero_deg (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

private lemma esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

open Polynomial in
private lemma coeff_prod_one_add (s : Multiset ℂ) (k : ℕ) :
    (s.map fun r => (1 + C r * X : ℂ[X])).prod.coeff k = s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => cases k <;> simp [Multiset.esymm, coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add,
      coeff_C_mul]
    cases k with
    | zero => rw [coeff_X_mul_zero, ih, esymm_zero_deg, esymm_zero_deg, mul_zero, add_zero]
    | succ k => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (j : ℕ) :
    (s + t).esymm j = ∑ a ∈ Finset.range (j + 1), s.esymm a * t.esymm (j - a) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

end UpperTheory.Reformulated.B.Qk43
end

section

theorem UpperTheory.Reformulated.B.Qi19.tube.{u_1, u_2} :
    ∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousInv G]
    [inst_3 : TopologicalSpace X] (T : G → X → X),
    (Continuous fun (p : G × X) ↦ T p.1 p.2) →
      (∀ (w : X), T (1 : G) w = w) →
        (∀ (k : G) (w : X), T k⁻¹ (T k w) = w) →
          ∀ {g : X → ℂ},
            IsLocallyConstant g → HasCompactSupport g → ∀ᶠ (k : G) in nhds (1 : G), ∀ (w : X), g (T k w) = g w := by
  intro G X _ _ _ _ T hT h1 hinv g hg hc
  have hK : ∀ᶠ k : G in nhds (1 : G), ∀ w ∈ tsupport g, g (T k w) = g w := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun (k : G) (w : X) => g (T k w) = g w) hc.isCompact ?_
    intro y _
    have ha := (hg.comp_continuous hT).eventually_eq ((1 : G), y)
    have hb := (hg.comp_continuous (continuous_snd : Continuous fun p : G × X => p.2)).eventually_eq
      ((1 : G), y)
    filter_upwards [ha, hb] with z hza hzb
    simp only [Function.comp_apply, h1] at hza hzb
    rw [hza, hzb]
  have hi : Filter.Tendsto (fun k : G => k⁻¹) (nhds 1) (nhds 1) := by
    simpa using (continuous_inv (G := G)).tendsto 1
  filter_upwards [hK, hi.eventually hK] with k hk hk' w
  by_cases hw : w ∈ tsupport g
  · exact hk w hw
  · by_cases hw' : T k w ∈ tsupport g
    · have h := hk' _ hw'
      rw [hinv] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hw, image_eq_zero_of_notMem_tsupport hw']
end

section

theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
end

section

open CategoryTheory

theorem UpperTheory.Reformulated.B.DYra4.main.{u} :
    ∀ (S : ℕ → Type u) [∀ (a : ℕ), Finite (S a)] [∀ (a : ℕ), Nonempty (S a)] (t : (a : ℕ) → S (a + (1 : ℕ)) → S a),
      ∃ (s : (a : ℕ) → S a), ∀ (a : ℕ), t a (s (a + (1 : ℕ))) = s a := by
  intro S _ _ t
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (X := S) (fun n => TypeCat.ofHom (t n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (S j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (S j.unop))
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun a => x (Opposite.op a), fun a => ?_⟩
  have h := hx (homOfLE (Nat.le_succ a)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
end

section

theorem UpperTheory.Reformulated.B.Re1.lower_iff :
    ∀ {n : ℕ} (P : Fin n → Prop) [inst : DecidablePred P],
    (∀ (a b : Fin n), a ≤ b → P b → P a) → ∀ (b : Fin n), P b ↔ (↑b : ℕ) < (Finset.filter P Finset.univ).card := by
  intro n P _ h b
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp P (fun i j hij => h j i hij)).symm
end
