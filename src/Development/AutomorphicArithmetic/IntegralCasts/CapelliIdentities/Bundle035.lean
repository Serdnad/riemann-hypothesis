module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

namespace UpperTheory.Reformulated.B.Gwb5

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem smooth_quot {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
    [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G U} (h : IsSmooth ρ)
    (T : Submodule ℂ U) (hst : ∀ g : G, T ≤ Submodule.comap (ρ g) T) :
    IsSmooth (ρ.quotient T hst) := by
  intro v
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective T v
  let H : Subgroup G :=
    { carrier := {g : G | ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
      one_mem' := by
        show ρ.quotient T hst 1 _ = _
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        have hb' : ρ.quotient T hst b (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := hb
        show ρ.quotient T hst (a * b) _ = _
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        show ρ.quotient T hst a⁻¹ _ = _
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine H.isOpen_of_mem_nhds (g := 1) ?_
  have h1 : {g : G | ρ g u = u} ∈ nhds (1 : G) :=
    (h u).mem_nhds (by
      show ρ 1 u = u
      rw [map_one]
      rfl)
  refine Filter.mem_of_superset h1 ?_
  intro g hg
  have hg' : ρ g u = u := hg
  show ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  have e : ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (ρ g u) := rfl
  rw [e, hg']

end UpperTheory.Reformulated.B.Gwb5
end

section

theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G _ _ _ V _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {g : G | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        change ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by simp }
  exact H.isOpen_of_mem_nhds (g := 1) h
end

section

noncomputable def UpperTheory.Reformulated.B.Gwa2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.Gwa2.twKer :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      Submodule.span k
        {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[k] V) (↑n : G) : V → V) v - (↑((ψ : ↥N → kˣ) n) : k) • v}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa2.TwJacquet :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Type :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      V ⧸ UpperTheory.Reformulated.B.Gwa2.twKer ρ N ψ

theorem UpperTheory.Reformulated.B.Gwa2.aux4 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (m : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m)) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs m
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
  have key : ρ (s m * (n : G) * (s m)⁻¹) (ρ (s m) v) = ρ (s m) (ρ (n : G) v) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
  rw [hθ, map_sub, map_smul, ← key]

theorem UpperTheory.Reformulated.B.Gwa2.aux5 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        Submodule.span ℂ
            {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
          Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs 1

theorem UpperTheory.Reformulated.B.Gwa2.aux6 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M)))
          (UpperTheory.Reformulated.B.Gwa2.aux5 ρ N θ s hs) =
        (1 : UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s 1) v) = Submodule.Quotient.mk v
  rw [map_one, map_one, Module.End.one_apply]

theorem UpperTheory.Reformulated.B.Gwa2.aux7 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (a b : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs (a * b)

theorem UpperTheory.Reformulated.B.Gwa2.aux8 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n)
      (a b : M),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b)))
          (UpperTheory.Reformulated.B.Gwa2.aux7 ρ N θ s hs a b) =
        (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) a))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs a) *
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) b))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs b) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
  rw [map_mul, map_mul, Module.End.mul_apply]

noncomputable def UpperTheory.Reformulated.B.Gwa2.twAct :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] →
          [inst_2 : _root_.Module ℂ V] →
            (ρ : Representation ℂ G V) →
              (N : Subgroup G) →
                (θ : ↥N →* ℂˣ) →
                  {M : Type} →
                    [inst_3 : Group M] →
                      (s : M →* G) →
                        (∀ (m : M) (n : ↥N),
                            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
                              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
                          Representation ℂ M (UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
        (θ : ↥N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
        (hs :
          ∀ (m : M) (n : ↥N),
            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) ↦
      {
        toFun := fun (m : M) ↦
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs m),
        map_one' := UpperTheory.Reformulated.B.Gwa2.aux6 ρ N θ s hs, map_mul' := UpperTheory.Reformulated.B.Gwa2.aux8 ρ N θ s hs :
        M →* UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ }

private theorem UpperTheory.Reformulated.B.Gwa2.isOpen_fixer {M W : Type} [Group M] [AddCommGroup W] [_root_.Module ℂ W]
    [TopologicalSpace M] [IsTopologicalGroup M] (τ : Representation ℂ M W) (x : W)
    (h : {m : M | τ m x = x} ∈ nhds (1 : M)) : IsOpen {m : M | τ m x = x} := by
  let H : Subgroup M :=
    { carrier := {m : M | τ m x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : τ a x = x) (hb : τ b x = x) ↦ show τ (a * b) x = x by
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} (ha : τ a x = x) ↦ show τ a⁻¹ x = x by
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact H.isOpen_of_mem_nhds h

theorem UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct :
    ∀ {G M V : Type} [inst : Group G] [inst_1 : Group M] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℂ V]
      [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace M] [IsTopologicalGroup M] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      Continuous (⇑s : M → G) → UpperTheory.Reformulated.B.Gwa2.IsSmooth ρ → UpperTheory.Reformulated.B.Gwa2.IsSmooth (UpperTheory.Reformulated.B.Gwa2.twAct ρ N θ s hs) := by
  intro G M V _ _ _ _ _ _ _ ρ N θ s hs hc hρ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine UpperTheory.Reformulated.B.Gwa2.isOpen_fixer _ _ ?_
  have hU : IsOpen {m : M | ρ (s m) v = v} := (hρ v).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun m (hm : ρ (s m) v = v) ↦ ?_
  change Submodule.Quotient.mk (ρ (s m) v) = Submodule.Quotient.mk v
  rw [hm]
end

section

theorem UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open.{u_1, u_2} :
    ∀ {G : Type u_1} {V : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
    {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} ∈ nhds (1 : G) →
      IsOpen {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {k : G | ρ k v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h1 }
  exact H.isOpen_of_mem_nhds h
end

section

theorem UpperTheory.Reformulated.B.Yhd2.main :
    ∀ {G M : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
      [inst_4 : AddCommGroup M] [inst_5 : _root_.Module ℂ M] (ρ : Representation ℂ G M) (x : M),
      IsOpen {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x} →
        (Set.range fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x).Countable := by
  intro G M _ _ _ _ _ _ ρ x hS
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  apply (hDc.image (fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x)).mono
  rintro _ ⟨g, rfl⟩
  have hU : IsOpen ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}) :=
    hS.preimage (continuous_const.mul continuous_id)
  have hne : ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}).Nonempty :=
    ⟨g, by simp⟩
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU hne
  refine ⟨d, hdD, ?_⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hdU
  have : d = g * (g⁻¹ * d) := by group
  simp only
  rw [this, map_mul, Module.End.mul_apply, hdU]
end

section

theorem UpperTheory.Reformulated.B.Yhd4.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousMul G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v hS
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  have hc : Filter.Tendsto (fun h : G => g⁻¹ * h) (nhds g) (nhds 1) := by
    have := ((continuous_const_mul g⁻¹ : Continuous (fun h : G => g⁻¹ * h)).tendsto g)
    simpa using this
  filter_upwards [hc hS] with h hh
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hh ⊢
  have : h = g * (g⁻¹ * h) := by group
  rw [this, map_mul, Module.End.mul_apply, hh, hg]
end

section

noncomputable def UpperTheory.Reformulated.B.DYka2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.DYka2.main :
    ∀ {Γ V W : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : _root_.Module ℂ W] {ρ : Representation ℂ Γ V}
      {σ : Representation ℂ Γ W},
      UpperTheory.Reformulated.B.DYka2.IsSmooth ρ →
        ∀ (f : ρ.IntertwiningMap σ) {L : Subgroup Γ},
          IsCompact (↑L : Set Γ) →
            ∀ (χ : Γ → ℂ) (u : V),
              (f : V → W) u ≠ (0 : W) →
                (∀ g ∈ L, ((σ : Γ → W →ₗ[ℂ] W) g : W → W) ((f : V → W) u) = χ g • (f : V → W) u) →
                  ∃ (v : V), v ≠ (0 : V) ∧ ∀ g ∈ L, ((ρ : Γ → V →ₗ[ℂ] V) g : V → V) v = χ g • v := by
  intro Γ V W _ _ _ _ _ _ _ ρ σ hρ f L hL χ u hu hχ
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hint : ∀ (g : Γ) (v : V), f (ρ g v) = σ g (f v) := fun g v => Representation.IntertwiningMap.isIntertwining ρ σ f g v
  have hmul : ∀ g ∈ L, ∀ h ∈ L, χ (g * h) = χ g * χ h := by
    intro g hg h hh
    have key : χ (g * h) • f u = (χ g * χ h) • f u := by
      rw [← hχ (g * h) (L.mul_mem hg hh), map_mul, Module.End.mul_apply, hχ h hh, map_smul,
        hχ g hg, smul_smul, mul_comm]
    exact smul_left_injective ℂ hu key
  have h1 : χ 1 = 1 := by
    have key : χ 1 • f u = (1 : ℂ) • f u := by
      rw [← hχ 1 L.one_mem, map_one, one_smul]; rfl
    exact smul_left_injective ℂ hu key
  have hne : ∀ g ∈ L, χ g ≠ 0 := by
    intro g hg h0
    have := hmul g hg g⁻¹ (L.inv_mem hg)
    rw [mul_inv_cancel, h1, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup L :=
    { carrier := {g | ρ (g : Γ) u = u}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : ρ ((a : Γ)⁻¹) (ρ (a : Γ) u) = u := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha] at this
        simpa using this }
  have hHopen : IsOpen (H : Set L) := (hρ u).preimage continuous_subtype_val
  haveI : Finite (L ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI : Fintype (L ⧸ H) := Fintype.ofFinite _
  have hχH : ∀ h : L, h ∈ H → χ (h : Γ) = 1 := by
    intro h hh
    have e : ρ (h : Γ) u = u := hh
    have key : χ (h : Γ) • f u = (1 : ℂ) • f u := by
      rw [← hχ h h.2, ← hint, e, one_smul]
    exact smul_left_injective ℂ hu key
  let φ : L → V := fun g => (χ (g : Γ))⁻¹ • ρ (g : Γ) u
  have hφ : ∀ a b : L, QuotientGroup.leftRel H a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hb : (b : Γ) = a * ((a⁻¹ * b : L) : Γ) := by simp
    have e : ρ ((a⁻¹ * b : L) : Γ) u = u := hab
    have c := hχH _ hab
    simp only [φ]
    rw [hb, hmul _ a.2 _ (a⁻¹ * b).2, c, mul_one, map_mul, Module.End.mul_apply, e]
  let ψ : L ⧸ H → V := Quotient.lift φ hφ
  have hψ : ∀ g : L, ψ (g : L ⧸ H) = φ g := fun g => rfl
  have hfψ : ∀ q : L ⧸ H, f (ψ q) = f u := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [hψ]
      simp only [φ]
      rw [map_smul, hint, hχ g g.2, smul_smul, inv_mul_cancel₀ (hne g g.2), one_smul]
  have hact : ∀ (l : L) (q : L ⧸ H), ρ (l : Γ) (ψ q) = χ (l : Γ) • ψ (l • q) := by
    intro l q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have : l • (g : L ⧸ H) = ((l * g : L) : L ⧸ H) := rfl
      rw [this, hψ, hψ]
      simp only [φ]
      rw [map_smul, Subgroup.coe_mul, hmul _ l.2 _ g.2, map_mul, Module.End.mul_apply, smul_smul,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (hne l l.2), one_mul]
  refine ⟨∑ q : L ⧸ H, ψ q, ?_, ?_⟩
  · intro h0
    have e : f (∑ q : L ⧸ H, ψ q) = (Fintype.card (L ⧸ H) : ℂ) • f u := by

      rw [map_sum]
      simp only [hfψ]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [h0, map_zero] at e
    have hc : (Fintype.card (L ⧸ H) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (smul_ne_zero hc hu) e.symm
  · intro g hg

    rw [map_sum, Finset.smul_sum]
    simp only [hact ⟨g, hg⟩]
    exact (Equiv.sum_comp (MulAction.toPerm (⟨g, hg⟩ : L)) (fun q => χ g • ψ q))
end

section

theorem UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by
  intro τ φ n hφ c w
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end
