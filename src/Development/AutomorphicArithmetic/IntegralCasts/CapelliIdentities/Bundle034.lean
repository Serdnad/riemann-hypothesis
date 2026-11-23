module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.RepresentationTheory.Irreducible
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
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

section

theorem UpperTheory.Reformulated.B.R4.lift_eigen :
    ∀ {T V : Type} [inst : CommGroup T]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V},
    (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) v = (↑((ψ : T → ℂˣ) t) : ℂ) • v) →
      μ ≠ ψ →
        y ∉ ℂ ∙ v →
          (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) y - (↑((μ : T → ℂˣ) t) : ℂ) • y ∈ ℂ ∙ v) →
            v ≠ (0 : V) →
              ∃ (z : V), z ≠ (0 : V) ∧ ∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) z = (↑((μ : T → ℂˣ) t) : ℂ) • z := by
  intro T V _ _ _ ρ ψ μ v y hv hne hy hmod _
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ ψ s := DFunLike.ne_iff.mp hne
  have hs' : ((μ s : ℂˣ) : ℂ) - ((ψ s : ℂˣ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hs (Units.ext h)
  refine ⟨ρ s y - ((ψ s : ℂˣ) : ℂ) • y, ?_, ?_⟩
  · intro h0
    apply hy
    have h1 := hmod s
    rw [sub_eq_zero.mp h0, ← sub_smul, ← neg_sub, neg_smul, neg_mem_iff] at h1
    exact (Submodule.smul_mem_iff _ hs').mp h1
  · intro t
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod t)
    have hty : ρ t y = ((μ t : ℂˣ) : ℂ) • y + b • v := by
      rw [hb]; abel
    have hcomm : ρ t (ρ s y) = ρ s (ρ t y) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_smul, hcomm, hty, map_add (f := _), map_smul, map_smul, hv s]
    module
end

section

noncomputable def UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

private noncomputable def flipConj {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (by intro v₁ v₂ w; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
    (by intro v w₁ w₂; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])

private theorem flipConj_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V) :
    flipConj B v w = starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

open UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers in
theorem UpperTheory.Reformulated.B.SesquilinearFlipConj.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ hS
  obtain ⟨B, hB0, hBinv⟩ := hS
  classical
  by_cases hH : B + flipConj B = 0
  · have hrel : ∀ v w, B v w + starRingEnd ℂ (B w v) = 0 := by
      intro v w
      have := congrArg (fun F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ => F v w) hH
      simpa [flipConj_apply] using this
    refine ⟨Complex.I • B, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      have : (-Complex.I) • (Complex.I • B) = B := by
        rw [smul_smul]; simp
      rw [← this, h, smul_zero]
    · intro v w
      have h1 := hrel v w
      have h2 : starRingEnd ℂ (B v w) = - B w v := by
        have := congrArg (starRingEnd ℂ) h1
        simp at this
        linear_combination this
      simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, h2]
      ring
    · intro g v w
      simp only [LinearMap.smul_apply, smul_eq_mul, hBinv]
  · refine ⟨B + flipConj B, hH, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, flipConj_apply, map_add (f := _), Complex.conj_conj]
      ring
    · intro g v w
      simp only [LinearMap.add_apply, flipConj_apply, hBinv]
end

section

noncomputable def UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] →
        {V : Type u_2} → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G} _ {_V} _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by rw [inv_mul_cancel, map_one]; rfl }
end

section

namespace UpperTheory.Reformulated.B.TwistedKernelFixed

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem aux2 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) {a b : V}
    (ha : a ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v})
    (hb : b ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (a + b) = (χ h : k) • (a + b) := by
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem aux3 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (h : H) :
    ρ h (0 : V) = (χ h : k) • (0 : V) := by
  rw [map_zero, smul_zero]

theorem aux4 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (c : k) {v : V}
    (hv : v ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (c • v) = (χ h : k) • c • v := by
  rw [map_smul, hv h, smul_comm]

noncomputable def eig {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v : V | ∀ h : H, ρ h v = (χ h : k) • v}
  add_mem' := @aux2 k G V _ _ _ _ ρ H χ
  zero_mem' := aux3 ρ H χ
  smul_mem' := aux4 ρ H χ

noncomputable def fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Submodule k V :=
  eig ρ H 1

noncomputable def twKer {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w : V | ∃ (n : N) (v : V), w = ρ n v - (ψ n : k) • v}

private theorem sum_shift {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →* (V →ₗ[ℂ] V)) (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)] (u : V)
    (hu : ∀ k ∈ K, ρ k u = u) (n : H) :
    ∑ q : H ⧸ K, ρ q.out (ρ n u) = ∑ q : H ⧸ K, ρ q.out u := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ K)) _ _ fun q => ?_
  have h1 : ((q.out * n : H) : H ⧸ K) = (((q * (n : H ⧸ K)).out : H) : H ⧸ K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have h2 := hu _ (QuotientGroup.eq.mp h1)
  have h3 : (q * (n : H ⧸ K)).out = q.out * n * ((q.out * n)⁻¹ * (q * (n : H ⧸ K)).out) := by
    rw [mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, h3, map_mul, Module.End.mul_apply, h2, map_mul, Module.End.mul_apply]

theorem eq_zero_of_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} [TopologicalSpace G] [IsTopologicalGroup G] (hs : IsSmooth π)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : v ∈ fixed π H)
    (hw : v ∈ twKer π H (1 : H →* ℂˣ)) : v = 0 := by
  classical
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have key : ∀ w ∈ twKer π H (1 : H →* ℂˣ),
      ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ (L : Subgroup H) [L.Normal] [Fintype (H ⧸ L)], L ≤ K →
        ∑ q : H ⧸ L, π (q.out : H) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, u, rfl⟩ := hx
      let K : Subgroup H :=
        { carrier := {h | π (h : G) u = u}
          mul_mem' := fun {a b} ha hb => by
            have ha' : π (a : G) u = u := ha
            have hb' : π (b : G) u = u := hb
            show π ((a : G) * b) u = u
            rw [map_mul, Module.End.mul_apply, hb', ha']
          one_mem' := by
            show π (1 : G) u = u
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {a} ha => by
            have ha' : π (a : G) u = u := ha
            show π ((a : G)⁻¹) u = u
            conv_lhs => rw [← ha']
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hK : IsOpen (K : Set H) := (hs u).preimage continuous_subtype_val
      have := Subgroup.quotient_finite_of_isOpen K hK
      refine ⟨K, Subgroup.finiteIndex_of_finite_quotient, fun L _ _ hL => ?_⟩
      have := sum_shift (π.comp H.subtype) L u (fun k hk => hL hk) n
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    | zero => exact ⟨⊤, inferInstance, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, h₁, hx⟩ := hx
      obtain ⟨K₂, h₂, hy⟩ := hy
      refine ⟨K₁ ⊓ K₂, inferInstance, fun L _ _ hL => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [hx L (hL.trans inf_le_left), hy L (hL.trans inf_le_right), add_zero]
    | smul c x _ hx =>
      obtain ⟨K, h, hx⟩ := hx
      refine ⟨K, h, fun L _ _ hL => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, hx L hL, smul_zero]
  obtain ⟨K, hK, h⟩ := key v hw
  have : Fintype (H ⧸ K.normalCore) := Fintype.ofFinite _
  have h0 := h K.normalCore K.normalCore_le
  have hv' : ∀ g : H, π (g : G) v = v := fun g => by
    have := hv g
    simpa using this
  simp only [hv', Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end UpperTheory.Reformulated.B.TwistedKernelFixed
end

section

theorem UpperTheory.isOpen_stabilizer_add_smul :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (a b : V) (z : ℂ),
        IsOpen {g : G | ρ g a = a} → IsOpen {g : G | ρ g b = b} → IsOpen {g : G | ρ g (a + z • b) = a + z • b} := by
  intro G V _ _ _ _ _ ρ a b z ha hb
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ρ g (a + z • b) = a + z • b := hg
  have hc : Continuous fun x : G => g⁻¹ * x := continuous_const.mul continuous_id
  have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b})) :=
    (ha.inter hb).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · simp
  · intro x hx
    have h1 : ρ (g⁻¹ * x) a = a := hx.1
    have h2 : ρ (g⁻¹ * x) b = b := hx.2
    have h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b := by
      rw [map_add (f := _), map_smul, h1, h2]
    have h4 : x = g * (g⁻¹ * x) := by group
    show ρ x (a + z • b) = a + z • b
    rw [h4, map_mul, Module.End.mul_apply, h3, hg']
end

section

noncomputable def UpperTheory.Reformulated.B.Gwa5.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.Gwa5.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), smul_add, ha h, hb h]

theorem UpperTheory.Reformulated.B.Gwa5.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.Gwa5.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.Gwa5.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.Gwa5.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.Gwa5.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.Gwa5.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.Gwa5.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.Gwa5.eig ρ H (1 : ↥H →* kˣ)

theorem UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (J L A : Subgroup G),
      IsOpen (↑J : Set G) →
        IsCompact (↑J : Set G) →
          ∀ (π : Representation ℂ G V),
            UpperTheory.Reformulated.B.Gwa5.IsSmooth π →
              ∀ (q : Submodule ℂ V) (u : V),
                L ≤ J →
                  (∀ y ∈ L, ((π : G → V →ₗ[ℂ] V) y : V → V) u = u) →
                    A ≤ J →
                      (∀ x ∈ A, ((π : G → V →ₗ[ℂ] V) x : V → V) u - u ∈ q) →
                        (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) → ∃ v ∈ UpperTheory.Reformulated.B.Gwa5.fixed π J, v - u ∈ q := by
  intro G V _ _ _ _ _ J L A _ hJc π hπ q u _ hL hAJ hA hdec
  classical
  have hmul : ∀ (x y : G) (w : V), π x (π y w) = π (x * y) w := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]

  have hq : ∀ y ∈ J, π y u - u ∈ q := by
    intro y hy
    obtain ⟨a, ha, hl⟩ := hdec y hy
    have h1 : π y u = π a u := by
      conv_rhs => rw [← hL _ hl, hmul, mul_inv_cancel_left]
    rw [h1]
    exact hA a ha

  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    have hU : ∀ x ∈ (J : Set G), {g : G | π g u = π x u} ∈ nhds x := by
      intro x _
      have ho : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g u = u}) :=
        (hπ u).preimage (continuous_const.mul continuous_id)
      refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
      · simp
      · intro g hg
        have hg' : π (x⁻¹ * g) u = u := hg
        show π g u = π x u
        conv_rhs => rw [← hg', hmul, mul_inv_cancel_left]
    obtain ⟨t, -, ht⟩ := hJc.elim_nhds_subcover _ hU
    refine (t.finite_toSet.image (fun g : G => π g u)).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨x, hx, hgx.symm⟩
  set O : Finset V := hfin.toFinset with hO
  have hmem : ∀ w, w ∈ O ↔ ∃ g ∈ J, π g u = w := by
    intro w
    rw [hO, Set.Finite.mem_toFinset]
    rfl
  have hstab : ∀ h ∈ J, ∀ w ∈ O, π h w ∈ O := by
    intro h hh w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * g, J.mul_mem hh hg, (hmul h g u).symm⟩
  have hne : (O.card : ℂ) ≠ 0 := by
    have : O.Nonempty := ⟨π 1 u, (hmem _).2 ⟨1, J.one_mem, rfl⟩⟩
    exact_mod_cast this.card_pos.ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ w ∈ O, w, ?_, ?_⟩
  · intro h
    have hs : ∑ w ∈ O, π (h : G) w = ∑ w ∈ O, w := by
      refine Finset.sum_nbij' (fun w => π (h : G) w) (fun w => π (h : G)⁻¹ w)
        (fun w hw => hstab _ h.2 w hw) (fun w hw => hstab _ (J.inv_mem h.2) w hw) ?_ ?_
        (fun _ _ => rfl)
      · intro w _
        simp only [hmul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro w _
        simp only [hmul, mul_inv_cancel, map_one, Module.End.one_apply]

    rw [map_smul, map_sum, hs, MonoidHom.one_apply, Units.val_one, one_smul]
  · have h2 : (O.card : ℂ)⁻¹ • ∑ w ∈ O, w - u = (O.card : ℂ)⁻¹ • ∑ w ∈ O, (w - u) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2]
    refine q.smul_mem _ (q.sum_mem ?_)
    intro w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact hq g hg
end

section

theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by
  intro V _ _ G _ _ _ ρ K hK w hw
  have hloc : IsLocallyConstant (fun g : G => ρ g w) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun g : G => k⁻¹ * g) ⁻¹' {g : G | ρ g w = w},
      hw.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hg' : ρ (k⁻¹ * g) w = w := hg
    calc ρ g w = ρ (k * (k⁻¹ * g)) w := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hg']
  haveI : CompactSpace (K : Set G) := isCompact_iff_compactSpace.mp hK
  have hfin := (hloc.comp_continuous
    (continuous_subtype_val (p := fun g : G => g ∈ (K : Set G)))).range_finite
  refine hfin.subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩
end

section

theorem UpperTheory.Reformulated.B.Qe20.irrCases :
    ∀ {G V : Type} [inst : Group G]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V),
    ρ.IsIrreducible →
      ∀ (W : Submodule ℂ V), (∀ (g : G), ∀ v ∈ W, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G V _ _ _ ρ hρ W hW
  let S : Subrepresentation ρ := ⟨W, fun g v hv => hW g v hv⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
end
