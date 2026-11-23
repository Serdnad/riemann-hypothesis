module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

section

open Module

namespace UpperTheory.V.Z.Sym.Tf

variable {Λ M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]

private theorem iter_lemma (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ) :
    ∀ (k : ℕ) (b : Λ), Θ ^ k * n b = n (σ^[k] b) * Θ ^ k := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, Function.iterate_succ_apply]

private theorem mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (h : ∀ a, Θ * n a = n (σ a) * Θ)
    (a : Λ) : ∀ k : ℕ, (n a * Θ) ^ k = ((List.range k).map (fun i => n (σ^[i] a))).prod * Θ ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_assoc, ← mul_assoc (Θ ^ k), iter_lemma n Θ σ h]
    simp [List.range_succ, pow_succ, mul_assoc]

private theorem list_prod_mem_ideal_pow_length {R : Type} [CommRing R] (I : Ideal R) :
    ∀ l : List R, (∀ x ∈ l, x ∈ I) → l.prod ∈ I ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact Ideal.mul_mem_mul (hl x (by simp)) (ih fun y hy => hl y (by simp [hy]))

private theorem exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent (n : Λ → End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b))
    (hn : ∀ a, IsNilpotent (n a)) (a : Λ) :
    ∃ m : ℕ, ((List.range m).map (fun i => n (σ^[i] a))).prod = 0 := by
  let A := Algebra.adjoin ℂ (Set.range n)
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact hc x y)
  letI : CommRing A := by
    open scoped IsMulCommutative in
    exact inferInstance
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_nilradical A
  let g : ℕ → A := fun i => ⟨n (σ^[i] a), Algebra.subset_adjoin ⟨σ^[i] a, rfl⟩⟩
  have hmem : ∀ i, g i ∈ nilradical A := by
    intro i
    obtain ⟨k, hk⟩ := hn (σ^[i] a)
    exact ⟨k, Subtype.ext (by simpa [g] using hk)⟩
  have hP := list_prod_mem_ideal_pow_length (nilradical A) ((List.range m).map g) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hmem i)
  simp only [List.length_map, List.length_range, hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hP
  refine ⟨m, ?_⟩
  have h2 := congrArg A.val hP
  rw [map_list_prod, map_zero, List.map_map] at h2
  exact h2

theorem trace_nil (n : Λ → End ℂ M) (Θ : End ℂ M) (σ : Λ → Λ) (hc : ∀ a b, Commute (n a) (n b)) (hn : ∀ a, IsNilpotent (n a))
    (h : ∀ a, Θ * n a = n (σ a) * Θ) (a : Λ) : LinearMap.trace ℂ M (n a * Θ) = 0 := by
  obtain ⟨m, hm⟩ := exists_prod_range_iterate_eq_zero_of_commute_of_isNilpotent n σ hc hn a
  have hnil : IsNilpotent (n a * Θ) := ⟨m, by rw [mul_pow_eq_prod_range_iterate_mul_pow_of_semiconj n Θ σ h a m, hm, zero_mul]⟩
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero

abbrev Vg (u : Λ → End ℂ M) (χ : Λ → ℂ) : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a)

theorem Vg_maps {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (a : Λ) (χ : Λ → ℂ) : Set.MapsTo (u a) (Vg u χ) (Vg u χ) := by
  intro v hv
  simp only [Vg, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
  intro b
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) (χ b) (hv b)

theorem Vg_indep {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : iSupIndep (Vg u) :=
  End.independent_iInf_maxGenEigenspace_of_forall_mapsTo u fun i j φ => End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ

theorem Vg_int [DecidableEq (Λ → ℂ)] {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) : DirectSum.IsInternal (Vg u) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (Vg_indep hc)
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute u
    (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (u i))

theorem trace_Vg {u : Λ → End ℂ M} (hc : ∀ a b, Commute (u a) (u b)) (χ : Λ → ℂ) (Θ : End ℂ M) (σ : Λ → Λ)
    (hΘ : Set.MapsTo Θ (Vg u χ) (Vg u χ)) (h : ∀ a, ∀ v ∈ Vg u χ, Θ (u a v) = u (σ a) (Θ v)) (hχ : ∀ a, χ (σ a) = χ a) (a : Λ)
    (h' : Set.MapsTo (u a * Θ) (Vg u χ) (Vg u χ)) :
    LinearMap.trace ℂ (Vg u χ) ((u a * Θ).restrict h') = LinearMap.trace ℂ (Vg u χ) (Θ.restrict hΘ) * χ a := by
  have key : ∀ (f : End ℂ M) (hf : Set.MapsTo f (Vg u χ) (Vg u χ)) (x : Vg u χ),
      ((f.restrict hf x : Vg u χ) : M) = f x := fun _ _ _ => rfl
  have hNm : ∀ b, Set.MapsTo (u b - algebraMap ℂ (End ℂ M) (χ b)) (Vg u χ) (Vg u χ) := by
    intro b v hv
    have h1 := Vg_maps hc b χ hv
    simp only [SetLike.mem_coe] at h1 hv ⊢
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ hv)
  let N : Λ → End ℂ (Vg u χ) := fun b => (u b - algebraMap ℂ (End ℂ M) (χ b)).restrict (hNm b)
  let T : End ℂ (Vg u χ) := Θ.restrict hΘ
  have hNc : ∀ b c, Commute (N b) (N c) := by
    intro b c
    show N b * N c = N c * N b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := LinearMap.congr_fun (hc b c).eq (w : M)
    simp only [Module.End.mul_apply] at e
    simp only [N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    module
  have hNn : ∀ b, IsNilpotent (N b) := by
    intro b
    exact Module.End.isNilpotent_restrict_of_le (q := (u b).maxGenEigenspace (χ b)) (iInf_le _ b)
      ((u b).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (χ b))
  have hTN : ∀ b, T * N b = N (σ b) * T := by
    intro b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have e := h b w w.2
    simp only [T, N, Module.End.mul_apply, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply, map_sub, map_smul, e]
    rw [hχ]
  have hsplit : (u a * Θ).restrict h' = N a * T + χ a • T := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [N, T, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, key, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    abel
  rw [hsplit, map_add (f := _), map_smul, trace_nil N T σ hNc hNn hTN a, zero_add, smul_eq_mul, mul_comm]

end UpperTheory.V.Z.Sym.Tf
end

section

noncomputable section

namespace UpperTheory.V.Z.Sym

open MulAction

def gq {H Y : Type} [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient H Y, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ)

def gqOn {H G : Type} [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) : ℂ :=
  letI : MulAction H (G ⧸ U) := MulAction.compHom _ j
  gq H₀ k

structure Base (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] where
  ι : Γ →* G
  U : Subgroup G
  ω : U →* ℂˣ
  W : Representation ℂ Γ V
  Γ₀ : Subgroup Γ
  cenΓ : Γ₀ ≤ Subgroup.center Γ
  cenG : ∀ z ∈ Γ₀, ι z ∈ Subgroup.center G
  memU : ∀ z ∈ Γ₀, ι z ∈ U
  scal : ∀ z (hz : z ∈ Γ₀) v, W z v = (ω ⟨ι z, memU z hz⟩ : ℂ) • v

namespace Base

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V)

def Forms : Submodule ℂ (G → V) where
  carrier := {φ | (∀ γ g, φ (B.ι γ * g) = B.W γ (φ g)) ∧ ∀ g (u : B.U), φ (g * u) = (B.ω u : ℂ) • φ g}
  add_mem' := fun {a b} ha hb => ⟨fun γ g => by simp [ha.1, hb.1], fun g u => by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun γ g => by simp, fun g u => by simp⟩
  smul_mem' := fun c a ha => ⟨fun γ g => by simp [ha.1], fun g u => by simp [ha.2, smul_comm c]⟩

structure Fin : Prop where
  cls : ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ B.U, g = B.ι γ * s * u
  stab : ∀ g : G, B.Γ₀.relIndex ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) ≠ 0

structure Tw where
  θΓ : Γ ≃* Γ
  θ : G ≃* G
  Θ : V →ₗ[ℂ] V
  comm : ∀ γ, θ (B.ι γ) = B.ι (θΓ γ)
  int : ∀ γ v, Θ (B.W γ v) = B.W (θΓ γ) (Θ v)
  fix : ∀ z ∈ B.Γ₀, θΓ z = z

def Tw.one : B.Tw := ⟨.refl _, .refl _, .id, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

variable {B}

def Tw.mul (s₁ s₂ : B.Tw) : B.Tw where
  θΓ := s₂.θΓ.trans s₁.θΓ
  θ := s₂.θ.trans s₁.θ
  Θ := s₁.Θ ∘ₗ s₂.Θ
  comm γ := by simp [s₂.comm, s₁.comm]
  int γ v := by simp [s₂.int, s₁.int]
  fix z hz := by simp [s₂.fix z hz, s₁.fix z hz]

namespace Tw

variable (s : B.Tw)

structure IsTest (f : G → ℂ) : Prop where
  left : ∀ (u : B.U) y, f (u * y) = ((B.ω u)⁻¹ : ℂˣ) * f y
  right : ∀ (u : B.U) y, f (y * s.θ u) = ((B.ω u)⁻¹ : ℂˣ) * f y
  fin : {x : G ⧸ B.U | f (s.θ x.out) ≠ 0}.Finite

def opF (f : G → ℂ) (φ : G → V) (g : G) : V := ∑ᶠ x : G ⧸ B.U, f (s.θ x.out) • s.Θ (φ (s.θ.symm g * x.out))


open scoped Classical in
open Classical in
def R (f : G → ℂ) : Module.End ℂ B.Forms :=
  if h : ∃ L : Module.End ℂ B.Forms, ∀ φ, (L φ).1 = s.opF f φ.1 then h.choose else 0

def conv (f₁ f₂ : G → ℂ) (y : G) : ℂ := ∑ᶠ x : G ⧸ B.U, f₁ (s.θ x.out) * f₂ (x.out⁻¹ * s.θ.symm y)

def Rel (δ δ' : Γ) : Prop := ∃ x : Γ, ∃ z ∈ B.Γ₀, δ' = x⁻¹ * δ * s.θΓ x * z

def Cent (δ : Γ) : Subgroup Γ where
  carrier := {x | ∃ z ∈ B.Γ₀, x⁻¹ * δ * s.θΓ x = δ * z}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨z, hz, h⟩ ⟨w, hw, h'⟩
    refine ⟨w * z, mul_mem hw hz, ?_⟩
    have hc := Subgroup.mem_center_iff.1 (B.cenΓ hz)
    calc (a * b)⁻¹ * δ * s.θΓ (a * b) = b⁻¹ * (a⁻¹ * δ * s.θΓ a) * s.θΓ b := by simp [mul_assoc]
      _ = (b⁻¹ * δ * s.θΓ b) * z := by rw [h, mul_assoc (b⁻¹ * δ) (s.θΓ b) z, hc (s.θΓ b)]; simp only [mul_assoc]
      _ = δ * (w * z) := by rw [h', mul_assoc]
  inv_mem' := by
    rintro a ⟨z, hz, h⟩
    refine ⟨z⁻¹, inv_mem hz, ?_⟩
    have hc := Subgroup.mem_center_iff.1 (B.cenΓ hz)
    have h1 : δ = a * (δ * z) * (s.θΓ a)⁻¹ := by rw [← h]; simp [mul_assoc]
    rw [eq_mul_inv_iff_mul_eq, inv_inv, map_inv, mul_assoc _ _ z, hc]
    conv_rhs => rw [h1]
    simp [mul_assoc]

def ker (f : G → ℂ) (δ : Γ) (y : G ⧸ B.U) : ℂ := f (y.out⁻¹ * B.ι δ * s.θ y.out)

def term (f : G → ℂ) (δ : Γ) : ℂ :=
  LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) *
    gqOn (B.ι.comp (s.Cent δ).subtype) (B.Γ₀.subgroupOf (s.Cent δ)) B.U (s.ker f δ)

end Tw

end Base

structure RPG {I : Type} (G : Type) [Group G] (Gv : I → Type) [∀ v, Group (Gv v)] (K : ∀ v, Subgroup (Gv v)) where
  p : ∀ v, G →* Gv v
  inj : ∀ g, (∀ v, p v g = 1) → g = 1
  ae : ∀ g, ∀ᶠ v in Filter.cofinite, p v g ∈ K v
  surj : ∀ x : ∀ v, Gv v, (∀ᶠ v in Filter.cofinite, x v ∈ K v) → ∃ g, ∀ v, p v g = x v

def RPG.box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) : Subgroup G := ⨅ v, (U v).comap (P.p v)

def FinOrb {T G : Type} [Group T] [Group G] (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : Prop :=
  ∃ S : Finset G, ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ s ∈ S, ∃ u ∈ U, y = ι t * s * u

def mass {H T : Type} [Group H] [Group T] (φ : H →* T) (H₀ : Subgroup H) (C : Subgroup T) : ℂ :=
  ((φ.range ⊔ C).index : ℂ) / (H₀.relIndex (C.comap φ) : ℂ)

def IsGenEig {Λ M : Type} [AddCommGroup M] [Module ℂ M] (u : Λ → Module.End ℂ M) (χ : Λ → ℂ) : Prop :=
  (⨅ a, (u a).maxGenEigenspace (χ a)) ≠ ⊥

end UpperTheory.V.Z.Sym
end
end
