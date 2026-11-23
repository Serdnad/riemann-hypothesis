module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle038
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle036
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

theorem exists_extend_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u : G → E, ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := by
  classical
  let r : G → G := fun x => (Quotient.mk (QuotientGroup.rightRel Γ) x).out
  have hr : ∀ x, x * (r x)⁻¹ ∈ Γ := fun x =>
    QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq
      (Quotient.mk (QuotientGroup.rightRel Γ) x)))
  have hrγ : ∀ (γ : Γ) (x : G), r (γ * x) = r x := fun γ x => by
    have : Quotient.mk (QuotientGroup.rightRel Γ) ((γ : G) * x)
        = Quotient.mk (QuotientGroup.rightRel Γ) x := by
      apply Eq.symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.2
      simp
    simp only [r, this]
  refine ⟨fun x => ρ (r x) (z ⟨x * (r x)⁻¹, hr x⟩), fun γ x => ?_⟩
  have h1 : (⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩ : Γ) = γ * ⟨x * (r x)⁻¹, hr x⟩ := by
    apply Subtype.ext
    simp [hrγ, mul_assoc]
  show ρ (r (γ * x)) (z ⟨(γ : G) * x * (r (γ * x))⁻¹, hr _⟩) = _
  rw [h1, hz, hrγ, map_add (f := _), ← hmul]
  simp

theorem exists_extn_of_cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (z : Γ → E) (hz : z ∈ cocyc Γ ρ) :
    ∃ u ∈ extn Γ ρ s, ∀ γ : Γ, u γ - u 1 = z γ := by
  obtain ⟨u0, hu0⟩ := exists_extend_cocyc Γ ρ hmul z hz
  let u : G → E := fun x => (1 / 4 : ℂ) •
    (u0 x + ρ (s ^ 3) (u0 (x * s)) + ρ (s ^ 2) (u0 (x * s ^ 2)) + ρ s (u0 (x * s ^ 3)))
  have e1 : s * s ^ 3 = 1 := by rw [← hs]; group
  have e2 : s ^ 2 * s ^ 2 = 1 := by rw [← hs]; group
  have e3 : s ^ 3 * s = 1 := by rw [← hs]; group
  have key : ∀ (γ : Γ) (x : G), u (γ * x) = ρ x (z γ) + u x := fun γ x => by
    simp only [u, mul_assoc, hu0, map_add (f := _), ← hmul, e1, e2, e3, mul_one]
    module
  have key1 : ∀ γ : Γ, u γ - u 1 = z γ := fun γ => by
    have := key γ 1
    rw [mul_one, hone] at this
    rw [this]; abel
  refine ⟨u, ⟨fun γ hγ x => ?_, fun x => ?_⟩, key1⟩
  · have h1 := key ⟨γ, hγ⟩ x
    have h2 := key1 ⟨γ, hγ⟩
    simp only at h1 h2
    rw [h1, h2]; abel
  · have f1 : s * s = s ^ 2 := (pow_two s).symm
    have f2 : s * s ^ 2 = s ^ 3 := by group
    have f3 : s ^ 2 * s = s ^ 3 := by group
    simp only [u, mul_assoc, map_add (f := _), map_smul, ← hmul, e1, e3, f1, f2, f3, mul_one, hone]
    module

def extnToCocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : extn Γ ρ s →ₗ[ℂ] cocyc Γ ρ where
  toFun u := ⟨fun γ => u.1 γ - u.1 1, fun γ δ => by
    have := u.2.1 γ γ.2 δ
    simp only [Subgroup.coe_mul]
    rw [← this]; abel⟩
  map_add' u v := by
    apply Subtype.ext; funext γ
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' c u := by
    apply Subtype.ext; funext γ
    simp [smul_sub]

theorem twInv_le_extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) :
    twInv Γ s (ρ s) ≤ extn Γ ρ s := by
  rintro f ⟨h1, h2⟩
  refine ⟨fun γ hγ x => ?_, h2⟩
  have := h1 γ hγ 1
  rw [mul_one] at this
  rw [h1 γ hγ, this]; simp

theorem finrank_cocyc_add_twInv_le_extn {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G)
    (hmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hone : ∀ v, ρ 1 v = v) (hs : s ^ 4 = 1)
    (hfd : FiniteDimensional ℂ (extn Γ ρ s)) :
    FiniteDimensional ℂ (cocyc Γ ρ) ∧
      Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s))
        ≤ Module.finrank ℂ (extn Γ ρ s) := by
  have hsurj : Function.Surjective (extnToCocyc Γ ρ s) := by
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, h⟩ := exists_extn_of_cocyc Γ ρ s hmul hone hs z hz
    exact ⟨⟨u, hu⟩, Subtype.ext (funext h)⟩
  refine ⟨Module.Finite.of_surjective _ hsurj, ?_⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (extnToCocyc Γ ρ s)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  let i : twInv Γ s (ρ s) →ₗ[ℂ] LinearMap.ker (extnToCocyc Γ ρ s) :=
    (Submodule.inclusion (twInv_le_extn Γ ρ s)).codRestrict _ (fun f => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext; funext γ
      have := f.2.1 γ γ.2 1
      rw [mul_one] at this
      show f.1 γ - f.1 1 = 0
      rw [this, sub_self])
  have hi : Function.Injective i := by
    intro a b hab
    exact Submodule.inclusion_injective _ (congrArg Subtype.val hab)
  have := LinearMap.finrank_le_finrank_of_injective hi
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def rightDefect (ρ : G → E →ₗ[ℂ] E) (t : G) : (G → E) →ₗ[ℂ] (G → E) where
  toFun u := fun x => u (x * t) - ρ t (u x)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, map_add (f := _)]
    abel
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

theorem rightDefect_apply (ρ : G → E →ₗ[ℂ] E) (t : G) (u : G → E) (x : G) :
    rightDefect ρ t u x = u (x * t) - ρ t (u x) := rfl

theorem rightDefect_mem_relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (hst : s ^ 2 = t ^ 3) (u : G → E)
    (hu : u ∈ extn Γ ρ s) : rightDefect ρ t u ∈ relThree Γ ρ t := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨ha, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have ha' : ∀ γ ∈ Γ, ∀ x, u (γ * x) = u x + ρ x (u γ - u 1) := by
    intro γ hγ x
    rw [← ha γ hγ x]
    abel
  have hs2 : ∀ x, u (x * t ^ 3) = ρ (t ^ 3) (u x) := by
    intro x
    rw [← hst, pow_two, ← mul_assoc, hb, hb, hρc]
  have p2 : t * t = t ^ 2 := (pow_two t).symm
  have p3 : t ^ 2 * t = t ^ 3 := (pow_succ t 2).symm
  have p3' : t * t ^ 2 = t ^ 3 := (pow_succ' t 2).symm
  simp only [relThree, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, rightDefect_apply]
  refine ⟨?_, ?_⟩
  · show (∀ h ∈ Γ, ∀ g : G, rightDefect ρ t u (h * g) = rightDefect ρ t u g) ∧
      ∀ g : G, rightDefect ρ t u (g * t ^ 3) = ρ (t ^ 3) (rightDefect ρ t u g)
    simp only [rightDefect_apply]
    refine ⟨?_, ?_⟩
    · intro h hh g
      rw [mul_assoc, ha' h hh (g * t), ha' h hh g, map_add (f := _), hρc]
      abel
    · intro g
      have e : g * t ^ 3 * t = g * t * t ^ 3 := by
        rw [mul_assoc, mul_assoc, (Commute.self_pow t 3).eq]
      rw [e, hs2, hs2, map_sub, hρc, hρc, (Commute.self_pow t 3).eq]
  · intro x
    have e1 : x * t * t = x * t ^ 2 := by rw [mul_assoc, p2]
    have e2 : x * t ^ 2 * t = x * t ^ 3 := by rw [mul_assoc, p3]
    rw [e1, e2, hs2, map_sub, map_sub, hρc, hρc, p3', p2]
    abel

theorem eq_zero_of_rightDefect_eq_zero (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (u : G → E)
    (hu : u ∈ extn Γ ρ s) (hΦ : rightDefect ρ t u = 0) (hu1 : u 1 = 0) : u = 0 := by
  simp only [extn, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
  obtain ⟨-, hb⟩ := hu
  have hρc : ∀ g h v, ρ h (ρ g v) = ρ (g * h) v := fun g h v => (hρ g h v).symm
  have hw : ∀ x, u (x * t) = ρ t (u x) := by
    intro x
    have hx := congrFun hΦ x
    rw [rightDefect_apply, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  let H : Subgroup G :=
    { carrier := {g | ∀ x, u (x * g) = ρ g (u x)}
      mul_mem' := by
        intro a b ha hb'
        simp only [Set.mem_ofPred_eq] at ha hb' ⊢
        intro x
        rw [← mul_assoc, hb', ha, hρc]
      one_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro x
        rw [mul_one, h1]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro x
        have hx := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at hx
        rw [hx, hρc, mul_inv_cancel, h1] }
  have hle : Subgroup.closure ({s, t} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hb
    · exact hw
  rw [hgen] at hle
  funext g
  have hg : g ∈ H := hle (Subgroup.mem_top g)
  have h1g := (show ∀ x, u (x * g) = ρ g (u x) from hg) 1
  rw [one_mul, hu1, map_zero] at h1g
  exact h1g

theorem finrank_extn_le {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]
    (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G)
    (hρ : ∀ g h v, ρ (g * h) v = ρ h (ρ g v)) (h1 : ∀ v, ρ 1 v = v) (hst : s ^ 2 = t ^ 3)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤) (hE : FiniteDimensional ℂ E)
    (hR : FiniteDimensional ℂ (relThree Γ ρ t)) :
    FiniteDimensional ℂ (extn Γ ρ s) ∧
      Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  have := hE
  have := hR
  have hmem : ∀ u : extn Γ ρ s, ((rightDefect ρ t).comp (extn Γ ρ s).subtype) u ∈ relThree Γ ρ t :=
    fun u => rightDefect_mem_relThree Γ ρ s t hρ hst u.1 u.2
  let Φ : extn Γ ρ s →ₗ[ℂ] relThree Γ ρ t × E :=
    LinearMap.prod (LinearMap.codRestrict (relThree Γ ρ t) ((rightDefect ρ t).comp (extn Γ ρ s).subtype) hmem)
      ((LinearMap.proj (R := ℂ) (φ := fun _ : G => E) (1 : G)).comp (extn Γ ρ s).subtype)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro u hu
    have h1' := congrArg (fun p : relThree Γ ρ t × E => (p.1 : G → E)) hu
    have h2' := congrArg Prod.snd hu
    exact Subtype.ext (eq_zero_of_rightDefect_eq_zero Γ ρ s t hρ h1 hgen u.1 u.2 h1' h2')
  have hfin : FiniteDimensional ℂ (extn Γ ρ s) := FiniteDimensional.of_injective Φ hinj
  refine ⟨hfin, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod] at hle

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem finrank_relThree_add_finrank_twInv_le :
    ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G)
      (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) →
      t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) →
      FiniteDimensional ℂ (relThree Γ ρ t) ∧
        Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤
          Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  intro G _ E _ _ Γ ρ t hmul hone ht hfd
  have h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v) := fun v => by rw [pow_two, hmul]
  have h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v)) := fun v => by
    rw [pow_succ t 2, hmul, h2]
  have h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v := fun v => by
    have h : t ^ 3 * t ^ 3 = 1 := by rw [← pow_add]; exact ht
    have h' := hmul (t ^ 3) (t ^ 3) v
    rw [h, hone, h3, h3] at h'
    exact h'.symm
  have e2 : ∀ x : G, x * t * t = x * t ^ 2 := fun x => by rw [pow_two, mul_assoc]
  have e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3 := fun x => by
    rw [mul_assoc, ← pow_succ']
  have hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3)) := fun Φ hΦ => hΦ.1
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  let P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t) :=
    { toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by
        obtain ⟨Φ, hΓ, hΦ⟩ := Φ
        refine ⟨fun γ hγ x => ?_, fun x => ?_⟩
        · simp only [mul_assoc, hΓ γ hγ]
        · simp only [e2, e3, hΦ, h2, h3, map_add (f := _)]
          abel⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        abel
      map_smul' := fun c Φ => by
        ext x
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }
  have hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2) :=
    fun _ _ => rfl
  have hsurj : LinearMap.range P = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Ψ, hΓ, hΨ⟩
    have hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x)) := fun x => by rw [← e2, hΨ, hΨ]
    have hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x))) := fun x => by rw [← e3, hΨ2, hΨ]
    refine ⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩
    · simp only [hΓ γ hγ]
    · simp only [hΨ3, h3, map_smul]
    · ext x
      rw [hP]
      simp only [hΨ, hΨ2, h2, map_smul, h6]
      module
  have hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    let ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P :=
      (Submodule.inclusion hle).codRestrict _ (fun Φ => by
        rw [LinearMap.mem_ker]
        ext x
        rw [hP]
        exact Φ.2.2 x)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro a b hab
    exact Submodule.inclusion_injective hle (congrArg Subtype.val hab)
  have hrk := LinearMap.finrank_range_add_finrank_ker P
  rw [hsurj, finrank_top] at hrk
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_point_slashEvaluations_independent_gamma : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  first | exact @GlobalTheory.CosetEval.evals_independent | exact GlobalTheory.CosetEval.evals_independent | (intros; apply GlobalTheory.CosetEval.evals_independent <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F ρ).det ≠ 0 → 3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  first | exact @GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | exact GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | (intros; apply GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) → ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧ (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  first | exact @GlobalTheory.OddFrame.descent | exact GlobalTheory.OddFrame.descent | (intros; apply GlobalTheory.OddFrame.descent <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ → ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  first | exact @GlobalTheory.OddFrame.reps_index | exact GlobalTheory.OddFrame.reps_index | (intros; apply GlobalTheory.OddFrame.reps_index <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.slashQExpansionCoeffWidth_transform : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧ (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧ (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  first | exact @GlobalTheory.OddFrame.co_transform | exact GlobalTheory.OddFrame.co_transform | (intros; apply GlobalTheory.OddFrame.co_transform <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (CuspForm Γ k) → (∀ j, IsCF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | exact GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | (intros; apply GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  first | exact @GlobalTheory.EisSep.exists_isMF_slash_ne | exact GlobalTheory.EisSep.exists_isMF_slash_ne | (intros; apply GlobalTheory.EisSep.exists_isMF_slash_ne <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) → (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finrank_sum_le_of_frame | exact GlobalTheory.OddFrame.finrank_sum_le_of_frame | (intros; apply GlobalTheory.OddFrame.finrank_sum_le_of_frame <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps : ∀ (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ), IsMF Γ K H → (∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) → ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  first | exact @GlobalTheory.exists_eq_discriminant_mul | exact GlobalTheory.exists_eq_discriminant_mul | (intros; apply GlobalTheory.exists_eq_discriminant_mul <;> assumption)
end
