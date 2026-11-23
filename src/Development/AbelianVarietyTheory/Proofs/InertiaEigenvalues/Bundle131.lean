module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩

theorem stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩

end GlobalTheory.UnitLemma
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section PairOrbits

variable (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
  [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂)

theorem latPair_orbitRel_iff (p q : LatPair O E g₁ g₂) :
    (MulAction.orbitRel (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) p q ↔
      (MulAction.orbitRel A₁ˣ (stLat O E g₁)) p.1 q.1 ∧ (MulAction.orbitRel A₂ˣ (stLat O E g₂)) p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), ?_⟩
    rw [latPair_smul]
    have e₁ : Units.map (MonoidHom.fst A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₁ :=
      congrArg Prod.fst (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    have e₂ : Units.map (MonoidHom.snd A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₂ :=
      congrArg Prod.snd (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    rw [e₁, e₂, h₁, h₂]
    rfl

def latPairOrbitEquiv :
    MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂) ≃
      MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂) where
  toFun := Quotient.lift (fun p : LatPair O E g₁ g₂ => ((Quotient.mk _ p.1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)),
      (Quotient.mk _ p.2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))))
    (fun p q h => by
      obtain ⟨h₁, h₂⟩ := (latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ p q).1 h
      exact Prod.ext (Quotient.sound h₁) (Quotient.sound h₂))
  invFun x := Quotient.lift₂ (fun (a : stLat O E g₁) (b : stLat O E g₂) =>
      (Quotient.mk _ ((a, b) : LatPair O E g₁ g₂) : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound
      ((latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ (a₁, b₁) (a₂, b₂)).2 ⟨h₁, h₂⟩)) x.1 x.2
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h p => rfl
  right_inv x := by
    obtain ⟨x₁, x₂⟩ := x
    induction x₁ using Quotient.inductionOn with
    | h a => induction x₂ using Quotient.inductionOn with
      | h b => rfl

end PairOrbits

theorem latPair_orbit_finite_and_sum : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ h₁ h₂
  let e := latPairOrbitEquiv O E A₁ A₂ g₁ g₂
  haveI hfin : Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) := Finite.of_equiv _ e.symm
  refine ⟨hfin, ?_⟩
  intro f₁ f₂ hf₁ hf₂

  have inv₁ : ∀ a b : stLat O E g₁, (MulAction.orbitRel A₁ˣ (stLat O E g₁)) a b → f₁ a = f₁ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₁ t b
  have inv₂ : ∀ a b : stLat O E g₂, (MulAction.orbitRel A₂ˣ (stLat O E g₂)) a b → f₂ a = f₂ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₂ t b
  have key : ∀ x : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂),
      f₁ (Quotient.out (e.symm x)).1 * f₂ (Quotient.out (e.symm x)).2 = f₁ (Quotient.out x.1) * f₂ (Quotient.out x.2) := by
    intro x
    have hx : e (e.symm x) = x := e.apply_symm_apply x
    set o := e.symm x
    have h1 : (Quotient.mk _ (Quotient.out o).1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) = x.1 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    have h2 : (Quotient.mk _ (Quotient.out o).2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) = x.2 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    rw [inv₁ _ _ (Quotient.exact (h1.trans (Quotient.out_eq x.1).symm)),
      inv₂ _ _ (Quotient.exact (h2.trans (Quotient.out_eq x.2).symm))]
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁))
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))
  rw [← finsum_comp_equiv e.symm]
  simp_rw [key]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

end GlobalTheory.UnitLemma
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.PairStab

open GlobalTheory.UnitLemma Polynomial

theorem relIndex_prod_prod {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by
  have h : (H₁.prod H₂).subgroupOf (K₁.prod K₂) =
      ((H₁.subgroupOf K₁).prod (H₂.subgroupOf K₂)).comap (K₁.prodEquiv K₂).toMonoidHom := by
    ext x
    rfl
  unfold Subgroup.relIndex
  rw [h, Subgroup.index_comap_of_surjective _ (K₁.prodEquiv K₂).surjective, Subgroup.index_prod]

section

variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]

theorem intUnits_prod_eq :
    intUnits O (A₁ × A₂) = ((intUnits O A₁).prod (intUnits O A₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
  tauto

variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]

theorem stabilizer_latPair_eq (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂) :
    MulAction.stabilizer (A₁ × A₂)ˣ y = ((MulAction.stabilizer A₁ˣ y.1).prod
      (MulAction.stabilizer A₂ˣ y.2)).comap (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  rw [MulAction.mem_stabilizer_iff, latPair_smul, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Prod.ext_iff

end

theorem stabilizer_pair_relIndex : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ y h₁ h₂
  rw [stabilizer_latPair_eq, intUnits_prod_eq]
  refine ⟨Subgroup.comap_mono (fun t ht => ⟨h₁ ht.1, h₂ ht.2⟩), ?_⟩
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod_prod]

end GlobalTheory.UnitLemma.PairStab
end
end

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma

section Bridge

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem stabLat_eq_stabilizer (g : A) (L : stLat O E g) :
    stabLat O (L : Submodule O A) = MulAction.stabilizer Aˣ L := by
  ext t
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]
  constructor
  · intro h
    ext x
    rw [mem_mulLat_iff]
    have := h (((t⁻¹ : Aˣ) : A) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this
  · intro h y
    have := SetLike.ext_iff.mp h ((t : A) * y)
    rw [mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this

def orbEquiv (g : A) : Orb O (⊤ : Subgroup Aˣ) (stLat O E g) ≃ MulAction.orbitRel.Quotient Aˣ (stLat O E g) where
  toFun := Quot.lift (fun L => (Quotient.mk _ L : MulAction.orbitRel.Quotient Aˣ (stLat O E g)))
    (by
      rintro L M ⟨t, -, h⟩
      exact (Quotient.sound (show M ∈ MulAction.orbit Aˣ L from ⟨t, Subtype.ext (by rw [stLat_smul_val]; exact h.symm)⟩)).symm)
  invFun := Quotient.lift (fun L => (Quot.mk _ L : Orb O (⊤ : Subgroup Aˣ) (stLat O E g)))
    (by
      rintro a b ⟨t, ht⟩
      exact (Quot.sound ⟨t, Subgroup.mem_top t, by rw [← ht, stLat_smul_val]⟩).symm)
  left_inv := by
    intro o
    induction o using Quot.ind
    rfl
  right_inv := by
    intro o
    induction o using Quotient.inductionOn
    rfl

theorem stabilizer_eq_of_mem_orbit (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by
  obtain ⟨t, rfl⟩ := h
  ext s
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul,
    smul_left_cancel_iff]

theorem countGL_eq_sum_orbits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
    (g : A) : countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g),
      ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  change orbSum O ⊤ (stLat O E g) (fun _ => 1) = _
  unfold orbSum
  rw [← finsum_comp_equiv (orbEquiv (O := O) (E := E) g)]
  refine finsum_congr fun o => ?_
  have h1 : (Quotient.mk _ (Quot.out o) : MulAction.orbitRel.Quotient Aˣ (stLat O E g)) = orbEquiv g o := by
    conv_rhs => rw [← Quot.out_eq o]
    rfl
  have h2 := Quotient.out_eq (orbEquiv (O := O) (E := E) g o)
  have h3 := Quotient.exact (h2.trans h1.symm)
  rw [one_mul, inf_top_eq, inf_top_eq, stabLat_eq_stabilizer g (Quot.out o),
    stabilizer_eq_of_mem_orbit g h3]

end Bridge

end GlobalTheory.UnitLemma
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem tm_isClosedEmbedding : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : A.K ≃ₜ (Fin r → F) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F :=
    (Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap
  have hg : IsClosedEmbedding g := by
    refine LinearMap.isClosedEmbedding_of_injective ?_
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 := Algebra.leftMulMatrix_injective (bas A hG) hxy
    exact e.symm.injective h1
  let f : A.K → Matrix (Fin r) (Fin r) F := fun x => Algebra.leftMulMatrix (bas A hG) x
  have hf : IsClosedEmbedding f := by
    have : f = g ∘ eh := by
      funext x; simp [f, g, eh, e]
    rw [this]; exact hg.comp eh.isClosedEmbedding
  haveI : T2Space A.K := eh.isEmbedding.t2Space
  have hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) :=
    hf.prodMap hfo
  have hK : IsClosedEmbedding (Units.embedProduct A.K) := Units.isClosedEmbedding_embedProduct
  have hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F)) := Units.isClosedEmbedding_embedProduct
  have hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) =
      (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K := by
    funext t
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact tm_coe A hG t
    · simp only
      rw [tm_inv_coe]
  have hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
    rw [hcomp]; exact hP.comp hK
  have hcont : Continuous (LinDesc.tm A hG) := by
    rw [hM.isInducing.continuous_iff]; exact hc.continuous
  refine ⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩
  · intro x y hxy
    exact hc.injective (by simp [Function.comp_apply, hxy])
  · have : Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, hM.injective ht⟩
    rw [this]; exact hc.isClosed_range.preimage hM.continuous

end GlobalTheory.JR.LinDesc
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.descFn_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  intro F E _ _ _ _ _ A r M Ax j lam α hαl hαc f hf

  have hstar : Continuous (star : E → E) := by
    have : Isometry (starAddEquiv : E ≃+ E) :=
      (AddMonoidHomClass.isometry_iff_norm (starAddEquiv : E ≃+ E)).2 (fun x => Unram.norm_star F x)
    exact this.continuous
  haveI : ContinuousStar E := ⟨hstar⟩
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjs : Continuous j.symm :=
    LinearMap.continuous_of_finiteDimensional ((j.symm : (Fin r → E) →ₗ[E] A.L).restrictScalars F)

  have hact : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (actU p.2 (Ax, j p.1, lam) : Hn r F E)) := by
    have hg : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (p.2 : Matrix (Fin r) (Fin r) E)) :=
      continuous_subtype_val.comp continuous_snd
    have c1 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) * Ax.1 * star (p.2 : Matrix (Fin r) (Fin r) E)) :=
      (hg.mul continuous_const).mul hg.star
    have c2 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) *ᵥ j p.1) :=
      Continuous.matrix_mulVec hg (hj.comp continuous_fst)
    exact Continuous.prodMk (Continuous.subtype_mk c1 _) (Continuous.prodMk c2 continuous_const)
  set Φ : A.L × Matrix.unitaryGroup (Fin r) E → ℂ := fun p => f (actU p.2 (Ax, j p.1, lam)) * (α p.2 : ℂ) with hΦ
  have hΦl : IsLocallyConstant Φ := by
    refine IsLocallyConstant.mul (hf.1.comp_continuous hact) ?_
    exact (hαl.comp_continuous continuous_snd).comp (fun x : ℝ => (x : ℂ))
  have hdesc : ∀ y, A.descFn M Ax j lam α f y = (letI := M.mU; ∫ g, Φ (y, g) ∂M.μU) := fun y => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y0
    have key : ∀ᶠ y in 𝓝 y0, ∀ g ∈ tsupport α, Φ (y, g) = Φ (y0, g) := by
      refine hαc.isCompact.eventually_forall_of_forall_eventually ?_
      intro g _
      have h1 := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦl (y0, g)
      have h2 : ∀ᶠ z : A.L × Matrix.unitaryGroup (Fin r) E in 𝓝 (y0, g), Φ (y0, z.2) = Φ (y0, g) := by
        have h3 : Tendsto (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) (𝓝 (y0, g)) (𝓝 (y0, g)) := by
          have : Continuous (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) :=
            continuous_const.prodMk continuous_snd
          simpa using this.tendsto (y0, g)
        exact h3.eventually h1
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    rw [hdesc, hdesc]
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hy g hg
    · have : α g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [hΦ, this]
  · let S : Set (Fin r → E) := Prod.fst '' (Prod.snd '' tsupport f)
    let Kset : Set A.L := (fun p : Matrix.unitaryGroup (Fin r) E × (Fin r → E) => j.symm (star (p.1 : Matrix (Fin r) (Fin r) E) *ᵥ p.2)) '' (tsupport α ×ˢ S)
    have hS : IsCompact S :=
      (hf.2.isCompact.image continuous_snd).image continuous_fst
    have hK : IsCompact Kset := by
      refine (hαc.isCompact.prod hS).image ?_
      refine hjs.comp ?_
      exact Continuous.matrix_mulVec ((continuous_subtype_val.comp continuous_fst).star) continuous_snd
    have hKc : IsClosed Kset := by
      have h1 : IsClosed (j '' Kset) := (hK.image hj).isClosed
      have h2 : Kset = j ⁻¹' (j '' Kset) := (Set.preimage_image_eq _ j.injective).symm
      rw [h2]
      exact h1.preimage hj
    refine HasCompactSupport.intro' hK hKc ?_
    intro y hy
    by_contra hne
    rw [hdesc] at hne
    have : ∃ g, Φ (y, g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      have : (fun g => Φ (y, g)) = fun _ => 0 := funext hall
      rw [this]
      simp
    obtain ⟨g, hg⟩ := this
    have hfg : f (actU g (Ax, j y, lam)) ≠ 0 := left_ne_zero_of_mul hg
    have hαg : (α g : ℂ) ≠ 0 := right_ne_zero_of_mul hg
    have hαg' : α g ≠ 0 := by exact_mod_cast hαg
    apply hy
    refine ⟨(g, g.1 *ᵥ j y), ⟨subset_tsupport _ hαg', ?_⟩, ?_⟩
    · exact ⟨(actU g (Ax, j y, lam)).2, ⟨actU g (Ax, j y, lam), subset_tsupport _ hfg, rfl⟩, rfl⟩
    · simp only [Matrix.mulVec_mulVec]
      have hu : star (g.1 : Matrix (Fin r) (Fin r) E) * g.1 = 1 := Matrix.UnitaryGroup.star_mul_self g
      rw [hu, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
end
