module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle002
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]

theorem nonempty_of_surjective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (H : AddSubgroup X)
    (φ : X →+ Y) (hφ : Surjective φ) (hk : ∀ x, φ x = 0 ↔ x ∈ H) : Nonempty (Y ≃+ X ⧸ H) := by
  have : φ.ker = H := by ext x; rw [AddMonoidHom.mem_ker, hk]
  subst this
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm⟩

theorem nonempty_groupCohomology_even (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi0 : i ≠ 0) (hi : Even i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ TateZerothCohomology ρ g) := by
  have : NeZero i := ⟨hi0⟩
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπEven]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff (Rep.of ρ) g hg i hi x

theorem nonempty_groupCohomology_odd (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ H1 ρ g) := by
  let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπOdd]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (Rep.of ρ) g hg i hi x

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Obar : ValuationSubring (PadicAlgCl p) := (PadicAlgCl.valued p).v.valuationSubring

abbrev kbar : Type := IsLocalRing.ResidueField (Obar p)

variable {p} in
theorem mem_Obar_iff {x : PadicAlgCl p} : x ∈ Obar p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

noncomputable def resK : Subfield (kbar p) where
  toSubring := (K.toSubring.comap (Obar p).subtype).map (IsLocalRing.residue (Obar p))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases h0 : IsLocalRing.residue (Obar p) a = 0
    · rw [h0, inv_zero]; exact Subring.zero_mem _
    · have h0 := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 h0
      obtain ⟨u, rfl⟩ := h0
      refine ⟨((u⁻¹ : (Obar p)ˣ) : Obar p), ?_, ?_⟩
      · have h1 : (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = ((u : Obar p) : PadicAlgCl p)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have h2 : ((((u⁻¹ : (Obar p)ˣ) : Obar p) * (u : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
            rw [u.inv_mul]; rfl
          exact h2
        change (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) ∈ K
        rw [h1]
        exact K.inv_mem ha
      · apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, u.inv_mul, map_one]

noncomputable def qK : ℕ := Nat.card (resK p K)

noncomputable def Kn (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}

def IsFrobOn (n : ℕ) (φ : GK p K) : Prop :=
  ∀ x ∈ Kn p K n, ‖x‖ ≤ 1 → ‖φ x - x ^ qK p K‖ < 1

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer

open _root_.Neutral.B1

noncomputable section

def quotAddCongr {R R' A A' : Type} [Ring R] [Ring R'] [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R' A']
    (P : Submodule R A) (P' : Submodule R' A') (e : A ≃+ A') (h : ∀ x, x ∈ P ↔ e x ∈ P') : (A ⧸ P) ≃+ (A' ⧸ P') :=
  QuotientAddGroup.congr P.toAddSubgroup P'.toAddSubgroup e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩)

section Scalars

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation ℤ G M) (h : ∀ g m, rho g m = rho' g m)

def oneCocyclesScalarEquiv : Z1 rho ≃+ Z1 rho' where
  toFun f := ⟨f.1, f.2.1, fun g k => by rw [← h]; exact f.2.2 g k⟩
  invFun f := ⟨f.1, f.2.1, fun g k => by rw [h]; exact f.2.2 g k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def h1ScalarEquiv : H1 rho ≃+ H1 rho' :=
  quotAddCongr _ _ (oneCocyclesScalarEquiv rho rho' h) fun f => by
    show f.1 ∈ Bd1 rho ↔ f.1 ∈ Bd1 rho'
    simp only [mem_contCoboundaries1, h]

end Scalars

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem kbarRep_apply (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := rfl

theorem contAction_kbarRep : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro x
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun σ₀ => ?_)
  have hx := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  refine ⟨_, hx.preimage (continuous_const_mul σ₀⁻¹), ?_, ?_⟩
  · simp
  · intro σ hσ
    have h1 : (σ₀⁻¹ * σ) ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) := hσ
    have h2 : σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ₀ (Additive.toMul x : (PadicAlgCl p)ˣ) := by
      have := congrArg σ₀ h1
      simpa [AlgEquiv.mul_apply] using this
    exact Units.ext h2

def kT : ReciprocityTheory.Coh.TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := contAction_kbarRep p K

def muRep : Representation ℤ (GK p K) (ZMod n) where
  toFun g := (charRep (cycK p K n) g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by
    show charRep (cycK p K n) 1 x = x
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    show charRep (cycK p K n) (g * h) x = charRep (cycK p K n) g (charRep (cycK p K n) h x)
    rw [map_mul]; rfl

theorem muRep_apply (g : GK p K) (x : ZMod n) : muRep p K n g x = ((cycK p K n g : (ZMod n)ˣ) : ZMod n) * x := rfl

variable {p n}

def muMap (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) : ZMod n →ₗ[ℤ] KbarMult p :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun k => (Additive.ofMul (ζ ^ k.val) : KbarMult p)
      map_zero' := by simp; rfl
      map_add' := fun a b => by
        show ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val
        rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add] }

theorem muMap_apply (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (k : ZMod n) :
    muMap ζ hζ k = (Additive.ofMul (ζ ^ k.val) : KbarMult p) := rfl

theorem muMap_equiv (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (g : GK p K) (k : ZMod n) :
    muMap ζ hζ (muRep p K n g k) = kbarRep p K g (muMap ζ hζ k) := by
  rw [muMap_apply, muMap_apply, kbarRep_apply, muRep_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  have h1 : ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Units.val_one]
  have h2 := cycN_spec (K := K) (L := PadicAlgCl p) (n := n) g _ h1
  show _ = g ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  rw [h2, ← Units.val_pow_eq_pow_val, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, ← pow_mul, mul_comm]

theorem muMap_injective {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (muMap ζ hζ.pow_eq_one) := by
  intro a b hab
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)


variable (p n) in
def powMap : KbarMult p →ₗ[ℤ] KbarMult p := (n : ℤ) • LinearMap.id

theorem powMap_apply (x : (PadicAlgCl p)ˣ) :
    powMap p n (Additive.ofMul x : KbarMult p) = (Additive.ofMul (x ^ n) : KbarMult p) := by
  show (n : ℤ) • (Additive.ofMul x : Additive (PadicAlgCl p)ˣ) = _
  rw [natCast_zsmul]; rfl

theorem powMap_surjective : Function.Surjective (powMap p n) := by
  intro y
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hz
    exact (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : KbarMult p), ?_⟩
  rw [powMap_apply]
  exact congrArg Additive.ofMul (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz))

theorem exact_muMap_powMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by
  intro y
  constructor
  · intro hy
    have h1 : (Additive.toMul y : (PadicAlgCl p)ˣ) ^ n = 1 := by
      have := powMap_apply (p := p) (n := n) (Additive.toMul y)
      exact (this.symm.trans hy : _)
    have h2 : ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one h2
    have hi'' : ζ ^ i = (Additive.toMul y : (PadicAlgCl p)ˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi')
    refine ⟨(i : ZMod n), ?_⟩
    rw [muMap_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi'']; rfl
  · rintro ⟨k, rfl⟩
    rw [muMap_apply, powMap_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]; rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
end
