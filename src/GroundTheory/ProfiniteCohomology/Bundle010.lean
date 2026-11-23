module

public import GroundTheory.ProfiniteCohomology.Bundle009
public import GroundTheory.ProfiniteCohomology.Bundle006
public import GroundTheory.ProfiniteCohomology.Shapiro
public import GroundTheory.ProfiniteCohomology.CyclicCup
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle001
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle002
import GroundTheory.ProfiniteCohomology.OpenNormal
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Counting

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

theorem card_eq_card_ker_mul_card_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h1 := AddSubgroup.card_mul_index f.toAddMonoidHom.ker
  rw [AddSubgroup.index_ker] at h1
  exact h1.symm

end Counting

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerChar_eq (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar A = (Nat.card (cohomology A 0) : ℚ) * Nat.card (cohomology A 2) /
      Nat.card (cohomology A 1) := by
  simp [eulerChar, Finset.prod_range_succ, div_eq_mul_inv]
  ring

section ShortExact

theorem card_range_eq_card_ker_of_exact {T : ShortComplex (ModuleCat k)} (hT : T.Exact) :
    Nat.card (LinearMap.range T.f.hom) = Nat.card (LinearMap.ker T.g.hom) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hT
  rw [hT]

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem eulerChar_shortExact_of_finite (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)]
    [Subsingleton (cohomology S.X₁ 3)] :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (cohomologyMap S.f i).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact ((cochainsShortComplex_shortExact hS).homology_exact₂ i)
  have e30 : Nat.card (LinearMap.range (cohomologyMap S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (cohomologyMap S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (cohomologyMap S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (cohomologyMap S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (cohomologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (cochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have htop : Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) = 1 :=
    Nat.card_of_subsingleton (0 : LinearMap.range (δ hS 2 3 rfl).hom)
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (cohomologyMap S.f 1), ← e10] at hA1
  rw [hk (cohomologyMap S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerChar_eq, eulerChar_eq, eulerChar_eq,
    hk (cohomologyMap S.f 0), hk (cohomologyMap S.f 1), hk (cohomologyMap S.f 2),
    hk (cohomologyMap S.g 0), hk (cohomologyMap S.g 1), hk (cohomologyMap S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, htop, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

end ShortExact

section Hypothesis

variable {P : ℕ → Prop}

theorem eulerChar_pos (hG : HasFiniteCohomology (k := k) (G := G) P)
    (A : Rep.{u} k G) [IsDiscreteRep A]
    [Finite A] (hA : P (Nat.card A)) : 0 < eulerChar A := by
  obtain ⟨hfin, -⟩ := hG A ‹_› hA
  have h0 := hfin 0
  have h1 := hfin 1
  have h2 := hfin 2
  rw [eulerChar_eq]
  have p0 : (0 : ℚ) < Nat.card (cohomology A 0) := by exact_mod_cast Nat.card_pos
  have p1 : (0 : ℚ) < Nat.card (cohomology A 1) := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℚ) < Nat.card (cohomology A 2) := by exact_mod_cast Nat.card_pos
  positivity

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem eulerChar_shortExact_of_mem (hG : HasFiniteCohomology (k := k) (G := G) P)
    (hS : S.ShortExact) [Finite S.X₁] [Finite S.X₂] [Finite S.X₃] (h₁ : P (Nat.card S.X₁))
    (h₂ : P (Nat.card S.X₂)) (h₃ : P (Nat.card S.X₃)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  obtain ⟨f₁, z₁⟩ := hG S.X₁ ‹_› h₁
  have := f₁ 1
  have := z₁ 3 le_rfl
  have := (hG S.X₂ ‹_› h₂).1 1
  have := (hG S.X₃ ‹_› h₃).1 1
  exact eulerChar_shortExact_of_finite hS

theorem eulerChar_shortExact (hP : ∀ m n, m ∣ n → P n → P m)
    (hG : HasFiniteCohomology (k := k) (G := G) P)
    (hS : S.ShortExact) [Finite S.X₂] (h₂ : P (Nat.card S.X₂)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have : Finite S.X₁ := Finite.of_injective _ hinj
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have h₁ : P (Nat.card S.X₁) :=
    hP _ _ (AddSubgroup.card_dvd_of_injective S.f.hom.toLinearMap.toAddMonoidHom hinj) h₂
  have h₃ : P (Nat.card S.X₃) := by
    refine hP _ _ ⟨Nat.card (LinearMap.ker S.g.hom.toLinearMap), ?_⟩ h₂
    rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap,
      LinearMap.range_eq_top.2 hsurj, mul_comm]
    congr 1
    exact Nat.card_congr (Submodule.topEquiv).toEquiv
  exact eulerChar_shortExact_of_mem hG hS h₁ h₂ h₃

end Hypothesis

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G)

theorem eulerChar_coind (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] :
    eulerChar (Rep.coind (U : Subgroup G).subtype B) = eulerChar B := by
  simp only [eulerChar]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.card_congr (shapiroIso U B q).toLinearEquiv.toEquiv]

theorem eulerChar_res_eq_eulerChar_coind (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar (Rep.res (U : Subgroup G).subtype A) =
      eulerChar (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  (eulerChar_coind U _).symm

noncomputable def coindValues (B : Rep.{u} k (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype B →+ (G ⧸ (U : Subgroup G) → B) :=
  AddMonoidHom.mk' (fun f c => f.1 (Quotient.out c)⁻¹) fun _ _ => rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem coindValues_injective (B : Rep.{u} k (U : Subgroup G)) :
    Function.Injective (coindValues U B) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) x⁻¹
  have hx : x = (U : Subgroup G).subtype u * (Quotient.out
      (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)))⁻¹ := by
    rw [show (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G))) = x⁻¹ * u from hu]
    simp
  have h := congrFun hfg (QuotientGroup.mk x⁻¹)
  simp only [coindValues, AddMonoidHom.mk'_apply] at h
  rw [hx, f.2 u, g.2 u, h]

instance finite_coind (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Finite (Rep.coind (U : Subgroup G).subtype B) :=
  Finite.of_injective _ (coindValues_injective U B)

theorem card_coind_dvd (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Nat.card (Rep.coind (U : Subgroup G).subtype B) ∣ Nat.card B ^ (U : Subgroup G).index := by
  have h := AddSubgroup.card_dvd_of_injective (coindValues U B) (coindValues_injective U B)
  rwa [Nat.card_fun] at h

end Shapiro

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

def charAdd {G : Type} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    Additive G →+ AddCircle (1 : ℚ) :=
  QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem charAdd_apply (χ : Additive G →ₜ+ QZ) (x : Additive G) :
    charAdd χ x = QZ.toAddCircle (χ x) :=
  rfl

omit [IsTopologicalGroup G] in
theorem isLocallyConstant_charAdd (χ : Additive G →ₜ+ QZ) :
    IsLocallyConstant fun g : G => charAdd χ (Additive.ofMul g) := by
  have hc : Continuous fun g : G => χ (Additive.ofMul g) :=
    χ.continuous_toFun.comp continuous_ofMul
  have h := IsLocallyConstant.comp_continuous
    (IsLocallyConstant.of_discrete (X := QZ) (fun x : QZ => QZ.toAddCircle x)) hc
  exact h

theorem exists_cocycle_H0Iso_inv {k : Type} [CommRing k] (A : Rep k G) [IsDiscreteRep A]
    (a : A.ρ.invariants) :
    ∃ z : cocycles A 0, cohomologyπ A 0 z = (H0Iso A).inv.hom a ∧
      cochainOf (A := A) (cocycleι (A := A) (p := 0) z) = fun _ => (a : A) := by
  refine ⟨(cocyclesIso₀ A).inv.hom a, rfl, ?_⟩
  have hf : (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochainsComplex A).iCycles 0 := by
    dsimp only [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit]
    exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)
  have e := ConcreteCategory.congr_hom hf ((cocyclesIso₀ A).inv a)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at e
  exact (congrArg (cochainOf (A := A)) e).symm

section Cocycles

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

theorem exists_cocycle_charH1 (χ : Additive G →ₜ+ QZ) :
    ∃ z : cocycles (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1,
      cohomologyπ _ 1 z = (cohomologyOneRatModIntIso G).inv.hom χ ∧
      ∀ v : Fin 1 → G, cochainOf (A := Rep.trivial ℤ G (AddCircle (1 : ℚ)))
        (cocycleι (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1 z) v = charAdd χ (Additive.ofMul (v 0)) := by
  obtain ⟨z, hz⟩ := cohomologyπ_surjective _ 1 ((cohomologyOneRatModIntIso G).inv.hom χ)
  refine ⟨z, hz, fun v => ?_⟩
  have h1 : (cohomologyOneRatModIntIso G).hom.hom (cohomologyπ _ 1 z) = χ := by
    rw [hz]
    exact congrArg (fun f => f.hom χ) (cohomologyOneRatModIntIso G).inv_hom_id
  simp only [cohomologyOneRatModIntIso, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    at h1
  change (locallyConstantHomQZEquiv G) ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom
    (cohomologyπ _ 1 z)) = χ at h1
  have h4 := DFunLike.congr_fun h1 (Additive.ofMul (v 0))
  rw [locallyConstantHomQZEquiv_apply] at h4
  have h2 := cohomologyOneIsoOfIsTrivial_hom_cohomologyπ G (AddCircle (1 : ℚ)) z (v 0)
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have h5 := congrArg QZ.toAddCircle h4
  rw [AddEquiv.apply_symm_apply] at h5
  rw [charAdd_apply, ← h5]
  conv_lhs => rw [hv]
  exact h2.symm

theorem exists_cocycle_charClassProf (χ : Additive G →ₜ+ QZ) :
    ∃ x : cocycles (Rep.trivial ℤ G ℤ) 2, cohomologyπ _ 2 x = charClassProf χ ∧
      ∀ v : Fin 2 → G, cochainOf (A := Rep.trivial ℤ G ℤ) (cocycleι (Rep.trivial ℤ G ℤ) 2 x) v =
        charCocycle (charAdd χ) (v 0, v 1) := by
  obtain ⟨z, hz, hzv⟩ := exists_cocycle_charH1 χ
  let y : (Fin 1 → G) → ℚ := fun v => reprIco (charAdd χ (Additive.ofMul (v 0)))
  have hy : IsLocallyConstant y :=
    (((isLocallyConstant_charAdd χ).comp_continuous (continuous_apply 0)).comp reprIco)
  let x₂ := mkCochain (A := (ratSES G).X₂) y hy
  have hx₂ : (cochainsMap (ratSES G).g).f 1 x₂ = cocycleι (A := (ratSES G).X₃) (p := 1) z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    exact (coe_reprIco _).trans (hzv v).symm
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d (ratSES_shortExact G) 2 z x₂ hx₂
  refine ⟨x₁, ?_, fun v => ?_⟩
  · rw [charClassProf, ← hz]
    exact (δ_cohomologyπ_of_lift (ratSES_shortExact G) rfl z x₂ hx₂ x₁ hx₁).symm
  · have e := congrArg (fun c => cochainOf (A := (ratSES G).X₂) c v) hx₁
    simp only [cochainOf_cochainsMap_f] at e
    erw [cochainOf_d, d_one_trivial_apply] at e
    have hc := charCocycle_cast (charAdd χ) (v 0) (v 1)
    apply Int.cast_injective (α := ℚ)
    refine e.trans ?_
    rw [hc]
    change reprIco (charAdd χ (Additive.ofMul (v 1))) - reprIco (charAdd χ (Additive.ofMul (v 0 * v 1)))
      + reprIco (charAdd χ (Additive.ofMul (v 0))) = _
    ring

theorem exists_cocycle_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w = (cupCharClassProf A χ).hom a ∧
      ∀ v : Fin 2 → G, cochainOf (A := A) (cocycleι (A := A) (p := 2) w) v =
        charCocycle (charAdd χ) (v 0, v 1) • (a : A) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv A a
  obtain ⟨x, hx, hxc⟩ := exists_cocycle_charClassProf χ
  let φ : A ⊗ Rep.trivial ℤ G ℤ ⟶ A := (ρ_ A).hom
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap φ) 2 (cupCocycles (zero_add 2) z0 x), ?_, ?_⟩
  · change _ = (cohomologyMap φ 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom a) (charClassProf χ))
    rw [← hz0, ← hx, cup_cohomologyπ]
    exact (ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap φ 2) _).symm
  · intro v
    have e := congrArg (fun ψ => cochainOf (A := A) (ψ.hom (cupCocycles (zero_add 2) z0 x)))
      (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change cochainOf (A := A) (((cochainsComplex A).iCycles 2).hom _) v = _
    rw [e, cochainOf_cochainsMap_f]
    change φ.hom (cochainOf (A := A ⊗ Rep.trivial ℤ G ℤ)
      (cocycleι (A ⊗ Rep.trivial ℤ G ℤ) 2 (cupCocycles (zero_add 2) z0 x)) v) = _
    rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cupCochain_apply, hz0c]
    erw [hxc, rightUnitor_hom_tmul]
    exact int_smul_eq_zsmul _ _ _

theorem cupCharClassProf_eq_inflation [CompactSpace G] (A : Rep ℤ G) [IsDiscreteRep A]
    (χ : Additive G →ₜ+ QZ) (U : OpenNormalSubgroup G)
    (ψ : Additive (G ⧸ (U : Subgroup G)) →+ AddCircle (1 : ℚ))
    (hψ : charAdd χ = charComp (U : Subgroup G) ψ) (a : A.ρ.invariants) :
    (cupCharClassProf A χ).hom a =
      (inflation A U 2).hom ((cupCharClass (A.quotientToInvariants (U : Subgroup G)) ψ).hom
        (invariantsToQuotient (U : Subgroup G) a)) := by
  have := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  change _ = (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((groupCohomology.isoCocycles₂ _).inv _))
  rw [inflation_π]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cyclesMap_inflationCochains]
  funext v
  rw [hwc, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  rw [hψ]
  rfl

end Cocycles

end Profinite

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Iso

variable {k G : Type*} [CommRing k] [Monoid G]

def Rep.isoOfBijective {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    A ≅ B :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective f.hom hf)

end Iso

section ZMod

variable (G : Type*) [Monoid G]

abbrev zmodRep (n : ℕ) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod n))

end ZMod

attribute [local instance 2000] Rep.hV2

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) : Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  Rep.of (Representation.linHom M.ρ (galUnits.{u} K L).ρ)

variable {K L}

theorem cartierDual_ρ_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (σ : Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    ((cartierDual K L M).ρ σ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m =
      (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

variable (K L)

def evalBilin (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M →ₗ[ULift.{u} ℤ] (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) →ₗ[ULift.{u} ℤ] galUnits.{u} K L where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def cartierPairing (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M ⊗ cartierDual K L M ⟶ galUnits.{u} K L :=
  pairingHom (evalBilin K L M) fun σ m f => by
    change (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = (galUnits.{u} K L).ρ σ (f m)
    rw [Representation.inv_self_apply]

variable {K L}

@[simp]
theorem cartierPairing_tmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (m : M)
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    (cartierPairing K L M).hom (m ⊗ₜ[ULift.{u} ℤ] (f : cartierDual K L M) :
      (M ⊗ cartierDual K L M : Rep _ _)) = f m :=
  pairingHom_tmul (A := M) (B := cartierDual K L M) (evalBilin K L M) _ m f

variable (K L)

variable {K L}

end GroundTheory.ProfCoh
end
end
