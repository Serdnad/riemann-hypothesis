module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle006
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle008
public import Mathlib.Tactic.ENatToNat
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
open scoped ZeroObject

universe w' u

noncomputable section

variable {X : Scheme.{u}}

lemma eq_zero_of_isTerminal {T : AddCommGrpCat.{u}} (hT : IsTerminal T) (s : T) : s = 0 := by
  let f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T :=
    AddCommGrpCat.ofHom ((zmultiplesHom T s).comp AddEquiv.ulift.toAddMonoidHom)
  have h := congrArg (fun g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T => g.hom (⟨1⟩ : ULift.{u} ℤ))
    (hT.hom_ext f 0)
  have h1 : (AddEquiv.ulift (⟨1⟩ : ULift.{u} ℤ) : ℤ) = 1 := rfl
  simp only [f] at h
  rwa [AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1, zmultiplesHom_apply, one_smul] at h

lemma eq_zero_of_bot (F : X.Modules) (s : Γ(F, ⊥)) : s = 0 :=
  eq_zero_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty (modulesAb F)) s

lemma isZero_of_forall_eq_zero (F : X.Modules) (h : ∀ (U : X.Opens) (s : Γ(F, U)), s = 0) :
    IsZero F := by
  have : IsIso (0 : F ⟶ 0) := isIso_of_bijective_app _ fun U =>
    ⟨fun a b _ => (h U a).trans (h U b).symm,
     fun t => ⟨0, (eq_zero_of_isZero (isZero_zero _) U t).symm ▸ map_zero _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

namespace Scheme.Modules.SupportedIn

lemma univ (F : X.Modules) : Scheme.Modules.SupportedIn F Set.univ := by
  intro U hU s
  have hU' : U = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => Set.disjoint_left.1 hU hx trivial
  subst hU'
  exact eq_zero_of_bot F s

lemma inter {F : X.Modules} {T₁ T₂ : Set X} (h₁ : Scheme.Modules.SupportedIn F T₁)
    (h₂ : Scheme.Modules.SupportedIn F T₂) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) :
    Scheme.Modules.SupportedIn F (T₁ ∩ T₂) := by
  intro U hU s
  let U₁ : X.Opens := U ⊓ ⟨T₁ᶜ, hT₁.isOpen_compl⟩
  let U₂ : X.Opens := U ⊓ ⟨T₂ᶜ, hT₂.isOpen_compl⟩
  have hcov : U ≤ U₁ ⊔ U₂ := by
    intro x hx
    by_cases hx₁ : x ∈ T₁
    · refine Or.inr ⟨hx, fun hx₂ => Set.disjoint_left.1 hU hx ⟨hx₁, hx₂⟩⟩
    · exact Or.inl ⟨hx, hx₁⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ (modulesAb F) (homOfLE inf_le_left)
    (homOfLE inf_le_left) hcov s 0 ?_ ?_
  · rw [map_zero]
    exact h₁ U₁ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _
  · rw [map_zero]
    exact h₂ U₂ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _

lemma of_mono {F G : X.Modules} (m : F ⟶ G) [Mono m] {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) : Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have h1 : Mono ((Scheme.Modules.toPresheaf X).map m) := Functor.map_mono _ m
  have h2 : Mono (((Scheme.Modules.toPresheaf X).map m).app (op U)) := inferInstance
  have hinj : Function.Injective (m.app U) := (AddCommGrpCat.mono_iff_injective _).1 h2
  apply hinj
  rw [map_zero]
  exact h U hU _

lemma isZero_restrict {F : X.Modules} {T : Set X} (h : Scheme.Modules.SupportedIn F T)
    (U : X.Opens) (hU : Disjoint (U : Set X) T) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F) := by
  refine isZero_of_forall_eq_zero _ fun V s => h (U.ι ''ᵁ V) ?_ s
  refine hU.mono_left ?_
  exact (U.ι.image_le_opensRange V).trans (by simp)

lemma of_isZero_restrict {F : X.Modules} {T : Set X}
    (h : ∀ U : X.Opens, Disjoint (U : Set X) T →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F)) :
    Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have hE : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_idem U
  have h0 : F.presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero (h U hU) (U.ι ⁻¹ᵁ U) _
  have hinv : F.presheaf.map (eqToHom hE.symm).op (F.presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

lemma of_epi {F G : X.Modules} (e : F ⟶ G) [Epi e] {T : Set X}
    (h : Scheme.Modules.SupportedIn F T) : Scheme.Modules.SupportedIn G T := by
  refine of_isZero_restrict fun U hU => ?_
  have : Epi ((Scheme.Modules.restrictFunctor U.ι).map e) := Functor.map_epi _ e
  exact (isZero_restrict h U hU).of_epi ((Scheme.Modules.restrictFunctor U.ι).map e)

lemma isZero_of_empty {F : X.Modules} (h : Scheme.Modules.SupportedIn F ∅) : IsZero F :=
  isZero_of_forall_eq_zero F fun U s => h U (Set.disjoint_empty _) s

end Scheme.Modules.SupportedIn

section Cohomology

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

lemma H_eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) {p : ℕ}
    (x : Sheaf.H.{w'} (modulesAb F) p) : x = 0 := by
  have hF' : IsZero (modulesAb F) := Functor.map_isZero _ hF
  change Abelian.Ext _ _ p at x
  rw [← Abelian.Ext.comp_mk₀_id x, hF'.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

theorem FiniteH.of_isZero (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)] {F : X.Modules}
    (hF : IsZero F) : FiniteH.{w'} A F := fun p =>
  have : Subsingleton (Sheaf.H.{w'} (modulesAb F) p) :=
    ⟨fun x y => (H_eq_zero_of_isZero hF x).trans (H_eq_zero_of_isZero hF y).symm⟩
  Module.Finite.of_finite

end Cohomology

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A] [X.Over (Spec (.of A))]

attribute [local instance] algebraOfOver

variable (I : Ideal A) (F : X.Modules)

lemma exists_smulHom_eq_comp_idealSumMap (J : Ideal A) {a : A} (ha : a ∈ J) :
    ∃ h : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      smulHom F (algebraMap A Γ(X, ⊤) a) = h ≫ idealSumMap F J := by
  rw [← span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 ha
  refine ⟨biproduct.lift fun j => smulHom F (algebraMap A Γ(X, ⊤) (c j)), ?_⟩

  simp only [idealSumMap, biproduct.lift_desc, smulHom_comp_smulHom, ← map_mul, ← smulHom_sum,
  ← map_sum]
  rw [hc]

def idealPowOfMem {k : ℕ} (a : A) (ha : a ∈ I ^ k) : F ⟶ idealPow I F k :=
  kernel.lift _ (smulHom F (algebraMap A Γ(X, ⊤) a)) (by
    obtain ⟨h, hh⟩ := exists_smulHom_eq_comp_idealSumMap F (I ^ k) ha
    rw [hh, Category.assoc, cokernel.condition, comp_zero])

lemma idealPowOfMem_ι {k : ℕ} (a : A) (ha : a ∈ I ^ k) :
    idealPowOfMem I F a ha ≫ idealPowι I F k = smulHom F (algebraMap A Γ(X, ⊤) a) :=
  kernel.lift_ι _ _ _

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits IsLocalRing MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (X : Scheme.{u})
  [X.Over (Spec (.of A))]

abbrev closedFibre : Set X := (X ↘ Spec (.of A)).base ⁻¹' {closedPoint A}

variable {X}


omit [IsNoetherianRing A] [IsLocalRing A] in
lemma mem_basicOpen_algebraMap_iff (x : X) (a : A) :
    x ∈ X.basicOpen (algebraMap A Γ(X, ⊤) a) ↔ a ∉ ((X ↘ Spec (.of A)).base x).asIdeal := by
  have h1 : algebraMap A Γ(X, ⊤) a = (X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
    rfl
  rw [h1, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl


omit [IsNoetherianRing A] in
lemma exists_mem_basicOpen_of_not_mem_closedFibre {x : X} (hx : x ∉ closedFibre (A := A) X) :
    ∃ a ∈ maximalIdeal A, x ∈ X.basicOpen (algebraMap A Γ(X, ⊤) a) := by
  set y := (X ↘ Spec (.of A)).base x
  have hne : y ≠ closedPoint A := hx
  have hnot : ¬ (maximalIdeal A ≤ y.asIdeal) := by
    intro h
    apply hne
    exact PrimeSpectrum.ext (le_antisymm (le_maximalIdeal y.isPrime.ne_top) h)
  obtain ⟨a, ha, hay⟩ := Set.not_subset.1 hnot
  exact ⟨a, ha, (mem_basicOpen_algebraMap_iff x a).2 hay⟩


omit [IsNoetherianRing A] in
lemma not_mem_basicOpen_of_mem_closedFibre {x : X} (hx : x ∈ closedFibre (A := A) X) {a : A}
    (ha : a ∈ maximalIdeal A) : x ∉ X.basicOpen (algebraMap A Γ(X, ⊤) a) := by
  rw [mem_basicOpen_algebraMap_iff, not_not]
  have : (X ↘ Spec (.of A)).base x = closedPoint A := hx
  rw [this]
  exact ha


variable (A X) in
abbrev fibreQuot (n : ℕ) : X.Modules := quotPow (maximalIdeal A) (𝟙_ X.Modules) n


variable (A X) in
abbrev fibreOne (n : ℕ) : Γ(fibreQuot A X n, ⊤) :=
  (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n).app ⊤ (1 : Γ(X, ⊤))

instance : (𝟙_ X.Modules).IsQuasicoherent := isQuasicoherent_unit X

lemma eq_zero_of_isAffineOpen_le_basicOpen {V : X.Opens} (hV : IsAffineOpen V) {a : A}
    (ha : a ∈ maximalIdeal A) (hVa : V ≤ X.basicOpen (algebraMap A Γ(X, ⊤) a)) (n : ℕ)
    (t : Γ(fibreQuot A X n, V)) : t = 0 := by
  obtain ⟨u, rfl⟩ := surjective_quotPowπ_app (maximalIdeal A) (𝟙_ X.Modules) hV n t
  rw [quotPowπ_app_eq_zero_iff _ _ hV]
  have hunit : IsUnit (toFunctions V (a ^ (n + 1))) := by
    rw [map_pow]
    refine IsUnit.pow _ ?_
    have h := X.toRingedSpace.isUnit_res_basicOpen (algebraMap A Γ(X, ⊤) a)
    have e : toFunctions V a = X.presheaf.map (homOfLE hVa).op
        (X.presheaf.map (homOfLE (X.basicOpen_le (algebraMap A Γ(X, ⊤) a))).op
          (algebraMap A Γ(X, ⊤) a)) := by
      change (X.presheaf.map (homOfLE le_top).op).hom _ = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [e]
    exact h.map _
  have htop : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow ha _)) hunit
  rw [htop, Submodule.top_smul]
  exact Submodule.mem_top

lemma supportedIn_fibreQuot_closedFibre (n : ℕ) :
    Scheme.Modules.SupportedIn (fibreQuot A X n) (closedFibre (A := A) X) := by
  intro U hU s
  apply sheaf_eq_of_locally (modulesAb (fibreQuot A X n)) s 0
  intro x hxU
  have hx : x ∉ closedFibre (A := A) X := fun h => Set.disjoint_left.1 hU hxU h
  obtain ⟨a, ha, hxa⟩ := exists_mem_basicOpen_of_not_mem_closedFibre hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_inter hxU hxa) (U ⊓ X.basicOpen (algebraMap A Γ(X, ⊤) a)).2
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  refine ⟨V, hVU, hxV, ?_⟩
  rw [map_zero]
  exact eq_zero_of_isAffineOpen_le_basicOpen hV ha (fun y hy => (hVle hy).2) n _

lemma resF_fibreOne_ne_zero {x : X} (hx : x ∈ closedFibre (A := A) X) {W : X.Opens} (hxW : x ∈ W)
    (n : ℕ) : resF (fibreQuot A X n) (le_top : W ≤ ⊤) (fibreOne A X n) ≠ 0 := by
  intro h0
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  replace hVW : V ≤ W := hVW
  have h1 : (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n).app V
      (resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))) = 0 := by
    have e1 := resF_app (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n) (le_top : V ≤ ⊤)
      (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))
    have e2 := resF_resF (fibreQuot A X n) (le_top : W ≤ ⊤) hVW (fibreOne A X n)
    rw [h0, map_zero] at e2
    exact e1.symm.trans e2.symm
  rw [quotPowπ_app_eq_zero_iff _ _ hV] at h1
  have h2 : (1 : Γ(X, V)) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) := by
    have e : resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤))) =
        (show Γ(𝟙_ X.Modules, V) from (1 : Γ(X, V))) := map_one (restrictTop V)
    rw [e] at h1
    refine Submodule.smul_induction_on (p := fun y : Γ(𝟙_ X.Modules, V) =>
      (show Γ(X, V) from y) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1))) h1
      (fun a ha m _ => ?_) (fun x y hx hy => Ideal.add_mem _ hx hy)
    exact Ideal.mul_mem_right _ _ ha
  have hle : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) ≤
      (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V x hxV).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    have ha' : a ∈ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
    intro hu
    apply not_mem_basicOpen_of_mem_closedFibre hx ha'
    have hb : x ∈ X.basicOpen (toFunctions V a) := (X.mem_basicOpen (toFunctions V a) x hxV).2 hu
    change x ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (algebraMap A Γ(X, ⊤) a)) at hb
    rw [X.basicOpen_res] at hb
    exact hb.2
  have h3 := hle h2
  rw [Ideal.mem_comap, map_one] at h3
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h3)

end

end GroundTheory.Arith.SchemeCoh
end
