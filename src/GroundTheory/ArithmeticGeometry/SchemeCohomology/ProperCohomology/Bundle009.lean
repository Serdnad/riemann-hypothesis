module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionCech
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SheafHEquiv
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle002
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle006
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle008
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle007
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerrePAux
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

section Top

variable {X : TopCat.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → Opens X)

def HAcyclicOn (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ {n : ℕ} (i : Fin (n + 1) → ι) (q : ℕ), Subsingleton (G.H' (q + 1) (inter U i))

variable {U}

lemma surjective_app_of_subsingleton_H'
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (V : Opens X) [Subsingleton (S.X₁.H' 1 V)] : Function.Surjective (S.g.hom.app (op V)) := by
  intro y
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    ((H'.equiv₀ S.X₃ V).symm y) rfl (Subsingleton.elim (α := S.X₁.H' 1 V) _ _)
  have key : H'.equiv₀ S.X₃ V (x.comp (Ext.mk₀ S.g) (add_zero 0)) =
      S.g.hom.app (op V) (H'.equiv₀ S.X₂ V x) := H'.equiv₀_naturality S.g V x
  exact ⟨H'.equiv₀ S.X₂ V x, by rw [← key, hx, AddEquiv.apply_symm_apply]⟩

lemma subsingleton_H'_of_injective
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    [Injective S.X₂] (V : Opens X) (q : ℕ) [Subsingleton (S.X₁.H' (q + 2) V)] :
    Subsingleton (S.X₃.H' (q + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    y rfl (Subsingleton.elim (α := S.X₁.H' (q + 2) V) _ _)
  have : Subsingleton (S.X₂.H' (q + 1) V) := H'.subsingleton_of_injective S.X₂ q V
  have hx0 : x = 0 := Subsingleton.elim (α := S.X₂.H' (q + 1) V) _ _
  rw [← hx, hx0, Ext.zero_comp]
  rfl

variable (U)

lemma injectiveSequence_isCechShortExact_of_acyclic
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    IsCechShortExact U (injectiveSequence G).f.hom (injectiveSequence G).g.hom :=
  isCechShortExact_of_surjective (injectiveSequence_shortExact G) U fun i =>
    have : Subsingleton ((injectiveSequence G).X₁.H' 1 (inter U i)) := hG i 0
    surjective_app_of_subsingleton_H'.{w'} (injectiveSequence_shortExact G) _

lemma injectiveSequence_hAcyclicOn
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    HAcyclicOn.{w, w'} U (injectiveSequence G).X₃ := fun i q =>
  have : Subsingleton ((injectiveSequence G).X₁.H' (q + 2) (inter U i)) := hG i (q + 1)
  have : Injective (injectiveSequence G).X₂ := inferInstanceAs (Injective (Injective.under G))
  subsingleton_H'_of_injective (injectiveSequence_shortExact G) _ q

variable (hU : iSup U = ⊤)

def cechHEquivOfAcyclic : ∀ (n : ℕ) (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
    HAcyclicOn.{w, w'} U G → (cechH G.obj U n ≃+ Sheaf.H.{w'} G n)
  | 0, G, _ => cechHZeroEquivH G U hU
  | 1, G, hG => cechHOneEquiv (S := injectiveSequence G) U hU (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U)
  | m + 2, G, hG => cechHEquivStep (S := injectiveSequence G) U (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U) m
      (cechHEquivOfAcyclic (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))

theorem cechHEquivOfAcyclic_naturality : ∀ (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hG : HAcyclicOn.{w, w'} U G) (hG' : HAcyclicOn.{w, w'} U G') (φ : G ⟶ G')
    (x : cechH G.obj U n),
    cechHEquivOfAcyclic U hU n G' hG' (cechHMap U φ.hom n x) =
      Sheaf.H.map.{w'} φ n (cechHEquivOfAcyclic U hU n G hG x)
  | 0, _, _, _, _, φ, x => cechHZeroEquivH_naturality U φ hU x
  | 1, G, G', hG, hG', φ, x =>
      cechHOneEquiv_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U hU
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) x
  | m + 2, G, G', hG, hG', φ, x =>
      cechHEquivStep_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) m
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G' hG'))
        (fun y => cechHEquivOfAcyclic_naturality (m + 1) (injectiveSequence_hAcyclicOn U G hG)
          (injectiveSequence_hAcyclicOn U G' hG') (injectiveSequenceMap φ).τ₃ y) x

end Top

section Scheme

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → X.Opens) (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechHLinearEquivHOfAcyclic (hU : iSup U = ⊤) (F : X.Modules)
    (hF : HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F)) (n : ℕ) :
    cechH (modulesAb F).obj U n ≃ₗ[A] Sheaf.H.{w'} (modulesAb F) n :=
  (cechHEquivOfAcyclic (X := X.toTopCat) U hU n (modulesAb F) hF).toLinearEquiv fun a x =>
    cechHEquivOfAcyclic_naturality (X := X.toTopCat) U hU n hF hF
      (modulesAbMap (smulHom F (algebraMap A Γ(X, ⊤) a))) x

variable [∀ V : X.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]

lemma hAcyclicOn_of_restrict (F : X.Modules)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict (⨅ a, U (i a)).ι)) (q + 1))) :
    HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F) := fun {n} i q => by
  have := h n i q
  rw [inter_eq_iInf]
  exact subsingleton_H'_of_restrict.{w'} (⨅ a, U (i a)) F (q + 1)

end Scheme

section Pushforward

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) (A : Type u) [CommRing A] [X.Over (Spec (.of A))]
  [X'.Over (Spec (.of A))] [ψ.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
  [∀ V : X'.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X'.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X'.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (V : ι → X.Opens) (hV : iSup V = ⊤)
  (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, V (i a)))

attribute [local instance] algebraOfOver

def HLinearEquivPushforwardOfAcyclic (G : X'.Modules)
    [((Scheme.Modules.pushforward ψ).obj G).IsQuasicoherent]
    (hG : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (G.restrict (ψ ⁻¹ᵁ ⨅ a, V (i a)).ι)) (q + 1)))
    (p : ℕ) :
    Sheaf.H.{w'} (modulesAb G) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward ψ).obj G)) p :=
  have hV' : iSup (fun j => ψ ⁻¹ᵁ V j) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]
    rfl
  have hG' : HAcyclicOn.{w, w'} (X := X'.toTopCat) (fun j => ψ ⁻¹ᵁ V j) (modulesAb G) :=
    hAcyclicOn_of_restrict _ G fun n i q => by
      have e := preimage_inter ψ V i
      rw [inter_eq_iInf, inter_eq_iInf] at e
      have h1 := hG n i q
      rw [e] at h1
      exact h1
  (cechHLinearEquivHOfAcyclic (fun j => ψ ⁻¹ᵁ V j) A hV' G hG' p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv ψ A G V p).symm ≪≫ₗ cechHLinearEquivH V hV hVaff A _ p

end Pushforward

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

lemma injective_app_of_mono {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (U : X.Opens) : Function.Injective (φ.app U) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have h := (NatTrans.mono_iff_mono_app _).1 this (op U)
  exact (AddCommGrpCat.mono_iff_injective _).1 h

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} [X.Over (Spec (.of A))]
  (F : X.Modules)

abbrev reesTarget : (reesScheme I X).Modules :=
  (Scheme.Modules.pushforward (reesPolyMap I X)).obj
    ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F))

abbrev reesUnit : (Scheme.Modules.pullback (reesPr I X)).obj F ⟶ reesTarget I F :=
  (Scheme.Modules.pullbackPushforwardAdjunction (reesPolyMap I X)).unit.app _

def reesSheaf : (reesScheme I X).Modules := Abelian.coimage (reesUnit I F)

def reesSheafπ : (Scheme.Modules.pullback (reesPr I X)).obj F ⟶ reesSheaf I F :=
  Abelian.coimage.π (reesUnit I F)

def reesSheafι : reesSheaf I F ⟶ reesTarget I F := Abelian.factorThruCoimage (reesUnit I F)

instance : Mono (reesSheafι I F) := (coimCokSC_shortExact (reesUnit I F)).mono_f

lemma reesSheafπ_ι : reesSheafπ I F ≫ reesSheafι I F = reesUnit I F :=
  Abelian.coimage.fac (reesUnit I F)

variable {I F}

lemma isCoherent_pullback_reesPr (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pullback (reesPr I X)).obj F) :=
  isCoherent_pullback _ hF

lemma isQuasicoherent_reesTarget (hF : IsCoherent F) : (reesTarget I F).IsQuasicoherent := by
  have := (isCoherent_pullback (reesPolyMap I X) (isCoherent_pullback_reesPr hF)).1
  exact isQuasicoherent_pushforward_of_isAffineHom _ _

theorem isCoherent_reesSheaf (hF : IsCoherent F) : IsCoherent (reesSheaf I F) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  have := isQuasicoherent_reesTarget (I := I) hF
  exact isCoherent_cokernel (kernel.ι (reesUnit I F)) (isCoherent_pullback_reesPr hF)

lemma surjective_reesSheafπ_app (hF : IsCoherent F) {W : (reesScheme I X).Opens}
    (hW : IsAffineOpen W) : Function.Surjective ((reesSheafπ I F).app W) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  have := isQuasicoherent_reesTarget (I := I) hF
  exact surjective_cokernel_π_app (kernel.ι (reesUnit I F)) hW

lemma injective_reesSheafι_app (W : (reesScheme I X).Opens) :
    Function.Injective ((reesSheafι I F).app W) :=
  injective_app_of_mono _ W

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

theorem exists_chow' {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      genericPoint X ∈ U ∧ IsIso (π ∣_ U) := by
  obtain ⟨k, n, X', q, π, U, hq, hqπ, hU, hπ⟩ := exists_chow_multiProj (A := A) X
  refine ⟨ProjSpace.multiProjDim k n, X', q ≫ ProjSpace.multiProjEmb A k n, π, U,
    inferInstance, ?_, hU, hπ⟩
  rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, hqπ]

theorem exists_chow {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  obtain ⟨N, X', i, π, U, hi, hiπ, hU, hπ⟩ := exists_chow' (A := A) X
  exact ⟨N, X', i, π, U, hi, hiπ, ⟨_, hU⟩, hπ⟩

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

private noncomputable def H.linearMapV436 {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{c236Ext} (modulesAb F) n →ₗ[A] Sheaf.H.{c236Ext} (modulesAb G) n where
  toFun := Sheaf.H.map.{c236Ext} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{c236Ext} (modulesAbMap φ) n (a • x) =
      a • Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x
    rw [H.smul_def, H.smul_def, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]

private lemma H.linearMapV436_apply {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H.{c236Ext} (modulesAb F) n) :
    H.linearMapV436 A φ n x = Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x := rfl

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

abbrev formalα (n : ℕ) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb F) q :=
  H.linearMap A (idealPowι I F (n + 1)) q

def formalK (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb F) q) :=
  LinearMap.range (formalα I F q n)

omit [IsNoetherianRing A] in
private lemma H.range_linearMap_le_of_comp {F₁ F₂ F₃ : X.Modules}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (h : F₁ ⟶ F₃) (hf : f ≫ g = h) :
    LinearMap.range (H.linearMap.{u} A h q) ≤ LinearMap.range (H.linearMap.{u} A g q) := by
  rw [← hf, H.linearMap_comp.{u} A f g q]
  exact LinearMap.range_comp_le_range (H.linearMap.{u} A f q) (H.linearMap.{u} A g q)

lemma formalK_antitone : Antitone (formalK I F q) :=
  antitone_nat_of_succ_le fun n =>
    H.range_linearMap_le_of_comp (q := q) (idealPowSucc I F (n + 1))
      (idealPowι I F (n + 1)) (idealPowι I F (n + 1 + 1)) (idealPowSucc_ι I F (n + 1))

abbrev formalβ (n : ℕ) : Sheaf.H.{u} (modulesAb F) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowπ I F n) q

abbrev formalτE (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowMap I F n) q

lemma shortExact_abSC_quotPow (n : ℕ) : (abSC (quotPowSC I F n)).ShortExact :=
  shortExact_abSC (quotPowSC_shortExact I F n)

lemma ker_formalβ (n : ℕ) : LinearMap.ker (formalβ I F q n) = formalK I F q n := by
  refine (LinearMap.exact_iff (f := formalα I F q n) (g := formalβ I F q n)).mp ?_
  refine fun y => ⟨H.exact₂ (n := q) (shortExact_abSC_quotPow I F n) y, ?_⟩
  rintro ⟨x, rfl⟩
  exact H.map_g_map_f (S := abSC (quotPowSC I F n)) (n := q) x

abbrev formalδ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1) :=
  H.δLinear A (shortExact_abSC_quotPow I F n) q

def formalQ (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) :=
  LinearMap.range (formalδ I F q n)

def formalι (n : ℕ) : (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  (formalK I F q n).liftQ (formalβ I F q n) (ker_formalβ I F q n).ge

lemma formalι_injective (n : ℕ) : Function.Injective (formalι I F q n) :=
  LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' (formalK I F q n) (formalβ I F q n) (ker_formalβ I F q n).symm)

def formalπ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A] formalQ I F q n :=
  (formalδ I F q n).rangeRestrict

private lemma range_liftQ_eq_ker_of_exact {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (K : Submodule R M) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : K ≤ LinearMap.ker f)
    (hex : Function.Exact f g) :
    LinearMap.range (K.liftQ f h) = LinearMap.ker g.rangeRestrict :=
  (Submodule.range_liftQ K f h).trans
    ((LinearMap.exact_iff.mp hex).symm.trans (LinearMap.ker_rangeRestrict g).symm)

lemma range_formalι (n : ℕ) :
    LinearMap.range (formalι I F q n) = LinearMap.ker (formalπ I F q n) := by
  refine range_liftQ_eq_ker_of_exact (formalK I F q n) (formalβ I F q n) (formalδ I F q n)
    (ker_formalβ I F q n).ge ?_
  let hS := shortExact_abSC_quotPow I F n
  refine fun y => ⟨H.exact₃ (n₀ := q) (n₁ := q + 1) hS rfl y, ?_⟩
  rintro ⟨x, rfl⟩
  exact H.δ_map_g (n₀ := q) (n₁ := q + 1) hS rfl x

def abSCHom {S S' : ShortComplex X.Modules} (φ : S ⟶ S') : abSC S ⟶ abSC S' where
  τ₁ := modulesAbMap φ.τ₁
  τ₂ := modulesAbMap φ.τ₂
  τ₃ := modulesAbMap φ.τ₃
  comm₁₂ := by
    change modulesAbMap φ.τ₁ ≫ modulesAbMap S'.f = modulesAbMap S.f ≫ modulesAbMap φ.τ₂
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₁₂]
  comm₂₃ := by
    change modulesAbMap φ.τ₂ ≫ modulesAbMap S'.g = modulesAbMap S.g ≫ modulesAbMap φ.τ₃
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₂₃]

def quotPowSCMap (n : ℕ) : quotPowSC I F (n + 1) ⟶ quotPowSC I F n where
  τ₁ := idealPowSucc I F (n + 1)
  τ₂ := 𝟙 F
  τ₃ := quotPowMap I F n
  comm₁₂ := by
    change idealPowSucc I F (n + 1) ≫ idealPowι I F (n + 1) = idealPowι I F (n + 2) ≫ 𝟙 F
    rw [idealPowSucc_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 F ≫ quotPowπ I F n = quotPowπ I F (n + 1) ≫ quotPowMap I F n
    rw [quotPowπ_map, Category.id_comp]

lemma formalδ_naturality (n : ℕ) (x : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q) :
    formalδ I F q n (formalτE I F q n x) =
      H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) (formalδ I F q (n + 1) x) :=
  H.δ_naturality (X := X.toTopCat)
    (shortExact_abSC_quotPow I F (n + 1)) (shortExact_abSC_quotPow I F n)
    (abSCHom (quotPowSCMap I F n)) q (q + 1) rfl x

end

end GroundTheory.Arith.SchemeCoh
end
