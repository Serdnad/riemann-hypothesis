module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle011
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle009
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle007
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ExistsGeneratingSectionsTwist
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle002
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerrePAux
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

theorem IsCoherent.of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (hM : IsCoherent M) :
    IsCoherent N := by
  obtain ⟨hq, hf⟩ := hM
  refine ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, fun U hU => ?_⟩
  have := hf U hU
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := e.hom.app U
      map_add' := map_add _
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul e.hom r m }
  refine Module.Finite.of_surjective φ fun n => ⟨e.inv.app U n, ?_⟩
  change (e.inv ≫ e.hom).app U n = n
  rw [e.inv_hom_id]
  rfl

theorem IsCoherent.restrict {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] {G : X.Modules}
    (hG : IsCoherent G) : IsCoherent (G.restrict f) :=
  IsCoherent.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app G).symm
    (isCoherent_pullback f hG)

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev overBase {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  letI := baseAlgebra A hV
  ⟨embed i ψ h hV ≫ pullback.snd _ _⟩

def embedProj {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme ⟶ projectiveSpace Γ(X, V) N :=
  letI := baseAlgebra A hV
  embed i ψ h hV ≫ (ProjSpace.isPullback_baseChange A Γ(X, V) N).isoPullback.inv

instance isClosedImmersion_embedProj [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embedProj i ψ h hV) := by
  letI := baseAlgebra A hV
  unfold embedProj
  infer_instance

lemma embedProj_isOver {V : X.Opens} (hV : IsAffineOpen V) :
    letI := overBase i ψ h hV
    (embedProj i ψ h hV).IsOver (Spec (.of Γ(X, V))) := by
  letI := baseAlgebra A hV
  letI := overBase i ψ h hV
  refine ⟨?_⟩
  change embedProj i ψ h hV ≫ ProjSpace.toSpecBase Γ(X, V) N =
    embed i ψ h hV ≫ pullback.snd _ _
  rw [embedProj, Category.assoc, IsPullback.isoPullback_inv_snd]

lemma embedProj_baseChangeMap {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embedProj i ψ h hV ≫ ProjSpace.baseChangeMap A Γ(X, V) N = (ψ ⁻¹ᵁ V).ι ≫ i := by
  letI := baseAlgebra A hV
  rw [embedProj, Category.assoc, IsPullback.isoPullback_inv_fst, embed_fst]

def twistRestrictIso {V : X.Opens} (hV : IsAffineOpen V) (G : X'.Modules) (k : ℤ) :
    ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k ≅
      (ProjScheme.twist i G k).restrict (ψ ⁻¹ᵁ V).ι :=
  letI := baseAlgebra A hV
  (ProjSpace.twistBaseChangeIso A (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k).symm ≪≫
    eqToIso (congrArg (fun g => ProjScheme.twist g (G.restrict (ψ ⁻¹ᵁ V).ι) k)
      (embedProj_baseChangeMap i ψ h hV)) ≪≫
    restrictTwistIso (ψ ⁻¹ᵁ V).ι i G k

attribute [local instance] algebraOfOver

theorem exists_vanishing_finite [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (G : X'.Modules)
    (hG : IsCoherent G) :
    letI := overBase i ψ h hV
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) (q + 1))) ∧
      Module.Finite Γ(X, V)
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) 0) := by
  letI := overBase i ψ h hV
  haveI := embedProj_isOver i ψ h hV
  have hGr : IsCoherent (G.restrict (ψ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨q₀, hq₀⟩ := ProjScheme.exists_subsingleton_H_twist.{u} (embedProj i ψ h hV) _ hGr
  refine ⟨q₀, fun n hn => ⟨fun q => ?_, ?_⟩⟩
  · have h1 := hq₀ n hn (q + 1) (Nat.succ_pos q)
    exact (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) (q + 1)).toEquiv.subsingleton_congr.1
      h1
  · have hc : IsCoherent (ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) n) :=
      isCoherent_tensor_of_invertible hGr (ProjScheme.isInvertibleSheaf_twistingSheaf _ _)
    have h2 := ProjScheme.finite_H.{u} (embedProj i ψ h hV) _ hc 0
    exact Module.Finite.equiv (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) 0)

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

instance sectionsModuleA (A : Type u) [CommRing A] {X : Scheme.{u}} [X.Over (Spec (.of A))]
    (F : X.Modules) (V : X.Opens) : Module A Γ(F, V) :=
  Module.compHom _ (algV X V)

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V : X.Opens}

lemma sectionsModuleA_smul (a : A) (m : Γ(F, V)) : a • m = algV X V a • m := rfl


variable (A) in
def toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) : PolynomialModule A Γ(F, V) :=
  PolynomialModule.ofCoeff A q.coeff

@[simp] lemma coeff_toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) (n : ℕ) :
    (toPolyA A q).coeff n = q.coeff n := rfl

lemma toPolyA_add (q q' : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (q + q') = toPolyA A q + toPolyA A q' := rfl

lemma toPolyA_injective : Function.Injective (toPolyA A (F := F) (V := V)) := fun q q' h =>
  PolynomialModule.coeff_injective (R := Γ(X, V))
    (show q.coeff = q'.coeff from congrArg (fun p : PolynomialModule A Γ(F, V) => p.coeff) h)

lemma smul_mem_pow_smul {i j : ℕ} {c : Γ(X, V)} (hc : c ∈ (I.map (algV X V)) ^ i)
    {m : Γ(F, V)} (hm : m ∈ I ^ j • (⊤ : Submodule A Γ(F, V))) :
    c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)) := by
  rw [← Ideal.map_pow] at hc
  have hstab : ∀ (d : Γ(X, V)) {k : ℕ} {x : Γ(F, V)}, x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) →
      d • x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) := by
    intro d k x hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
    · have : d • (a • y) = a • (d • y) := by
        rw [sectionsModuleA_smul, sectionsModuleA_smul, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hy'
  refine Submodule.span_induction (p := fun c _ => c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)))
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨a, ha, rfl⟩
    rw [← sectionsModuleA_smul, pow_add, mul_smul]
    exact Submodule.smul_mem_smul ha hm
  · simp
  · intro x y _ _ hx hy
    rw [add_smul]
    exact add_mem hx hy
  · intro d x _ hx
    rw [smul_eq_mul, mul_smul]
    exact hstab d hx

lemma toPolyA_smul_mem {p : Polynomial Γ(X, V)} (hp : p ∈ reesCoeffRing I X V)
    {q : PolynomialModule Γ(X, V) Γ(F, V)} (hq : toPolyA A q ∈ reesSubmodule I Γ(F, V)) :
    toPolyA A (p • q) ∈ reesSubmodule I Γ(F, V) := by
  intro n
  rw [coeff_toPolyA, PolynomialModule.smul_apply]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [← hx]
  exact smul_mem_pow_smul (hp x.1) (hq x.2)

lemma toPolyA_map_smul (r : reesAlgebra I) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (((r : Polynomial A).map (algV X V)) • q) = r • toPolyA A q := by
  apply PolynomialModule.coeff_injective
  ext n
  change (((r : Polynomial A).map (algV X V)) • q).coeff n =
    ((r : Polynomial A) • toPolyA A q).coeff n
  rw [PolynomialModule.smul_apply, PolynomialModule.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_map, coeff_toPolyA]
  rfl

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

def targetToPolySec (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) : polySec I F V := z

lemma targetToPolySec_add (z z' : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (z + z') = targetToPolySec z + targetToPolySec z' := rfl

lemma targetToPolySec_injective :
    Function.Injective (targetToPolySec (I := I) (F := F) (V := V)) := fun _ _ h => h

lemma targetToPolySec_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (s • z) = (reesPolyMap I X).app _ s • targetToPolySec z := rfl

lemma targetToPolySec_ι_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec ((reesSheafι I F).app _ ((reesSheafπ I F).app _ y)) = unitB I F V y := by
  have h := congrArg (fun f => (Scheme.Modules.Hom.app f (reesPr I X ⁻¹ᵁ V)) y) (reesSheafπ_ι I F)
  exact h


variable (I) in
def reesSectionsMap (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) : PolynomialModule A Γ(F, V) :=
  toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ x)))

lemma reesSectionsMap_add (x x' : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (x + x') = reesSectionsMap I hF hV x + reesSectionsMap I hF hV x' := by
  rw [reesSectionsMap, map_add (f := _), targetToPolySec_add, map_add (f := _), toPolyA_add]
  rfl

lemma reesSectionsMap_zero : reesSectionsMap I hF hV 0 = 0 := by
  change toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ 0))) = 0
  rw [map_zero, show targetToPolySec (0 : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) = 0 from rfl,
    map_zero]
  rfl

lemma reesSectionsMap_injective : Function.Injective (reesSectionsMap I hF hV) :=
  toPolyA_injective.comp ((thetaMap_injective hF hV).comp
    (targetToPolySec_injective.comp (injective_reesSheafι_app _)))

lemma reesSectionsMap_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV ((reesSheafπ I F).app _ y) = toPolyA A (theta₁ hF hV y) := by
  rw [reesSectionsMap, targetToPolySec_ι_π, thetaMap_unitB]

lemma reesSectionsMap_mem (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV x ∈ reesSubmodule I Γ(F, V) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [reesSectionsMap_π]
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    rw [theta₁_unitPr]
    exact single_zero_mem_reesSubmodule I Γ(F, V) m
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    rw [map_add (f := _), toPolyA_add]
    exact add_mem hz hz'
  | smul s z _ hz =>
    rw [theta₁_smul]
    exact toPolyA_smul_mem (reesRingHom_mem hV s) hz

lemma reesSectionsMap_smul (r : reesAlgebra I) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (reesInr I V r • x) = r • reesSectionsMap I hF hV x := by
  rw [reesSectionsMap, Scheme.Modules.Hom.app_smul, targetToPolySec_smul, thetaMap_smul,
    ← RingHom.comp_apply, ← reesRingHom, reesRingHom_inr, toPolyA_map_smul]
  rfl

lemma reesSectionsMap_surjective (p : reesSubmodule I Γ(F, V)) :
    ∃ x, reesSectionsMap I hF hV x = p := by
  obtain ⟨p, hp⟩ := p
  rw [reesSubmodule_eq_span] at hp
  change ∃ x, reesSectionsMap I hF hV x = p
  refine Submodule.span_induction (p := fun z _ => ∃ x, reesSectionsMap I hF hV x = z)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨m, rfl⟩
    refine ⟨(reesSheafπ I F).app _ (unitPr I F V m), ?_⟩
    rw [reesSectionsMap_π, theta₁_unitPr]
    rfl
  · exact ⟨0, reesSectionsMap_zero hF hV⟩
  · rintro z z' _ _ ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [reesSectionsMap_add, hx, hx']⟩
  · rintro r z _ ⟨x, hx⟩
    exact ⟨reesInr I V r • x, by rw [reesSectionsMap_smul, hx]⟩


variable (I) in
def reesSectionsEquiv : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) ≃+ reesSubmodule I Γ(F, V) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨reesSectionsMap I hF hV x, reesSectionsMap_mem hF hV x⟩
       map_zero' := Subtype.ext (reesSectionsMap_zero hF hV)
       map_add' := fun x x' => Subtype.ext (reesSectionsMap_add hF hV x x') } :
      Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ reesSubmodule I Γ(F, V))
    ⟨fun x x' h => reesSectionsMap_injective hF hV (congrArg Subtype.val h), fun p => by
      obtain ⟨x, hx⟩ := reesSectionsMap_surjective hF hV p
      exact ⟨x, Subtype.ext hx⟩⟩

lemma reesSectionsEquiv_apply (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) = reesSectionsMap I hF hV x := rfl

end

end GroundTheory.Arith.SchemeCoh
end
