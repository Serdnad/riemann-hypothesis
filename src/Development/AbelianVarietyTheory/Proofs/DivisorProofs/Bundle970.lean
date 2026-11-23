module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle944
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle945
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle946
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerExpJointHarmPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Formalism.BranchSandwichDivisors.StatementR
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem homLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  intro R R₀ _ _ I hI π _ _ B B₀ _ _ _ _ p hs _ _ B' B₀' _ _ _ _ p' hs' hp' hker' _ φ
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  letI : Algebra R B₀' := ((algebraMap R₀ B₀').comp π).toAlgebra
  let P : B →ₐ[R] B₀' := { (φ : B₀ →+* B₀').comp p with
    commutes' := fun r ↦ by
      show φ (p (algebraMap R B r)) = algebraMap R₀ B₀' (π r)
      rw [hs.map_algebraMap r]
      exact φ.commutes (π r) }
  let P' : B' →ₐ[R] B₀' := { p' with commutes' := fun r ↦ hs'.map_algebraMap r }
  have hn := LocalIsomorphism.nil I P' hker' (map_sq hI B')
  exact ⟨Algebra.FormallySmooth.liftOfSurjective P P' hp' hn,
    fun b ↦ Algebra.FormallySmooth.liftOfSurjective_apply P P' hp' hn b⟩

end GlobalTheory.Obs
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCupProduct_graded_comm : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.cup_comm
  | exact GlobalTheory.EtC.cup_comm
  | (intros; apply GlobalTheory.EtC.cup_comm <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  first
  | exact @GlobalTheory.EtC.CupGen.main
  | exact GlobalTheory.EtC.CupGen.main
  | (intros; apply GlobalTheory.EtC.CupGen.main <;> assumption)
end

section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  apply _root_.FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le <;> assumption

theorem fil_properties : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J), fil δ 0 = ⊤ ∧ fil δ 1 = J ∧ (∀ m n, m ≤ n → fil δ n ≤ fil δ m) ∧ (∀ m n, fil δ m * fil δ n ≤ fil δ (m + n)) ∧ (∀ n, ∀ x ∈ J, δ.dpow n x ∈ fil δ n) ∧ (IsNilDP δ ↔ ∃ N, IsLev δ N) ∧ ∀ (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → ∀ N, (fil δ N).map f ≤ fil δ' N := by
  intro B _ J δ
  refine ⟨fil_zero_eq_top δ, fil_one_eq δ, fun m n h ↦ GlobalTheory.Cris.ExpBij.dpFil_anti δ h, fun m n ↦ ?_,
    fun n x hx ↦ GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hx n, isDPNilpotent_iff_exists_isLevel δ,
    fun C _ J' δ' f hf N ↦ map_fil_le δ δ' f hf N⟩
  rw [Ideal.mul_le]
  exact fun a ha b hb ↦ GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ha hb

end GlobalTheory.PDA
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerSplittingDifference_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  first | (exact @GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (exact GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (intros; apply GlobalTheory.EtC.kumDiff_mul_rootOfUnity <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.DualPull

variable {X Y : Scheme.{0}}

abbrev cutO (T W : Y.Opens) : Y.Opens := T.ι ''ᵁ T.ι ⁻¹ᵁ W

theorem cutO_le (T W : Y.Opens) : cutO T W ≤ W := T.ι.image_preimage_le W

theorem cutO_le' (T W : Y.Opens) : cutO T W ≤ T := T.ι_image_le _

theorem le_cutO {T W S : Y.Opens} (h : S ≤ T) (h' : S ≤ W) : S ≤ cutO T W := by
  rw [cutO, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h h'

theorem cutO_mono (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) : cutO T W' ≤ cutO T W :=
  le_cutO (cutO_le' _ _) ((cutO_le _ _).trans h)

def cut (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj ((structureModule Y).restrict T.ι)

def cutEquiv (T W : Y.Opens) : Γ(cut T, W) ≃+ Γ(Y, cutO T W) := AddEquiv.refl _

theorem cutEquiv_smul (T W : Y.Opens) (a : Γ(Y, W)) (s : Γ(cut T, W)) :
    cutEquiv T W (a • s) = resG Y (cutO_le T W) a * cutEquiv T W s :=
  congrArg (· * cutEquiv T W s) congr($(T.ι.app_appIso_inv W) a)

theorem cutEquiv_res (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(cut T, W)) :
    cutEquiv T W' (resM (cut T) h s) = resG Y (cutO_mono T h) (cutEquiv T W s) := rfl

variable {P : Y.Modules} {T : Y.Opens}

def toCut (l : Γ(dual P, T)) : P ⟶ cut T :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv T W).symm (dualApp l (cutO_le' T W) (resM P (cutO_le T W) s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := (cutEquiv T W).injective (by
        rw [RingHom.id_apply, cutEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul]) })
    fun {W W'} h s => (cutEquiv T W').injective (by
      change dualApp l _ (resM P _ (resM P h s)) = resG Y (cutO_mono T h) (dualApp l _ (resM P _ s))
      rw [← dualApp_resM, resM_resM, resM_resM])

theorem toCut_app (l : Γ(dual P, T)) (W : Y.Opens) (s : Γ(P, W)) :
    cutEquiv T W ((toCut l).app W s) = dualApp l (cutO_le' T W) (resM P (cutO_le T W) s) := rfl

theorem toCut_injective {l l' : Γ(dual P, T)} (h : toCut l = toCut l') : l = l' :=
  dual_ext fun W hW s => by
    have := congrArg (resG Y (le_cutO hW le_rfl)) ((toCut_app l W s).symm.trans (h ▸ toCut_app l' W s))
    rwa [← dualApp_resM, ← dualApp_resM, resM_resM, resM_self] at this

def ofCut (φ : P ⟶ cut T) : Γ(dual P, T) :=
  dualMk (fun W h =>
    { toFun s := resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutEquiv_smul, map_mul, resG_resG, resG_self]; rfl })
    fun W W' h h' s => by
      change resG Y _ (cutEquiv T W' (φ.app W' (resM P h' s))) = resG Y h' (resG Y _ _)
      rw [app_resM, cutEquiv_res, resG_resG, resG_resG]

theorem dualApp_ofCut (φ : P ⟶ cut T) {W : Y.Opens} (h : W ≤ T) (s : Γ(P, W)) :
    dualApp (ofCut φ) h s = resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s)) := rfl

variable (f : Y ⟶ X)

def adj {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (Scheme.Modules.pullback f).obj F ⟶ G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).symm ψ

theorem adj_app {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G)
    {V : X.Opens} (e : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) :
    (adj f ψ).app T (pullbackSections f F e s) = resM G e (ψ.app V s) := by
  refine (QCoh.hom_app_res (adj f ψ) e _).trans (congrArg (resM G e) ?_)
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at this
  exact congr(($this).app V s)

theorem pull_ext {F : X.Modules} {G : Y.Modules} {φ φ' : (Scheme.Modules.pullback f).obj F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s) =
      φ'.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s)) : φ = φ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have e : pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s = _ := QCoh.res_self _ _ _
  exact (congrArg (φ.app _) e).symm.trans ((h V s).trans (congrArg (φ'.app _) e))

variable {F G : X.Modules} {V : X.Opens}

theorem dual_pull_ext (e : T ≤ f ⁻¹ᵁ V) {l l' : Γ(dual ((Scheme.Modules.pullback f).obj F), T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      dualApp l hS (pullbackSections f F e' s) = dualApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCut_injective (pull_ext f fun W s => (cutEquiv T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCut_app, toCut_app, this]
  exact h _ inf_le_right _ _ _ _

theorem cutO_le_inf (V W : X.Opens) : cutO (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
  le_inf (cutO_le (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)) (cutO_le' (f ⁻¹ᵁ V) (f ⁻¹ᵁ W))

theorem appLE_resG {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) :
    f.appLE W T e (resG X h a) = f.appLE V T (e.trans (f.preimage_mono h)) a :=
  congr($(f.map_appLE e (homOfLE h).op) a)

theorem resG_appLE {S : Y.Opens} (h : S ≤ T) (e : T ≤ f ⁻¹ᵁ V) (a : Γ(X, V)) :
    resG Y h (f.appLE V T e a) = f.appLE V S (h.trans e) a :=
  congr($(f.appLE_map e (homOfLE h).op) a)

def formPush (l : Γ(dual F, V)) : F ⟶ (Scheme.Modules.pushforward f).obj (cut (f ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).symm (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
        (dualApp l inf_le_right (resM F inf_le_left s)))
      map_add' s t := by simp only [map_add (f := _)]; rfl
      map_smul' a s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutEquiv_smul _ _ (f.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul, map_mul, appLE_resG]
        rfl) })
    fun {W W'} h s => (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W')).injective (by
      change f.appLE (W' ⊓ V) _ _ (dualApp l _ (resM F _ (resM F h s))) =
        resG Y (cutO_mono _ (f.preimage_mono h)) (f.appLE (W ⊓ V) _ _ (dualApp l _ (resM F _ s)))
      rw [resG_appLE, ← appLE_resG f (inf_le_inf_right V h) (cutO_le_inf f V W'), ← dualApp_resM,
        resM_resM, resM_resM])

def pullForm (l : Γ(dual F, V)) : Γ(dual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) :=
  ofCut (adj f (formPush f l))

theorem dualApp_pullForm (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (hT : T ≤ f ⁻¹ᵁ V)
    (e : T ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp (pullForm f l) hT (pullbackSections f F e s) = f.appLE W T e (dualApp l h s) := by
  rw [pullForm, dualApp_ofCut, adj_app]
  change resG Y _ (resG Y (cutO_mono _ e) (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
    (dualApp l inf_le_right (resM F inf_le_left s)))) = _
  rw [resG_appLE, resG_appLE, dualApp_resM l h, appLE_resG]


variable (F) in
def pullFormHom :
    dual F ⟶ (Scheme.Modules.pushforward f).obj (dual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLinear (fun V =>
    { toFun l := pullForm f l
      map_add' l l' := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = dualApp (pullForm f l) hS _ + dualApp (pullForm f l') hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_add,
          LinearMap.add_apply, map_add]
      map_smul' a l := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = resG Y hS (f.app V a) * dualApp (pullForm f l) hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_smul,
          LinearMap.smul_apply, smul_eq_mul, map_mul, appLE_resG]
        rfl })
    fun {V V'} hV l => dual_pull_ext f le_rfl fun W h S hS e s => by
      change dualApp (pullForm f (resM _ hV l)) hS _ =
        dualApp (pullForm f l) (hS.trans (f.preimage_mono hV)) _
      rw [dualApp_pullForm f _ h, dualApp_pullForm f _ (h.trans hV), dualApp_res]


variable (F) in
def theta : (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F) :=
  adj f (pullFormHom f F)

theorem dualApp_theta (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ V)
    {S : Y.Opens} (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp ((theta f F).app T (pullbackSections f (dual F) e l)) hS (pullbackSections f F e' s) =
      f.appLE W S e' (dualApp l h s) := by
  rw [theta, adj_app]
  exact dualApp_pullForm f l h (hS.trans e) e' s

theorem isIso_theta {r : ℕ} (h : IsVB F r) : IsIso (theta f F) := by
  have := h.isQuasicoherent
  have := h.dual.isQuasicoherent
  refine isIso_of_frames (ι := Fin r) _ fun y => ?_
  obtain ⟨U, e, hx, he⟩ := h (f y)
  refine ⟨f ⁻¹ᵁ U, _, hx, he.dual.pullback f, ?_⟩
  have H (i : Fin r) : (theta f F).app _ (pullbackSections f (dual F) (le_refl (f ⁻¹ᵁ U))
      (he.coord i)) = (he.pullback f).coord i :=
    dual_pull_ext f le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact (he.pullback_basis_repr f hW e' s i).symm
  rw [funext H]
  exact (he.pullback f).dual

end GlobalTheory.DualPull
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  first | exact @GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | exact GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | (intros; apply GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → ∃ (Q : PDivGroup p k) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) • 𝟙 G ∧ q' ≫ q = (p : ℤ_[p]) • 𝟙 Q ∧ kerIdeal (q.app 1) = RingHom.ker π := by
  first | exact @GlobalTheory.HTPair.exists_quot_field | exact GlobalTheory.HTPair.exists_quot_field | (intros; apply GlobalTheory.HTPair.exists_quot_field <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime → OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  first | exact @GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | exact GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | (intros; apply GlobalTheory.HilbFam.LatticeUp.exists_mul_integral <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

theorem _root_.GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M → (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  first | exact @GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | exact GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | (intros; apply GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockHarmonics_graded_compactStable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)), (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) → (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧ KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧ KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧ ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  first | exact @GlobalTheory.FockAlg.harm_graded_stable | exact GlobalTheory.FockAlg.harm_graded_stable | (intros; apply GlobalTheory.FockAlg.harm_graded_stable <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.inner_expt_jointHarm_real_pos : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Y ∈ pR p q, ∀ P ∈ jointHarm p q r s, P ≠ 0 → (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).im = 0 ∧ 0 < (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).re := by
  first | exact @GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos | exact GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos | (intros; apply GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos <;> assumption)
end
