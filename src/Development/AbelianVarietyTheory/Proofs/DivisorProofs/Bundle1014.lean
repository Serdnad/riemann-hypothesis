module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimIdeal

variable {R : Type} [CommRing R] (I : Ideal R)

section Lin

variable (B : Type) [CommRing B] [Algebra R B]

def iota : I ⊗[R] B →ₗ[R] TrivSqZeroExt R I ⊗[R] B := (TrivSqZeroExt.inrHom R I).rTensor B

def tau : I ⊗[R] B →ₗ[R] B := TensorProduct.lid R B ∘ₗ I.subtype.rTensor B

def sig : TrivSqZeroExt R I ⊗[R] B →ₗ[R] B := tau I B ∘ₗ (TrivSqZeroExt.sndHom R I).rTensor B

theorem tau_tmul (i : I) (b : B) : tau I B (i ⊗ₜ b) = (i : R) • b := by
  simp [tau]

theorem sig_iota (y : I ⊗[R] B) : sig I B (iota I B y) = tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [sig, iota]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tau_mem (y : I ⊗[R] B) : tau I B y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b =>
    rw [tau_tmul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
  | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy

theorem sig_mem (x : TrivSqZeroExt R I ⊗[R] B) : sig I B x ∈ I.map (algebraMap R B) := tau_mem I B _

theorem tau_mulLeft (b : B) (y : I ⊗[R] B) : tau I B ((LinearMap.mulLeft R b).lTensor I y) = b • tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i c => simp [tau_tmul, Algebra.smul_def]; ring
  | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]

theorem exists_tau {x : B} (hx : x ∈ I.map (algebraMap R B)) : ∃ y, tau I B y = x := by
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨⟨i, hi⟩ ⊗ₜ 1, by simp [tau_tmul, Algebra.smul_def]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, rfl⟩ := hx; obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩
  | smul b x _ hx =>
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(LinearMap.mulLeft R b).lTensor I y, tau_mulLeft I B b y⟩

theorem tau_injective (hB : Module.Flat R B) : Function.Injective (tau I B) :=
  (TensorProduct.lid R B).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective)

variable {B} {B' : Type} [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')

theorem iota_nat (y : I ⊗[R] B) :
    extHom (TrivSqZeroExt R I) φ (iota I B y) = iota I B' (φ.toLinearMap.lTensor I y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [iota]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tau_nat (y : I ⊗[R] B) : tau I B' (φ.toLinearMap.lTensor I y) = φ (tau I B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [tau_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sig_nat (x : TrivSqZeroExt R I ⊗[R] B) :
    sig I B' (extHom (TrivSqZeroExt R I) φ x) = φ (sig I B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sig, tau_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Lin

end GlobalTheory.PrimIdeal

namespace GlobalTheory.PrimIdeal

theorem primI_of_ext : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁)
    (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧
    ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R)
      (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) →
      (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F),
        (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) →
      PrimI I n₀ n₁ n₂ := by
  intro R _ I
  refine ⟨TrivSqZeroExt R I, inferInstance, inferInstance, TrivSqZeroExt.fstHom R R I, ?_, ?_⟩
  · intro y y' hy hy'
    have h1 : y.fst = 0 := hy
    have h2 : y'.fst = 0 := hy'
    ext
    · simp [h1, h2]
    · simp [h1, h2]
  intro D T _ _ F F' n₀ n₁ n₂ hF hF' hc z f hz hf hrel
  choose y hy using fun (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t'') ↦ exists_tau I (F.obj t'') (hz t t' t'' a b)
  choose y' hy' using fun (t t' : T) (a : t ⟶ t') ↦ exists_tau I (F'.obj t') (hf t t' a)
  let zh : C2 (ext (TrivSqZeroExt R I) F) := fun t t' t'' a b ↦ iota I (F.obj t'') (y t t' t'' a b)
  have hzc : zh ∈ Z2 (ext (TrivSqZeroExt R I) F) := by
    intro t t' t'' t''' φ ψ χ
    have key : (mp F χ).toLinearMap.lTensor I (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ =
        y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ := by
      apply tau_injective I (F.obj t''') (hF t''')
      simp only [map_add (f := _), AlgHom.toLinearMap_apply, tau_nat, hy]
      exact z.2 φ ψ χ
    have := congrArg (iota I _) key
    simp only [map_add (f := _), ← iota_nat] at this
    exact this
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 (hc (H2.mk _ ⟨zh, hzc⟩) (by
    show H2.mk _ ((extMap _ n₀).pullbackTwoCocycle ⟨zh, hzc⟩) =
      H2.mk _ ((extMap _ n₁).pullbackTwoCocycle ⟨zh, hzc⟩) + H2.mk _ ((extMap _ n₂).pullbackTwoCocycle ⟨zh, hzc⟩)
    rw [← LinearMap.map_add (H2.mk _), H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ iota I (F'.obj t') (y' t t' a), ?_⟩
    funext t t' t'' a b
    simp only [d1_apply, Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply, CoefMap.pullCocycleTwo_apply]
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hrel t) t') t'') a) b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply] at e
    have key : (mp F' b).toLinearMap.lTensor I (y' _ _ a) - y' _ _ (a ≫ b) + y' _ _ b =
        (coefHom n₀ t'').toLinearMap.lTensor I (y _ _ _ (n₀.G.map a) (n₀.G.map b)) -
          ((coefHom n₁ t'').toLinearMap.lTensor I (y _ _ _ (n₁.G.map a) (n₁.G.map b)) +
            (coefHom n₂ t'').toLinearMap.lTensor I (y _ _ _ (n₂.G.map a) (n₂.G.map b))) := by
      apply tau_injective I (F'.obj t'') (hF' t'')
      simp only [map_add (f := _), map_sub, AlgHom.toLinearMap_apply, tau_nat, hy, hy']
      rw [e]
      rw [sub_sub]; rfl
    have := congrArg (iota I _) key
    simp only [map_add (f := _), map_sub, ← iota_nat] at this
    exact this))
  refine ⟨fun t t' a ↦ sig I (F.obj t') (g t t' a), fun t t' a ↦ sig_mem I _ _, ?_⟩
  funext t t' t'' a b
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hg t) t') t'') a) b
  simp only [d1_apply] at e ⊢
  rw [← sig_nat, ← map_sub, ← map_add (f := _)]
  change sig I (F.obj t'') (mp (ext (TrivSqZeroExt R I) F) b (g t t' a) - g t t'' (a ≫ b) + g t' t'' b) = _
  rw [e]
  exact (sig_iota I _ _).trans (hy t t' t'' a b)

end GlobalTheory.PrimIdeal
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.GenericMember

theorem genSec_chart_ne_zero_and_isPrime : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  intro k _ N X X' _ f f' π L hL b V hne hW c hVc j hj
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  intro e he1 he2
  haveI : Nonempty V := hne.to_subtype
  set a : Fin N → Γ(X, V) := fun i => resG X hVc ((b i).f c) with ha
  set t₀ : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) :=
    ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i with ht
  obtain ⟨ht0, hI⟩ := GlobalTheory.GenericForm.span_genericForm_isPrime_or_eq_top k Γ(X, V) N a j hj t₀ rfl
  have hWU : π ⁻¹ᵁ V ≤ (L.pull π).U (fun _ => c) := fun x hx => Set.mem_iInter.2 fun _ => hVc hx
  have hsum : ∀ J, (genSec k N f' π L b).f J =
      ∑ i, resG X' le_top (genVar k N f' i) * (secPull (b i) π).f J := by
    intro J
    let F : (L.pull π).Sec →+ Γ(X', (L.pull π).U J) :=
      { toFun := fun s => s.f J, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show F (∑ i, genVar k N f' i • secPull (b i) π) = _

    rw [map_sum]
    rfl
  have key : resG X' hWU ((genSec k N f' π L b).f (fun _ => c)) = e t₀ := by

    rw [hsum (fun _ => c), map_sum, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hq : algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i =
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] (1 : Γ(X, V))) *
          ((1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] a i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hq, map_mul, he1, he2]
    congr 1
    · have e2 : f'.appTop ≫ X'.presheaf.map (homOfLE (le_top : (L.pull π).U (fun _ => c) ≤ ⊤)).op ≫
          X'.presheaf.map (homOfLE hWU).op = f'.appLE ⊤ (π ⁻¹ᵁ V) le_top := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv.hom
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))) e2
    · have e1 : π.appLE (L.U c) ((L.pull π).U (fun _ => c)) ((GlobalTheory.chartPullPull L π).le (fun _ => c)) ≫
          X'.presheaf.map (homOfLE hWU).op = X.presheaf.map (homOfLE hVc).op ≫ π.app V := by
        rw [Scheme.Hom.naturality]
        simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((b i).f c)) e1
  have hid : (secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ =
      Ideal.span {e t₀} := by
    rw [ideal_secIdeal (LB.isLB_pull hL π) _ ⟨π ⁻¹ᵁ V, hW⟩ (fun _ => c) hWU]
    exact congrArg (fun x => Ideal.span {x}) key
  have hmap : Ideal.span {e t₀} = Ideal.map e (Ideal.span {t₀}) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun h0 => ht0 (e.injective ?_), ?_⟩
  · rw [map_zero, ← key, h0, map_zero]
  · rw [hid]
    rcases hI with h | ⟨hp, hx⟩
    · left
      rw [hmap, h, Ideal.map_top]
    · right
      refine ⟨?_, ?_⟩
      · haveI := hp
        rw [hmap]
        exact Ideal.map_isPrime_of_equiv e
      · rw [eq_bot_iff]
        intro x hx'
        rw [Ideal.mem_bot]
        apply hx x
        rw [Ideal.mem_comap, ← he1, Ideal.mem_span_singleton'] at hx'
        obtain ⟨d, hd⟩ := hx'
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm d, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, hd]

end GlobalTheory.GenericMember
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_one_left_eq_zero {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0 := GlobalTheory.ThetaExtend.pic_local (R := K) _
  rw [Hom.one_def, Over.comp_left, pull_comp, h, map_zero]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem pull_pow_left (hcube : CubeSt) {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L)
    (c : Pic A.left) (ψ : A ⟶ A) (n : ℕ) :
    pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c := by
  have hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c =
      2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c := by
    intro n
    have h := hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹
    have e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1) := mul_inv_cancel_right _ _
    have e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2) := (pow_succ _ _).symm
    have e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n := by rw [pow_succ, mul_inv_cancel_right]
    have e4 : ψ * ψ⁻¹ = 1 := mul_inv_cancel _
    rw [e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero] at h
    rw [two_nsmul]
    exact h.symm
  have key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c +
      ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c =
      (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, pull_one_left_eq_zero]; simp
      · rw [pow_one]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := eq_sub_of_add_eq (hrec n)
      rw [show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]
      rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1),
        choose_two_succ n]
      push_cast
      module
  exact (key n).1

theorem separatedSt_of_const_cube : ConstSt → CubeSt → SeparatedSt := by
  intro hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu
  haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  obtain ⟨d, hd, n0, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
  have heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL)) := by
    intro φ
    rw [← cls_pw hL (d : ℤ)]
    exact eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance
  have heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL)) := by
    intro φ j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using heff φ
    | succ j hj ih =>
      push_cast
      rw [add_zsmul, one_zsmul]
      exact eff_add _ _ ih (heff φ)
  obtain ⟨t₀, ht₀⟩ := hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))
  have hN : t₀ + 2 < Q ^ (t₀ + 2) := Nat.lt_pow_self (by omega)
  obtain ⟨ψ, hψ, rfl⟩ := hu (t₀ + 2)
  have hpow := pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_
    · have h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2 := by
        rw [choose_two_succ]; omega
      have h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2 :=
        Nat.le_mul_of_pos_left _ hd
      omega
    · have hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2 := Nat.choose_pos (by omega)
      have e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) -
          (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) =
          (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL) := by
        rw [hpow, map_zsmul, ← natCast_zsmul]
        push_cast
        module
      rw [e]
      exact heffn _ _ hb
  rw [hψ1, one_pow]

end GlobalTheory.AmpleRigid
end
end

section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.AmpleTwistLB

theorem ample_pow_div : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  intro W S _ _ f A hA N M hN hM hcls hV
  have : CompactSpace S := hA.compactSpace
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow A n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hA.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨K, hK, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hAK := isLB_lbPow hA.isLB K
  have hG : ((lbPow A K).pull f).IsLB := LB.isLB_pull hAK f
  have hGgen : IsGenerated ((lbPow A K).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hMK := isLB_lbPow hM K
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hMK hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB ((M.pull (f ⁻¹ᵁ V z).ι).pull (W.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB (M.pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hM _) (GenSpread.lbIso_pull_pull hM _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hM _) hK).2 h₂).of_lbIso (LB.isLB_pull hMK _)
      (lbIso_lbPow_pull hM _ K).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hAf : (A.pull f).IsLB := LB.isLB_pull hA.isLB f
  have hD : (LB.div (lbPow (A.pull f) (c + k)) N).IsLB := LB.isLB_div (isLB_lbPow hAf (c + k)) hN
  refine (isAmpleLB_pow_iff hD hK).1 ?_
  have hT := AbLaw.isLB_tw hMK hG (c : ℤ)
  have hGk := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = K • CechPic.cls _ hAf := by
    rw [CechPic.cls_pull hAK f, CechPic.cls_lbPow hA.isLB, map_nsmul, ← CechPic.cls_pull hA.isLB f]
  have eT : CechPic.cls _ hT = CechPic.cls _ hMK + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hMK (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD K) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk, CechPic.cls_div (isLB_lbPow hD K) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hM, eG, CechPic.cls_div (isLB_lbPow hAf (c + k)) hN hD,
    CechPic.cls_lbPow hAf, hcls]
  module

end GlobalTheory.AmpleTwistLB
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser : ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  first | exact @GlobalTheory.NormSum.exists_prime_integralOver | exact GlobalTheory.NormSum.exists_prime_integralOver | (intros; apply GlobalTheory.NormSum.exists_prime_integralOver <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.denominator_bound_weierstrass_cm_torsion : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  first | exact @GlobalTheory.CMSize.main | exact GlobalTheory.CMSize.main | (intros; apply GlobalTheory.CMSize.main <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M1 → AdmGK M1 → Intw M1 M2 f → f ≠ 0 → ∀ (μ : Ix p q → ℚ), (∃ v, IsHW M1.act μ v) → (∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν) → (∃ (μ' : Ix r s → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct1 p q r s) μ P → f P ∈ Submodule.map f (genSub (fockAct2 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q}) := by
  first | exact @GlobalTheory.FockAlg.min_first | exact GlobalTheory.FockAlg.min_first | (intros; apply GlobalTheory.FockAlg.min_first <;> assumption)
end
