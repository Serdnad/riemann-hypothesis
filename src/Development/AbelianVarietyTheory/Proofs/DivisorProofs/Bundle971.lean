module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle944
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isFun_of_isOb2_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj L hob

  obtain ⟨θ, -, -, hθ, -⟩ := hob 0

  let Wm : Submodule R (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') :=
    { carrier := {g | ∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))}
      add_mem' := fun hx hy T T' a ↦ Ideal.add_mem _ (hx T T' a) (hy T T' a)
      zero_mem' := fun T T' a ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg T T' a ↦ by
        show r • g T T' a ∈ _
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hg T T' a) }
  let q : (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') →ₗ[R]
      (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun g T T' T'' a b ↦ L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b
      map_add' := fun g g' ↦ by
        funext T T' T'' a b
        simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r g ↦ by
        funext T T' T'' a b
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add] }
  let v : GlobForm s₀ →+ (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun w T T' T'' a b ↦ θ T T' T'' a b (w.1 T)
      map_zero' := by funext T T' T'' a b; simp
      map_add' := fun w w' ↦ by funext T T' T'' a b; simp }
  have hv : ∀ (r : R) (w : GlobForm s₀), v (π r • w) = r • v w := by
    intro r w
    funext T T' T'' a b
    show θ T T' T'' a b (π r • w.1 T) = r • θ T T' T'' a b (w.1 T)
    have e : π r • w.1 T = L.p T (algebraMap R (L.B T) r) • w.1 T := by
      rw [SemiHom.map_algebraMap (L.semi T), algebraMap_smul]
    rw [e, (hθ T T' T'' a b).smul, AlgHom.commutes, ← Algebra.smul_def]
  have hW : ∀ (r : R), π r = 0 → ∀ m ∈ Wm, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    funext T T' a
    show r • m T T' a = 0
    rw [Algebra.smul_def]
    exact mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ hrI) (hm T T' a)
  have hex : ∀ w : GlobForm s₀, ∃ m ∈ Wm, q m = v w := by
    intro w
    obtain ⟨g, hg, hgθ⟩ := GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero R R₀ I hI π hπ hk R₁ α _ (OAff s₀) L w θ hθ (hob w)
    refine ⟨g, hg, ?_⟩
    funext T T' T'' a b
    exact (hgθ T T' T'' a b).symm
  obtain ⟨u, hus, huW, huq⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hproj _ _ Wm hW q v hv hex

  have hext : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃! ξ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T',
      (∀ b w, ξ (L.p T b • w) = L.ρ a b * ξ w) ∧ (∀ w, ξ w ∈ I.map (algebraMap R (L.B T'))) ∧
        ∀ w : GlobForm s₀, ξ (w.1 T) = u w T T' a := fun T T' a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar T _ _ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)
      ((Pi.evalAddMonoidHom (fun _ ↦ L.B T') a).comp ((Pi.evalAddMonoidHom _ T').comp ((Pi.evalAddMonoidHom _ T).comp u)))
      (fun r w ↦ by
        show u (π r • w) T T' a = r • u w T T' a
        rw [hus]; rfl) (fun w ↦ huW w T T' a)
  choose ξ hξ huniq using hext
  have hβ : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃ β : L.B T →ₐ[R] L.B T', IsTheta I (L.p T) (L.ρ a) β (ξ T T' a) :=
    fun T T' a ↦ (theta_classify R R₀ _ _ _ I hI π hπ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)).2
      (ξ T T' a) (hξ T T' a).1 (hξ T T' a).2.1
  choose ρ' hρ' using hβ
  have hρ'e : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, ρ' T T' a x = L.ρ a x - ξ T T' a (D R₀ _ (L.p T x)) := by
    intro T T' a x
    rw [(hρ' T T' a).der]; abel
  have hp0 : ∀ (T T' : AffOp X₀) (a : T ⟶ T') y, L.p T' (ξ T T' a y) = 0 :=
    fun T T' a y ↦ (L.ker T' _).2 ((hξ T T' a).2.1 y)
  have hnat : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, L.p T' (ρ' T T' a x) = mp (OAff s₀) a (L.p T x) := by
    intro T T' a x
    rw [hρ'e, map_sub, hp0, sub_zero, L.nat]
  let L' : Pre I π (OAff s₀) :=
    { B := L.B, p := L.p, semi := L.semi, surj := L.surj, ker := L.ker, smooth := L.smooth
      ρ := fun {T T'} a ↦ ρ' T T' a
      nat := fun {T T'} a x ↦ hnat T T' a x }
  refine ⟨L', ?_⟩

  have hcomp : ∀ (T T' T'' : AffOp X₀) (a : T ⟶ T') (b : T' ⟶ T'') (y : Ω[Sec s₀ T.unop.1⁄R₀]),
      ξ T T'' (a ≫ b) y = L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y := by
    intro T T' T'' a b
    let ψ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T'' :=
      AddMonoidHom.mk' (fun y ↦ L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
        (fun y z ↦ by simp only [map_add (f := _)]; abel)
    have hψm : ∀ y, ψ y ∈ I.map (algebraMap R (L.B T'')) := fun y ↦
      Ideal.sub_mem _ (Ideal.add_mem _ (algHom_mem_map I (L.ρ b) ((hξ T T' a).2.1 y)) ((hξ T' T'' b).2.1 _))
        ((hθ T T' T'' a b).mem y)
    have e : ψ = ξ T T'' (a ≫ b) := by
      refine huniq T T'' (a ≫ b) ψ ⟨fun c y ↦ ?_, hψm, fun w ↦ ?_⟩
      · have h1 : ψ (L.p T c • y) = L.ρ b (L.ρ a c) * ψ y := by
          show L.ρ b (ξ T T' a (L.p T c • y)) + ξ T' T'' b (p1 (OAff s₀) a (L.p T c • y)) -
              θ T T' T'' a b (L.p T c • y) = L.ρ b (L.ρ a c) * (L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
          rw [(hξ T T' a).1, oneFormsMapOfFunctorMorphism_smul, ← L.nat, (hξ T' T'' b).1, (hθ T T' T'' a b).smul, map_mul]
          simp only [AlgHom.comp_apply]; ring
        have h2 : L.ρ b (L.ρ a c) = L.ρ (a ≫ b) c + θ T T' T'' a b (D R₀ _ (L.p T c)) := by
          rw [(hθ T T' T'' a b).der]; simp
        rw [h1, h2, add_mul, mul_eq_zero_of_mem_map hI ((hθ T T' T'' a b).mem _) (hψm y), add_zero]
      · show L.ρ b (ξ T T' a (w.1 T)) + ξ T' T'' b (p1 (OAff s₀) a (w.1 T)) - θ T T' T'' a b (w.1 T) = u w T T'' (a ≫ b)
        rw [← w.2 a, (hξ T T' a).2.2, (hξ T' T'' b).2.2]
        have := congrFun (congrFun (congrFun (congrFun (congrFun (huq w) T) T') T'') a) b
        change L.ρ b (u w T T' a) - u w T T'' (a ≫ b) + u w T' T'' b = θ T T' T'' a b (w.1 T) at this
        rw [← this]; abel
    intro y
    rw [← e]; rfl
  intro T T' T'' a b x
  change ρ' T T'' (a ≫ b) x = ρ' T' T'' b (ρ' T T' a x)
  have hD : D R₀ _ (L.p T' (ρ' T T' a x)) = p1 (OAff s₀) a (D R₀ _ (L.p T x)) := by
    rw [hnat, p1_D]
  rw [hρ'e T' T'' b, hD, hρ'e T T' a, map_sub, hρ'e, hcomp]
  have h2 : L.ρ b (L.ρ a x) = L.ρ (a ≫ b) x + θ T T' T'' a b (D R₀ _ (L.p T x)) := by
    rw [(hθ T T' T'' a b).der]; simp
  rw [h2]; abel

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_cochain_of_isOb1_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h
  obtain ⟨κ, -, -, hκ, -, -, -⟩ := h 0
  let W : Submodule R (∀ T : C', L'.B T) :=
    { carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))}
      add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T)
      zero_mem' := fun T ↦ Ideal.zero_mem _
      smul_mem' := fun r m hm T ↦ by
        show r • m T ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hm T) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext T
    show r • m T = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  let q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun m T T' a ↦ m T' - L'.ρ a (m T)
      map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r m ↦ by
        funext T T' a; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  let v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T))
      map_zero' := by funext T T' a; exact map_zero (κ T T' a)
      map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    funext T T' a
    show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))
    have hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r) := by
      have h1 := L.semi (n.G.obj T) r 1
      rw [← Algebra.algebraMap_eq_smul_one, map_one] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    have h3 := (hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))
    rw [hp, algebraMap_smul, AlgHom.commutes] at h3
    rw [h3, Algebra.smul_def]
  have hq : ∀ w, ∃ m ∈ W, q m = v w := by
    intro w
    obtain ⟨κw, σw, zw, hκw, hσw, hc, hz⟩ := h w
    obtain ⟨f, hf⟩ := H1.mk_eq_zero.1 hc.symm
    have hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a := fun T T' a ↦
      (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _
        (hκ T T' a)).2.2.1 (hκw T T' a)
    refine ⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T)
      (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩
    funext T T' a
    have hn := (sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T')
      (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)
    have hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T) := by
      rw [← hf]; rfl
    show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))
    rw [hκκ, ← (hz T T' a).2, hzf, map_sub, hn]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq
  exact ⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R]

theorem pullHO1_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = pullHO1 h' c := by
  subst e; rfl

theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) {c : HO1 s} {c' : HO1 s'} :
    IsPullO h c c' ↔ IsPullO h' c c' := by
  subst e; rfl

theorem pullHO1_self {X : Scheme.{0}} {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = c :=
  (IsPullO.eq_pullHO1 h
    (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c)).symm

theorem pullHO1_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : HO1 C.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = pullHO1 (overW (g ≫ f)) a := by
  have h'' : (g.left ≫ f.left) ≫ C.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.comp_left]; exact overW (g ≫ f)
  have k := (GlobalTheory.T.structureSheaf_pullback_relations_basic R C.left B.left C.hom B.hom f.left (overW f)).2.2 A.left A.hom g.left (overW g) h'' a _ _
    (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact IsPullO.eq_pullHO1 _ ((isPullO_congr (show g.left ≫ f.left = (g ≫ f).left from rfl) _ _).1 k)

theorem pullHO1_pull_self {A B : Over (Sp R)} (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 𝟙 A) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = a := by
  rw [pullHO1_comp]
  have h' : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  rw [pullHO1_congr (show (g ≫ f).left = 𝟙 A.left by rw [e]; rfl) _ h', pullHO1_self]

theorem pullHO1_pull_one {A B : Over (Sp R)} [GrpObj A] (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 1) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = 0 := by
  rw [pullHO1_comp]
  have h' : (toUnit A ≫ η[A]).left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := overW _
  rw [pullHO1_congr (show (g ≫ f).left = (toUnit A ≫ η[A]).left by rw [e, Hom.one_def]) _ h', ← pullHO1_comp]
  have : pullHO1 (overW η[A]) a = 0 := by
    haveI : IsAffine (𝟙_ (Over (Sp R))).left := by change IsAffine (Sp R); infer_instance
    exact (GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ _
  rw [this, map_zero]

variable (A : Over (Sp R)) [GrpObj A]

def sumPull : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
  (pullHO1 (overW (fst A A))).coprod (pullHO1 (overW (snd A A)))

def axesPull : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  (pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A)))).prod (pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))))

theorem axesPull_sumPull (x : HO1 A.hom × HO1 A.hom) : axesPull A (sumPull A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = a
    rw [map_add (f := _), pullHO1_pull_self _ _ (lift_fst _ _), pullHO1_pull_one _ _ (lift_snd _ _), add_zero]
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = b
    rw [map_add (f := _), pullHO1_pull_one _ _ (lift_fst _ _), pullHO1_pull_self _ _ (lift_snd _ _), zero_add]

theorem axesPull_injective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Injective (axesPull A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x = 0 := congrArg Prod.fst hx
  have h2 : pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x = 0 := congrArg Prod.snd hx
  refine hax R A g hA hg x ?_ ?_
  · have := isPullO_pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x; rwa [h1] at this
  · have := isPullO_pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x; rwa [h2] at this

theorem pullHO1_mul (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (a : HO1 A.hom) : pullHO1 (overW μ[A]) a = sumPull A (a, a) := by
  apply axesPull_injective A hax g hA hg
  rw [axesPull_sumPull]
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_right]) a
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_left]) a

theorem sumPull_bijective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (sumPull A) :=
  ⟨Function.LeftInverse.injective (axesPull_sumPull A), fun c ↦
    ⟨axesPull A c, axesPull_injective A hax g hA hg (axesPull_sumPull A _)⟩⟩

end GlobalTheory.Obs.PrimitivePullback

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {h : φ ≫ s = s' ≫ spMap (RingHom.id R)}

theorem isPullO2_zero : IsPullbackH2Structure h (0 : CatCoh.H2 (OAff s)) (0 : CatCoh.H2 (OAff s')) := by
  unfold IsPullbackH2Structure; rw [map_zero, map_zero]

theorem isPullO2_add {a b : CatCoh.H2 (OAff s)} {a' b' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a')
    (hb : IsPullbackH2Structure h b b') : IsPullbackH2Structure h (a + b) (a' + b') := by
  unfold IsPullbackH2Structure at *; rw [map_add (f := _), map_add (f := _), ha, hb]

theorem isPullO2_smul {a : CatCoh.H2 (OAff s)} {a' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a') (r : R) :
    IsPullbackH2Structure h (r • a) (r • a') := by
  unfold IsPullbackH2Structure at *; rw [map_smulₛₗ, map_smulₛₗ, ha]

theorem isPullO2_unique {c : CatCoh.H2 (OAff s)} {x y : CatCoh.H2 (OAff s')} (hx : IsPullbackH2Structure h c x)
    (hy : IsPullbackH2Structure h c y) : x = y :=
  (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).1.1 (hx.symm.trans hy)

theorem pullback_wedge_cup_square (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (e : ⋀[R]^2 (HO1 s) ≃ₗ[R] CatCoh.H2 (OAff s))
    (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s) a b)
    (e' : ⋀[R]^2 (HO1 s') ≃ₗ[R] CatCoh.H2 (OAff s'))
    (he' : ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s') a b) (t : ⋀[R]^2 (HO1 s)) :
    IsPullbackH2Structure h (e t) (e' (exteriorPower.map 2 (pullHO1 h) t)) := by
  have key : ∀ a b : HO1 s, IsPullbackH2Structure h (e (exteriorPower.ιMulti R 2 ![a, b]))
      (e' (exteriorPower.map 2 (pullHO1 h) (exteriorPower.ιMulti R 2 ![a, b]))) := by
    intro a b
    have hc : (pullHO1 h) ∘ ![a, b] = ![pullHO1 h a, pullHO1 h b] := by
      funext i; fin_cases i <;> try rfl
    rw [exteriorPower.map_apply_ιMulti, hc, he, he']
    exact (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).2.1 a b _ _ (isPullO_pullHO1 h a) (isPullO_pullHO1 h b)
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> try rfl
    have := key (v 0) (v 1)
    rwa [← hv] at this
  | zero => simp only [map_zero]; exact isPullO2_zero
  | add x y _ _ hx hy => simp only [map_add (f := _)]; exact isPullO2_add hx hy
  | smul r x _ hx => simp only [map_smul]; exact isPullO2_smul hx r

end GlobalTheory.Obs.PrimitivePullback


open GlobalTheory.Obs.PrimitivePullback in
theorem GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso
    (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) : PrimitiveStructureSheafDegTwoVanish := by
  intro R _ A _ g hA hg c c₁ c₂ hm h1 h2
  have hax : AxesVanishingStructureSheafDegOne := GlobalTheory.T.axesO1_of_projective_rank_cup H
  obtain ⟨hAA, hgg⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, hproj, _⟩, e, he⟩ := H R A g hA hg
  obtain ⟨_, e', he'⟩ := H R (A ⊗ A) (g + g) hAA hgg
  obtain ⟨t, rfl⟩ := e.surjective c
  have km := pullback_wedge_cup_square (overW μ[A]) e he e' he' t
  have k1 := pullback_wedge_cup_square (overW (fst A A)) e he e' he' t
  have k2 := pullback_wedge_cup_square (overW (snd A A)) e he e' he' t
  have E : exteriorPower.map 2 (pullHO1 (overW μ[A])) t =
      exteriorPower.map 2 (pullHO1 (overW (fst A A))) t + exteriorPower.map 2 (pullHO1 (overW (snd A A))) t := by
    apply e'.injective
    rw [map_add (f := _), ← isPullO2_unique hm km, ← isPullO2_unique h1 k1, ← isPullO2_unique h2 k2]
  let P := LinearEquiv.ofBijective (sumPull A) (sumPull_bijective A hax g hA hg)
  have hμ : (pullHO1 (overW μ[A]) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ (LinearMap.inl R (HO1 A.hom) (HO1 A.hom) + LinearMap.inr R (HO1 A.hom) (HO1 A.hom)) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add]
    exact pullHO1_mul A hax g hA hg a
  have h₁ : (pullHO1 (overW (fst A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inl R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inl_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, add_zero]
  have h₂ : (pullHO1 (overW (snd A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inr R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inr_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, zero_add]
  simp only [hμ, h₁, h₂, exteriorPower.map_comp, LinearMap.comp_apply] at E
  rw [← map_add (exteriorPower.map 2 (sumPull A))] at E
  have hid : P.symm.toLinearMap ∘ₗ sumPull A = LinearMap.id :=
    LinearMap.ext fun x ↦ P.symm_apply_apply x
  have hinj : Function.Injective (exteriorPower.map 2 (sumPull A)) := by
    intro x y hxy
    have k : ∀ z, exteriorPower.map 2 P.symm.toLinearMap (exteriorPower.map 2 (sumPull A) z) = z := by
      intro z
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hid, exteriorPower.map_id, LinearMap.id_apply]
    rw [← k x, ← k y, hxy]
  haveI := hproj
  rw [GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective R (HO1 A.hom) t (hinj E), map_zero]
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials : ∀ (R R₀ B B₀ B' : Type) [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] (I : Ideal R), I ^ 2 = 0 → ∀ (π : R →+* R₀), Function.Surjective π → ∀ p : B →+* B₀, SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ α : B →ₐ[R] B', (∀ β : B →ₐ[R] B', (∀ b, α b - β b ∈ I.map (algebraMap R B')) → ∃! θ : Ω[B₀⁄R₀] →+ B', IsTheta I p α β θ) ∧ ∀ θ : Ω[B₀⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) → (∀ w, θ w ∈ I.map (algebraMap R B')) → ∃ β : B →ₐ[R] B', IsTheta I p α β θ := by
  first | exact @GlobalTheory.LiftSys.theta_classify | exact GlobalTheory.LiftSys.theta_classify | (intros; apply GlobalTheory.LiftSys.theta_classify <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  first | exact @GlobalTheory.LiftSys.cobound_I | exact GlobalTheory.LiftSys.cobound_I | (intros; apply GlobalTheory.LiftSys.cobound_I <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  first | exact @GlobalTheory.LiftSys.presents_isLift | exact GlobalTheory.LiftSys.presents_isLift | (intros; apply GlobalTheory.LiftSys.presents_isLift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  first | exact @GlobalTheory.LiftSys.locIso_nonempty | exact GlobalTheory.LiftSys.locIso_nonempty | (intros; apply GlobalTheory.LiftSys.locIso_nonempty <;> assumption)
end
