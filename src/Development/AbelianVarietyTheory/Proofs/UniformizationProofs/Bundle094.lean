module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionLiftAbelianPartFiniteExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiIn_maximalIdeal_of_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → D.PsiEven → {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ 1)}.Finite → ∀ χ : D.X, χ ≠ 0 → D.PsiIn χ (IsLocalRing.maximalIdeal V) := by
  intro V _ _ _ hV D hT hE hfin χ hχ
  have : IsDiscreteValuationRing V := hV.1
  obtain ⟨ga, a, ha⟩ := exists_psiScal V D
  have hc := GlobalTheory.T.psiScalars_relations_up_to_baseUnits V D ga a ha
  have hm : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hiff := fun x => psiIn_iff_scalar_mem V D ga a ha x _ hm
  rw [hiff]
  refine cubeRel_scalars_mem_maximalIdeal V D.X a (hc.1 hT) (hc.2 hE) ?_ χ hχ
  refine hfin.subset ?_
  intro x hx
  show ¬ _
  rw [pow_one, hiff]
  exact hx

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem mem_of_orthogonal_of_card {F : Type} [Field F] {M U : Type} [CommGroup M] [CommGroup U] (φ : U →* Fˣ)
    (hφ : Function.Injective φ) (N : ℕ) (w : M → M → U → Prop)
    (hex : ∀ x y, x ^ N = 1 → y ^ N = 1 → ∃! ζ, w x y ζ)
    (hmul : ∀ x x' y ζ ζ', w x y ζ → w x' y ζ' → w (x * x') y (ζ * ζ'))
    (hsymm : ∀ x y ζ, w x y ζ → w y x ζ⁻¹)
    (hfin : Nat.card {x : M // x ^ N = 1} ≠ 0)
    (hnd : ∀ x, x ^ N = 1 → (∀ y, y ^ N = 1 → w x y 1) → x = 1)
    (T H : Subgroup M) (hT : ∀ x ∈ T, x ^ N = 1) (hH : ∀ x ∈ H, x ^ N = 1)
    (hc : Nat.card T * Nat.card H = Nat.card {x : M // x ^ N = 1})
    (hTH : ∀ x ∈ T, ∀ y ∈ H, w x y 1) (x : M) (hx : x ^ N = 1) (hxH : ∀ y ∈ H, w x y 1) : x ∈ T := by
  let K : Subgroup M := (powMonoidHom N : M →* M).ker
  have hK : ∀ a, a ∈ K ↔ a ^ N = 1 := fun a => Iff.rfl
  have hcK : Nat.card K = Nat.card {x : M // x ^ N = 1} := rfl
  have : Finite K := Nat.finite_of_card_ne_zero (hcK ▸ hfin)
  have hex' : ∀ a b : K, ∃ ζ, w a b ζ := fun a b => (hex a b a.2 b.2).exists
  choose v hv using hex'
  have hu : ∀ (a b : K) ζ, w a b ζ → v a b = ζ := fun a b ζ h => (hex a b a.2 b.2).unique (hv a b) h
  have h1 : ∀ a a' b : K, v (a * a') b = v a b * v a' b :=
    fun a a' b => hu _ _ _ (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have hs : ∀ a b : K, v b a = (v a b)⁻¹ := fun a b => hu _ _ _ (hsymm _ _ _ (hv a b))
  have hTK : T ≤ K := hT
  have hHK : H ≤ K := hH
  have key := (GlobalTheory.perfectPairing_orthogonal_of_card F K (fun a b => φ (v a b))
    (fun a a' b => by rw [h1, map_mul])
    (fun a b b' => by rw [hs (b * b') a, h1, mul_inv, ← hs, ← hs, map_mul])
    (fun a ha => Subtype.ext (hnd a a.2 fun y hy => by
      have h := hv a ⟨y, hy⟩
      rwa [hφ ((ha ⟨y, hy⟩).trans φ.map_one.symm)] at h))
    (T.subgroupOf K) (H.subgroupOf K)
    (fun t ht h hh => by rw [hu _ _ _ (hTH t ht h hh), map_one])
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hc, hcK])).1 ⟨x, hx⟩
  exact key.1 fun h hh => by rw [hu ⟨x, hx⟩ h _ (hxH h hh), map_one]

theorem mem_of_cubWeil_orthogonal : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ T H : Subgroup (TF (R := V) F ⟶ G), (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = N ^ (2 * A.g) → (∀ x ∈ T, ∀ y ∈ H, CubWeil s.P.c N x y 1) → ∀ x, x ^ N = 1 → (∀ y ∈ H, CubWeil s.P.c N x y 1) → x ∈ T := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N hN T H hT hH hc hTH x hx hxH
  obtain ⟨hcard, hnd⟩ := GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect hL V A G s F N hN
  let ε₀ : Γ(Spec (CommRingCat.of F), ⊤) ≃+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine mem_of_orthogonal_of_card (F := F) (M := TF (R := V) F ⟶ G) (U := Γ((TF (R := V) F).left, ⊤)ˣ)
    (Units.map ε₀.toMonoidHom) (Units.map_injective ε₀.injective) N (CubWeil s.P.c N)
    (fun _ _ hx hy => existsUnique_cubWeil _ hx hy) (fun _ _ _ _ _ h h' => h.mul_left h')
    (fun _ _ _ h => h.symm) ?_ hnd T H hT hH (hc.trans hcard.symm) hTH x hx hxH
  rw [hcard]
  exact pow_ne_zero _ (by omega)

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psi_mul_psi_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  first | exact @GlobalTheory.psi_mul_psi_of_addition_second_variable | exact GlobalTheory.psi_mul_psi_of_addition_second_variable | (intros; apply GlobalTheory.psi_mul_psi_of_addition_second_variable <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  first | exact @GlobalTheory.psiRel_of_pullB | exact GlobalTheory.psiRel_of_pullB | (intros; apply GlobalTheory.psiRel_of_pullB <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.valueExpansion_of_chartExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  first | exact @GlobalTheory.UU.expF_of_expands | exact GlobalTheory.UU.expF_of_expands | (intros; apply GlobalTheory.UU.expF_of_expands <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionFormula_coefficients_abelian_square : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  first | exact @GlobalTheory.AddCoeff.main | exact GlobalTheory.AddCoeff.main | (intros; apply GlobalTheory.AddCoeff.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjThickForTorsionLiftWrapper {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

theorem _root_.GlobalTheory.T.torsion_lift_abelianPart_finite_extension : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : W →+* F), Function.Injective φ ∧ φ.comp (algebraMap V W) = (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧ (∀ z : F, z ^ N = 1 → z ∈ φ.range) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), y ^ N = 1 ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (y).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) ∧ (Spec.map (CommRingCat.ofHom φ)) ≫ b.left = x.left := by
  first | exact @GlobalTheory.TorsionLift.torsion_lift | exact GlobalTheory.TorsionLift.torsion_lift | (intros; apply GlobalTheory.TorsionLift.torsion_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_expansion_section_lineBundle_power : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  first | exact @GlobalTheory.BaseExpansionExists.main | exact GlobalTheory.BaseExpansionExists.main | (intros; apply GlobalTheory.BaseExpansionExists.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_mul_pow_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (k l : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (l : ℤ)))) :
    ∃ u : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((k + l : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval u r z J = sval s r z J * sval t r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (φ' := fun _ : Fin 1 => p) (ε' := fun _ => ((k + l : ℕ) : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, zpow_add]) (H1.SectionArithmetic.mulSec s t)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec s t r z hJ)⟩

theorem exists_pow_exp_supp : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U Λ θ f hθ hf l hl
  induction l, hl using Nat.le_induction with
  | base => exact ⟨θ, f, hθ, hf, fun Z r z J _ => (pow_one _).symm⟩
  | succ l hl ih =>
    obtain ⟨σ, g, hσ, hg, hv⟩ := ih
    obtain ⟨u, hu⟩ := exists_mul_pow_sec U.P.L.isLB _ l 1 σ θ
    obtain ⟨g', hg'⟩ := GlobalTheory.BaseExpansionExists.main h₁ h₂ V hV D A G U (l + 1) (Nat.le_add_left 1 l) u
    exact ⟨u, g', hg', GlobalTheory.T.product_support_in_subgroup_theta V hV D A G U Λ l 1 σ θ u g f g' hσ hθ hg' hu hg hf,
      fun Z r z J hJ => by rw [hu Z r z J hJ, hv Z r z J hJ, pow_succ]⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  first | exact @GlobalTheory.UU.exists_cp_of_isSymmetric | exact GlobalTheory.UU.exists_cp_of_isSymmetric | (intros; apply GlobalTheory.UU.exists_cp_of_isSymmetric <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.card_quotient_kTorsion_pairs : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  first | exact @GlobalTheory.UT.card_qk | exact GlobalTheory.UT.card_qk | (intros; apply GlobalTheory.UT.card_qk <;> assumption)
end
