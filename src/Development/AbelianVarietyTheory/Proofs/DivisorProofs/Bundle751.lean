module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
open IsLocalRing

theorem maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre :
    ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O]
      [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat →
      IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  intro O' O _ _ _ _ _ σ hloc hflat hart g hg
  letI := σ.toAlgebra
  haveI : Module.Flat O' O := hflat
  haveI : Algebra.HasGoingDown O' O := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap O' O) := hloc
  haveI : IsLocalHom σ := hloc
  set I : Ideal O := (maximalIdeal O').map σ with hI
  have hIle : I ≤ maximalIdeal O := IsLocalRing.map_maximalIdeal_le _
  haveI : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top hIle)
  haveI : IsLocalRing (O ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (O ⧸ I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hle => ?_⟩
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le (maximalIdeal.isMaximal _).ne_top
      hle).ge
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal O') (maximalIdeal O)
  have hIalg : (maximalIdeal O').map (algebraMap O' O) = I := rfl
  rw [hIalg, hmap, hF, add_zero] at H
  have hdim : ((maximalIdeal O').spanFinrank : WithBot ℕ∞) = g := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, ← maximalIdeal_height_eq_ringKrullDim, ← H,
      maximalIdeal_height_eq_ringKrullDim, hg]
  have hg' : (maximalIdeal O').spanFinrank = g := by exact_mod_cast hdim
  have hfg : (maximalIdeal O').FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hg'] at htcard
  let u : Fin g → O' := fun i => (t.equivFin.symm (Fin.cast htcard.symm i) : O')
  have hu : Set.range u = (t : Set O') := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm _).2
    · intro hx; exact ⟨Fin.cast htcard (t.equivFin ⟨x, hx⟩), by simp [u]⟩
  refine ⟨fun i => σ (u i), ?_⟩
  rw [hI, ← htspan, Ideal.map_span, ← hu, ← Set.range_comp]
  rfl

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.LevelLift

theorem exists_linear_lift {J G V : Type} [Fintype J] [DecidableEq J] [Group G] [AddCommGroup V] [Module ℂ V]
    (ex : V → G) (hadd : ∀ z w, ex (z + w) = ex z * ex w) (honto : Function.Surjective ex)
    (Λ : Submodule ℤ V) (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (k : ℕ) (hk : 0 < k) (lev : (J → ℤ) → G)
    (hl : ∀ a b, lev (a + b) = lev a * lev b) (hp : ∀ a, lev a ^ k = 1) :
    ∃ l : (J → ℤ) →ₗ[ℤ] Λ, ∀ a, lev a = ex ((k : ℂ)⁻¹ • (l a : V)) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let E : V →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) (fun z w => by
    rw [hadd]; rfl)
  let F : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (lev z)) (fun z w => by
    rw [hl]; rfl)
  choose z hz using fun j : J => honto (lev (Pi.single j 1))
  have hw : ∀ j, k • z j ∈ Λ := fun j => by
    rw [← hker]
    have h1 : E (k • z j) = k • E (z j) := map_nsmul E k (z j)
    have h2 : ex (k • z j) = ex (z j) ^ k := congrArg Additive.toMul h1
    rw [h2, hz, hp]
  let l : (J → ℤ) →ₗ[ℤ] Λ := (Pi.basisFun ℤ J).constr ℤ fun j => ⟨k • z j, hw j⟩
  have hlj : ∀ j, (l (Pi.single j 1) : V) = k • z j := fun j => by
    have := (Pi.basisFun ℤ J).constr_basis ℤ (fun j => (⟨k • z j, hw j⟩ : Λ)) j
    rw [Pi.basisFun_apply] at this
    exact congrArg Subtype.val this
  let F' : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => E ((k : ℂ)⁻¹ • (l a : V))) (fun a b => by
    rw [map_add (f := _), Submodule.coe_add, smul_add, map_add (f := _)])
  refine ⟨l, fun a => ?_⟩
  have hmem : a ∈ F.eqLocus F' := by
    have ha : a = ∑ j, a j • (Pi.single j 1 : J → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [ha]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
    show Additive.ofMul (lev (Pi.single j 1)) = Additive.ofMul (ex ((k : ℂ)⁻¹ • (l (Pi.single j 1) : V)))
    rw [hlj, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul, hz]
  exact congrArg Additive.toMul (show F a = F' a from hmem)

theorem dvd_sub_of_exp_eq (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  obtain ⟨c, hc⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨c, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    first
      | linear_combination (2 * Real.pi * Complex.I) * hc
      | linear_combination -(2 * Real.pi * Complex.I) * hc
      | linear_combination hc
      | linear_combination -hc
  exact_mod_cast this

theorem exists_lattice_lift : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  intro h k P lev u Ef hk hl hp hW hE
  obtain ⟨l, hlift⟩ := exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp
  refine ⟨l, hlift, fun a b => ?_⟩
  have h1 := hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  have h2 := hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  rw [← hlift a, ← hlift b] at h2
  have h3 := GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2
  exact dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)

end GlobalTheory.LevelLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

theorem _root_.GlobalTheory.T.generator_translate_ratio_global_unit : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rosGen_comp_val : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}, GlobalFnsSt → IsAbelianScheme A → L.IsLB →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = f₂ ≫ f₁ → g = g₁ ≫ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.ι}, Good L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y = val₂ u₁ z J (x ≫ f₂) y * val₂ u₂ z J x (y ≫ g₁) := by
  intro S A _ _ L hG hA hL f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have zl : ∀ (a b : A ⟶ A) [IsMonHom a] [IsMonHom b], zero2 A ≫ (lift (fst A A ≫ a) (snd A A ≫ b)).left = zero2 A := by
    intro a b _ _
    show (lift η[A] η[A]).left ≫ _ = (lift η[A] η[A]).left
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have v0 : ∀ {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb L φ ε)), LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t (zero2 A)) (LB.oneGen L) →
      ∀ {y : S} {I}, Good L y I → val t (zero2 A) y I = 1 := by
    intro K _ φ ε t ht y I hI
    have := val_corr hI ht (𝟙 _)
    rwa [val_pull hI, Category.id_comp, val_one] at this
  have key := gen_unique' hL (u := u)
    (u' := LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u₁ (lift (fst A A ≫ f₂) (snd A A)).left)
      (LB.pullGen L _ _ u₂ (lift (fst A A) (snd A A ≫ g₁)).left))
    (fun V _ k => by
      have p := prod_ros (f₂ ≫ f₁) (g₁ ≫ g₂) (fst A A) (snd A A) k
      rw [lift_fst_snd, Over.id_left] at p
      simp only [Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (prod_ros f₁ g₁ (fst A A ≫ f₂) (snd A A) k) (prod_ros f₂ g₂ (fst A A) (snd A A ≫ g₁) k)).trans
        (Eq.trans ?_ p.symm)
      simp only [Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    ((snd A A).left ≫ A.hom) (zero2 A) (by
      rw [Over.w (snd A A)]; exact Over.w (lift η[A] η[A]))
    (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) hu
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _) (DVR.pullGen_isGen _ _ _ _ hu₂ _))
    (fun y I hI => by
      rw [v0 u h₀ hI, val_mul hI, val_pull hI, val_pull hI]
      have e1 := zl f₂ (𝟙 A)
      have e2 := zl (𝟙 A) g₁
      simp only [Category.comp_id] at e1 e2
      rw [e1, e2, v0 u₁ h₁ hI, v0 u₂ h₂ hI, _root_.mul_one])
    T.left (lift x y).left z J hJ
  unfold val₂
  rw [key, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift,
    lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.WeilComplexUnique

theorem weilIs_unitOn_unique_complex : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (y : Sp ℂ ⟶ X) (k : ℤ) (x x' : Over.mk y ⟶ G) (c c' : ℂˣ), Out.WeilIs G L k x x' (unitOn c) → Out.WeilIs G L k x x' (unitOn c') → c = c' := by
  intro X G _ _ g _ _ L hL y k x x' c c' h h'
  exact GlobalTheory.weilIs_unique_fieldPoint X G L hL ℂ y k x x' c c' h h'

end GlobalTheory.WeilComplexUnique
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiUnitOfPsiOn

theorem injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by
  intro a b e
  have := congrArg (inv f).hom e
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem mem_wchart1 {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz

theorem psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by
  intro R _ _ D W ψ y j V _ hVW hj h
  obtain ⟨p, rfl⟩ : ∃ p, j = fun _ => p := ⟨j PUnit.unit, funext fun _ => rfl⟩
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    fun z hz => mem_wchart1 _ _ _ _ (hj hz)
  have hVr : V ≤ W.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hVW
  haveI := W.ι.isIso_app V hVr
  set u : Γ(W.toScheme, W.ι ⁻¹ᵁ V)ˣ := res hle ((ψ.psi y).s (fun _ => p)) with hu
  set r : Γ(Spec (CommRingCat.of R), V) := (inv (W.ι.app V)).hom u.val with hr
  have hr' : (W.ι.app V).hom r = u.val := by
    rw [hr, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨r, u.isUnit.map (inv (W.ι.app V)).hom, ?_⟩
  have hKr : jK R ⁻¹ᵁ V ≤ (jK R ⁻¹ᵁ W).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact fun z hz => hVW hz
  haveI := (jK R ⁻¹ᵁ W).ι.isIso_app (jK R ⁻¹ᵁ V) hKr
  apply injective_of_isIso ((jK R ⁻¹ᵁ W).ι.app (jK R ⁻¹ᵁ V))
  refine fn_ext ?_
  intro z hz
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hzV : jK R ((jK R ⁻¹ᵁ W).ι z) ∈ V := hz
  have hpt : W.ι ((jK R ∣_ W) z) = jK R ((jK R ⁻¹ᵁ W).ι z) := congrArg (fun q => q z) hι
  have hm : (jK R ∣_ W) z ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z) ∈ V
    rw [hpt]; exact hzV
  have h₁ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hm)
  have h₂ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ⁻¹ᵁ W).ι ≫ D.xK y) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hzV)
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi y) (jK R ∣_ W) (𝟙 _) z (fun _ => p) h₁).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq y) (𝟙 _) z p h₁ h₂).trans
      (gm_pullGen D.P.L _ _ (D.psi y) (jK R ⁻¹ᵁ W).ι (𝟙 _) z (fun _ => p) h₂))
  rw [Category.id_comp, Category.id_comp] at e₃
  have l₁ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz ((jK R).app V |>.hom r)
  have l₂ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz
    (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi y).s (fun _ => p)).val)
  rw [Category.id_comp] at l₁ l₂
  rw [l₁, l₂, gs_pull _ _ z V hzV r, ← hι, ← gs_pull _ _ z V hm r, hr', hu,
    gs_unit _ z _ hm]
  erw [gm_res _ z hle hm]
  erw [gs_res _ z h hz]
  rw [gs_unit _ z _ (h hz)]
  exact congrArg Units.val e₃


end GlobalTheory.PsiUnitOfPsiOn
end
end
