module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle180
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle122
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  first | exact @GlobalTheory.FiniteData.exists_isogenous_retract | exact GlobalTheory.FiniteData.exists_isogenous_retract | (intros; apply GlobalTheory.FiniteData.exists_isogenous_retract <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.GoodTrait
set_option linter.style.haveILetI false

theorem exists_unit_prime (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + -((5 : ℕ) : O)) := by
    have : ((3 : ℕ) : O) * 2 + -((5 : ℕ) : O) = 1 := by push_cast; norm_num
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, (IsUnit.neg_iff _).1 h⟩

theorem norm_eq_one_of_isUnit {W C : Type} [CommRing W] [NormedField C] (f : W →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {x : W}
    (hx : IsUnit x) : ‖f x‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h : ‖f x‖ * ‖f y‖ = 1 := by rw [← norm_mul, ← map_mul, hy, map_one, norm_one]
  have h₁ := hf x
  have h₂ := hf y
  have h₃ := norm_nonneg (f x)
  nlinarith

theorem exists_valuationSubring {K C : Type} [Field K] [NormedField C] [IsUltrametricDist C] (f : K →+* C) :
    ∃ S : ValuationSubring K, (∀ x, x ∈ S ↔ ‖f x‖ ≤ 1) ∧ ∀ x, S.valuation x = 1 ↔ ‖f x‖ = 1 := by
  let v := (NormedField.valuation (K := C)).comap f
  refine ⟨v.valuationSubring, fun x => ?_, fun x => ?_⟩
  · rw [Valuation.mem_valuationSubring_iff]
    exact Iff.rfl
  · rw [← (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one]
    exact NNReal.coe_inj.symm

theorem isDominant_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (spMap f) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap f)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot f).1 hf]
  exact bot_le



theorem range_subset_abLocus : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ThetaInt Y g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → IsUnit (φ (g PowerSeries.X)) → Set.range χ ⊆ abLocus Y.t.G := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO R₁ _ _ g y₁ _ _ _ hT hy W _ _ _ hW φ gam hgam χ hχ hu
  haveI : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField
      exact inferInstance
    · exact inferInstance
  obtain ⟨n, hn, hodd, hnu⟩ := exists_unit_prime O'
  obtain ⟨hdvr, -, hch⟩ := id hW
  obtain ⟨C, _, _, _, _, alg, -, -, hC⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  let iC : W →+* C := (algebraMap (FractionRing W) C).comp (algebraMap W _)
  have hiC : Function.Injective iC := (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  haveI : CharZero C := charZero_of_injective_ringHom hiC
  obtain ⟨o, ho, hθ⟩ := hT
  haveI := o.charZero
  let Γ : AlgebraicClosure (FractionRing R₁) →+* C :=
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).toRingHom
  have hΓ : Γ.comp (algebraMap (FractionRing R₁) _) = (algebraMap (FractionRing W) C).comp gam := by
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    exact RingHom.ext fun x => (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).commutes x
  have hΓ' : ∀ r, Γ (((algebraMap (FractionRing R₁) _).comp (algebraMap R₁ _)) r) = iC (φ r) := fun r => by
    have := DFunLike.congr_fun hΓ (algebraMap R₁ _ r)
    simp only [RingHom.comp_apply, hgam] at this
    exact this
  obtain ⟨o', hext, hth, -⟩ := GlobalTheory.FullExtend.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D _ C Γ o
  have e₀ : spMap Γ ≫ spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ =
      spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ := by
    rw [← Category.assoc, ← spMap_comp', hΓ, spMap_comp', Category.assoc]
  have bF : c.F →+* AlgebraicClosure (FractionRing R₁) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
      ((spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁) ≫ pullback.snd _ _).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing R₁)))).hom).hom
  have ho' := (GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y _ bF).2.2 C Γ _ o o' ho hext
  rw [e₀] at ho'
  have e₁ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp' (algebraMap R₁ _) gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp' φ (algebraMap W _)))
  have e₂ : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
  obtain ⟨M, f, χ', mp, hf, hfC, hχ', -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y C W hW hC
    (FractionRing W) (algebraMap (FractionRing W) C) (fun _ => rfl) (spMap gam ≫ y₁)
    (φ.comp (g.comp ((PowerSeries.C (R := O')).comp b))) (by
      rw [e₂, Category.id_comp, Category.assoc, hy, spMap_comp', spMap_comp', spMap_comp', ← Category.assoc, e₁,
        Category.assoc]) o' ho'
  obtain ⟨v, hv, hint⟩ := hθ n 2 hn hodd hnu one_le_two
  obtain ⟨S, hS, hS'⟩ := exists_valuationSubring Γ
  obtain ⟨a₁, -, a₃⟩ := hint S fun r => by rw [hS, hΓ']; exact hC.1 _
  have a₄ := a₃ (by rw [hS', hΓ']; exact norm_eq_one_of_isUnit iC hC.1 hu)
  have hnC : ‖(n : C)‖ = 1 := by
    have := norm_eq_one_of_isUnit iC hC.1 (hnu.map (φ.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, map_natCast] at this
  have hprop : IsProper M.t.G.hom := GlobalTheory.T.isProper_of_theta_unit_in_every_coset h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D C o' M n 2 hn hodd hnC le_rfl _ (hth _ _ hv)
    (fun x => (hS _).1 (a₁ x)) fun x => (a₄ x).imp fun h hh => (hS' _).1 hh
  let jC : M.W →+* C := (algebraMap (FractionRing M.W) C).comp (algebraMap M.W _)
  have hjC : Function.Injective jC := (algebraMap (FractionRing M.W) C).injective.comp (IsFractionRing.injective M.W _)
  have hjf : jC.comp f = iC := RingHom.ext hfC
  have hfi : Function.Injective f := Function.Injective.of_comp (f := jC) (by rw [← RingHom.coe_comp, hjf]; exact hiC)
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have := isDominant_spMap jC hjC
  have e₃ : χ' = spMap f ≫ χ := by
    refine ext_of_isDominant (spMap jC) ?_
    have e₄ : spMap jC = jFK (R := M.W) C ≫ jK M.W := spMap_comp' _ _
    have e₅ : spMap iC = spMap (algebraMap (FractionRing W) C) ≫ jK W := spMap_comp' _ _
    rw [← Category.assoc, ← spMap_comp', hjf, e₅, e₄, Category.assoc, hχ', Category.assoc, Category.assoc, hχ]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := hf.to_isIntegral.comap_surjective hfi x
  have h := (abLocus_pullback abLocusOne Y.t.semi mp.cart.1 x').2 fun K _ _ t _ => inferInstance
  rw [e₃] at h
  exact h

end GlobalTheory.Ex.GoodTrait
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ClosurePoint

theorem exists_full_of_closure_of_cosets :
    HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y K _ _ _ n j ρ z v hn hodd hj hc hvan hcos
  have hm : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  have hm3 : 3 ≤ n ^ j := hn3.trans (Nat.le_self_pow (by omega) n)
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hcos 0
    exact hx (by rw [h]; rfl)
  obtain ⟨C, _, _, _, _, _, S, κ, _, _, res, i, o, M, v', r', z', hnorm, hS, hres, hth, hv', hr', hρ,
    hz', hz⟩ := GlobalTheory.T.exists_trait_specialisation_of_mem_closure_thetaPoints h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K (n ^ j) ρ z v hm hc hv0 hvan
  have hunit : ∀ x, v x ≠ 0 → ‖(v' x : C)‖ = 1 := by
    intro x hx
    have hle : ‖(v' x : C)‖ ≤ 1 := (hS _).1 (v' x).2
    by_contra hne
    have h0 := hres (v' x) (lt_of_le_of_ne hle hne)
    rw [hv' x] at h0
    exact hx (i.injective (by rw [h0, map_zero]))
  have hprop : IsProper M.t.G.hom :=
    GlobalTheory.T.isProper_of_theta_unit_in_every_coset h1 h2 h3 h4 h5 h6 h7 E H D C o M n j hn hodd (hnorm n hn.pos) hj
      (fun x => v' x) hth (fun x => (hS _).1 (v' x).2)
      (fun x => (hcos x).imp fun h hh => hunit _ hh)
  obtain ⟨o', hρ', hζ', hth'⟩ := GlobalTheory.T.exists_specialisation_with_thetaPoint h1 h2 h3 h4 h5 h6 h7 E H D C hnorm o M hprop S hS κ res
    hres (n ^ j) v' hm hm3 hth (by
      obtain ⟨x, hx⟩ := hcos 0
      exact ⟨_, by rw [hv']; exact (map_ne_zero i).2 hx⟩)
  refine GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K κ i (n ^ j) ρ z v o' hm hc
    ((hρ' r' hr').trans hρ) ((hζ' _ (by positivity) z' hz').trans hz) ?_
  have : (fun x => res (v' x)) = fun x => i (v x) := funext hv'
  rwa [this] at hth'

end GlobalTheory.Ex.ClosurePoint
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.extension_of_abelian_schemes : Laws → Laws2 → Ega := by
  first | exact @GlobalTheory.LN.ega_of_laws | exact GlobalTheory.LN.ega_of_laws | (intros; apply GlobalTheory.LN.ega_of_laws <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGen
open GlobalTheory.TorusExt

theorem mem_of_step {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M) (n j : ℕ) (h₀ : ∀ t, φ t ^ (n ^ j) = 1)
    (h : ∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) (t : T) : φ t ∈ S := by
  have key : ∀ i : ℕ, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ (n ^ i) := fun i => by
    induction i with
    | zero => exact ⟨1, S.one_mem, t, by simp⟩
    | succ i ih =>
      obtain ⟨s, hs, t', e⟩ := ih
      obtain ⟨s', hs', t'', e'⟩ := h t'
      refine ⟨s * s' ^ (n ^ i), S.mul_mem hs (S.pow_mem hs' _), t'', ?_⟩
      rw [e, e', mul_pow, ← pow_mul, _root_.mul_assoc, pow_succ']
  obtain ⟨s, hs, t', e⟩ := key j
  rwa [e, h₀, _root_.mul_one]

attribute [local instance] gtGroup

theorem exists_hom {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [CommGroup M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') :
    ∃ φ : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker →+ Additive M,
      ∀ t (p : QkPt D F k), p.y = 0 → p.g = t.1 → φ t = Additive.ofMul (f p) := by
  have hiota0 : ∀ (h : GtPtF D F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D (T := TF (R := R) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let qkMk (g : GtPtF D F) (h : k • g = 0) : QkPt D F k :=
    ⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, hiota0 _ ((isZero_iff_eq _).2 h)⟩
  let r : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker → QkPt D F k := fun t =>
    qkMk t.1 t.2
  refine ⟨AddMonoidHom.mk' (fun t => Additive.ofMul (f (r t))) fun t t' => ?_, fun t p hy hg => ?_⟩
  · let p := qkMk (t.1 + t'.1) (by rw [nsmul_add, show k • t.1 = 0 from t.2, show k • t'.1 = 0 from t'.2, add_zero])
    have hp : QkAdd (r t) (r t') p :=
      ⟨p, by simp [p, qkMk, r], (isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB p⟩
    rw [← ofMul_mul, ← hf _ _ _ hp]
    exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext rfl rfl)
  · exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext (by simpa [r] using hy.symm) hg.symm)

theorem fromGt_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN theta ϑ hE hP n j hn ho hu hj x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hdvd₂ : n * n ∣ n ^ j := by rw [← pow_two]; exact pow_dvd_pow n hj
  have hm : Odd (n ^ j) := ho.pow
  have hum : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hu.pow j
  have kill : ∀ {M : Type} [CommGroup M]
      (φ : (nsmulAddMonoidHom (n ^ j) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker →+ Additive M) t,
      Additive.toMul (φ t) ^ (n ^ j) = 1 := fun φ t => by
    rw [← toMul_nsmul, ← map_nsmul, show (n ^ j) • t = 0 from Subtype.ext t.2, map_zero, toMul_zero]
  have ua := (GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN theta ϑ hE hP _ hm hum).2 n hn.two_le hdvd
  have fin : ∀ {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M), (∀ t, φ t ^ (n ^ j) = 1) →
    (∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) → ∀ t, φ t ∈ S := fun S φ => mem_of_step S φ n j
  generalize n ^ j = m at *
  have m1 : 1 ≤ m := hm.pos
  have div := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have lev := fun p q x => (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F m m (m ^ 2) m1 m1 (pow_two m) p q x).2
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F m m1
  obtain ⟨f', f₁', -, -, f₄', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨φ, hφ⟩ := exists_hom hB f f₄
  obtain ⟨φ', hφ'⟩ := exists_hom hB f' f₄'
  have hiota0 : ∀ (h : GtPtF D.toPre F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D.toPre (T := TF (R := V) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  have mem : ∀ {k} (p : QkPt D.toPre F k), p.y = 0 →
      p.g ∈ (nsmulAddMonoidHom k : GtPtF D.toPre F →+ GtPtF D.toPre F).ker := fun {k} p hy => by
    show k • p.g = 0
    obtain ⟨g, h₁, h₂⟩ := p.eq
    rw [hy] at h₂
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans (isIota_unique h₂ (hiota0 _ ((isZero_iff_eq _).2 rfl)))
  have mk : ∀ {k : ℕ} (g : GtPtF D.toPre F), k • g = 0 → ∃ p : QkPt D.toPre F k, p.y = 0 ∧ p.g = g := fun {k} g h =>
    ⟨⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl,
      hiota0 _ ((isZero_iff_eq _).2 h)⟩, rfl, rfl⟩
  have inj : ∀ t, φ t = 0 → t = 0 := fun t ht => by
    obtain ⟨p, py, pg⟩ := mk t.1 t.2
    obtain ⟨o, oy, og⟩ := mk (k := m) 0 (nsmul_zero m)
    have e : f o = f p := Additive.ofMul.injective (by rw [← hφ t p py pg, ← hφ 0 o oy og, ht, map_zero])
    obtain ⟨z, hy, g, hg₁, hg₂⟩ := (f₃ _ _).1 e
    rw [py, oy, zero_add] at hy
    have z0 : z = 0 := by
      by_contra h0
      have b₁ := QForm.Q_pos hϖ D hQ h0
      have b₂ := Q_nsmul hϖ hQ m z
      rw [← hy, QForm.Q_zero hϖ D hQ] at b₂
      have b₃ : (0 : ℤ) < (m : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
      exact absurd b₂ (mul_pos b₃ (by omega)).ne
    rw [z0] at hg₁
    have hg0 : g = 0 := isIota_unique hg₁ (hiota0 _ ((isZero_iff_eq _).2 rfl))
    have hg := (isAdd_iff_eq _ _ _).1 hg₂
    rw [hg0, add_zero, pg, og] at hg
    exact Subtype.ext hg
  obtain ⟨p, py, hp⟩ := hx
  have ex : x = Additive.toMul (φ ⟨p.g, mem p py⟩) := by rw [hφ _ p py rfl, (f₁ p x).1 hp]; rfl
  rw [ex]
  refine fin _ (fun t => Additive.toMul (φ t)) (kill φ) (fun t => ?_) _
  obtain ⟨r, ry, rg⟩ := mk t.1 t.2
  obtain ⟨g', hg'⟩ := div m m1 t.1
  have e₁ : t.1 = m • g' := (isNsmul_iff_eq _ _ _).1 hg'
  obtain ⟨q, qy, qg⟩ := mk (k := m ^ 2) g' (by rw [pow_two, mul_smul, ← e₁]; exact t.2)
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f' q) := (f₁' _ _).2 rfl
  have e₂ : f' q ^ m = Additive.toMul (φ t) := by
    rw [hφ t r ry rg]
    exact (f₁ _ _).1 (lev r q _ (ry.trans qy.symm) (by rw [qg, rg]; exact hg') hq)
  obtain ⟨p', x', t₁, c, py', hx', hn', hT, hc₀⟩ := ua q _ qy hq
  have x1 : x' ^ (m ^ 2) = 1 := by
    rw [(f₁' _ _).1 hx']
    have := congrArg Additive.toMul (hφ' ⟨_, mem p' py'⟩ p' py' rfl)
    rw [toMul_ofMul] at this
    rw [← this, ← toMul_nsmul, ← map_nsmul,
      show (m ^ 2) • (⟨_, mem p' py'⟩ : (nsmulAddMonoidHom (m ^ 2) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = 0 from
        Subtype.ext (mem p' py'), map_zero, toMul_zero]
  obtain ⟨s, sy, sg⟩ := mk (k := m) (m • p'.g) (by rw [← mul_smul, ← pow_two]; exact mem p' py')
  have e₃ : x' ^ m = Additive.toMul (φ ⟨_, mem s sy⟩) := by
    rw [hφ _ s sy rfl]
    exact (f₁ _ _).1 (lev s p' _ (sy.trans py'.symm) ((isNsmul_iff_eq _ _ _).2 sg) hx')
  refine ⟨x' ^ m, Subgroup.subset_closure ⟨x', t₁, c, x1, hT, hc₀, rfl⟩, ?_⟩
  rw [e₂, e₃] at hn'
  rw [e₃]
  generalize (⟨_, mem s sy⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = a at hn'
  have z : n • (a - t) = 0 := inj _ (by
    rw [map_nsmul, map_sub]
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_sub, div_eq_mul_inv, hn', toMul_zero])
  obtain ⟨w, hw⟩ := div n hn.one_le (t - a).1
  have e₄ : (t - a).1 = n • w := (isNsmul_iff_eq _ _ _).1 hw
  have z' : n • (t - a) = 0 := by rw [← neg_sub, smul_neg, z, neg_zero]
  have wm : m • w = 0 := by
    obtain ⟨d, hd⟩ := hdvd₂
    have : n • (t - a).1 = 0 := congrArg Subtype.val z'
    rw [hd, _root_.mul_comm, mul_smul, mul_smul, ← e₄, this, smul_zero]
  refine ⟨⟨w, wm⟩, ?_⟩
  show Additive.toMul (φ t) = Additive.toMul (φ a) * Additive.toMul (φ ⟨w, wm⟩) ^ n
  rw [← toMul_nsmul, ← map_nsmul, ← toMul_add, ← map_add (f := _),
    show n • (⟨w, wm⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = t - a from
      Subtype.ext e₄.symm, add_sub_cancel]

end GlobalTheory.OneBasis.UnitGen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

theorem GlobalTheory.Ex.OneGen.thG_val_of_prim : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  rintro ⟨hLL, h₁, h₂, h₃, h₄⟩ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hw th ϑ hex hprim m hmo hmu hm
  have hAdm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨f, hf, hfs, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hLL V _ hAdm D A G hG U F (m ^ 2) (pow_pos hmo.pos 2)
  obtain ⟨ua, ub⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hLL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hw th ϑ hex hprim m hmo hmu
  refine ⟨fun x c H => ?_, ?_⟩
  · obtain ⟨hx, t, ht⟩ := (thG_iff A ρ m th x c).1 H
    obtain ⟨p, hp⟩ := hfs x hx
    refine (ua p x t c ((hf p x).2 hp.symm) ht).1 0 fun χ => div_nonneg ?_ (Nat.cast_nonneg _)
    by_cases h : m • χ + p.y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]; simp
    · exact_mod_cast zero_le_one.trans (QForm.Q_pos hϖ D hQ h)
  · obtain ⟨p', x', t, c, -, hx', -, hc, hz⟩ := ub m (by omega) dvd_rfl (TorusExt.qkZero D.tau_bimult F _) _ rfl
      ((hf _ _).2 rfl)
    exact ⟨x', c, (thG_iff A ρ m th x' c).2 ⟨(hx' w₀ hw.1).1, t, hc⟩, hz⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.uniformisedModel_adaptedBasis_is_modelWithSeries : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  first | exact @GlobalTheory.ZH.utest_nonempty_mod | exact GlobalTheory.ZH.utest_nonempty_mod | (intros; apply GlobalTheory.ZH.utest_nonempty_mod <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  first | exact @GlobalTheory.ThetaBound.norm_theta_le | exact GlobalTheory.ThetaBound.norm_theta_le | (intros; apply GlobalTheory.ThetaBound.norm_theta_le <;> assumption)
end
