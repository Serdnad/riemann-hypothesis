module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle989
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem iterD_eq_jet_of_count : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t : ℂ) (κ : Emb F → ℕ) (u : List (Emb F)), 0 < τ.im → (∀ i, u.count i = κ i) → iterD u (fun z ↦ (cK F (2 * s) : ℂ) * gval (2 * s) L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 = jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t κ u hτ hu
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have h1 := GlobalTheory.T.hasSum_iteratedDeriv_hilbertEisenstein_splitLattice F (2 * s) 𝔞 𝔟 _ a x τ c t u (even_two_mul s) ha hτ
  have h2 := GlobalTheory.T.hasSum_iteratedDeriv_hilbertEisenstein_splitLattice F (2 * s) 𝔞 𝔟 _ a x τ c t (word κ) (even_two_mul s) ha hτ
  simp only [hu] at h1
  simp only [count_word_eq] at h2
  have h3 := h1.unique h2
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF
      exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 ≠ 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
      exact_mod_cast mt FractionalIdeal.absNorm_eq_zero_iff.1 𝔞.ne_zero
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor
    exact_mod_cast mul_ne_zero (Real.rpow_pos_of_pos hd _).ne' hn
  have hc : ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ (2 * s) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ Complex.two_pi_I_ne_zero) hω)
  exact (div_left_inj' hc).1 h3

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

namespace GlobalTheory.HilbFam

theorem jet_smul_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, hc⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) hc hτ

end GlobalTheory.HilbFam
end

section

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_add_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im →
    jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) ha hτ

end GlobalTheory.HilbFam
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.axes_vanishing_degree_one_extension : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  first | exact @GlobalTheory.Obs.axesE1_of_axesO1 | exact GlobalTheory.Obs.axesE1_of_axesO1 | (intros; apply GlobalTheory.Obs.axesE1_of_axesO1 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degreeTwoObstructionClass_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  first | exact @GlobalTheory.Obs.isOb2_natural | exact GlobalTheory.Obs.isOb2_natural | (intros; apply GlobalTheory.Obs.isOb2_natural <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_naturalLift_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  first | exact @GlobalTheory.LiftSys.exists_natLift_of_defect | exact GlobalTheory.LiftSys.exists_natLift_of_defect | (intros; apply GlobalTheory.LiftSys.exists_natLift_of_defect <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitive_degree_two_extension : PrimitiveStructureSheafDegTwoVanish → PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_of_primO2 | exact GlobalTheory.Obs.primE2_of_primO2 | (intros; apply GlobalTheory.Obs.primE2_of_primO2 <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem appLE_apply_of_eq_id {X : Scheme.{0}} {g : X ⟶ X} (hg : g = 𝟙 X) {U V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (e' : V ≤ U) (x : Γ(X, U)) : (g.appLE U V e).hom x = (X.presheaf.map (homOfLE e').op).hom x := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  rfl

theorem appLE_appLE_of_retr {X₀ Z₀ : Scheme.{0}} {j₀ : X₀ ⟶ Z₀} {f₀ : Z₀ ⟶ X₀} (hjf : j₀ ≫ f₀ = 𝟙 X₀)
    (U : X₀.Opens) (U' : Z₀.Opens) (U'' : X₀.Opens) (e₁ : U' ≤ f₀ ⁻¹ᵁ U) (e₂ : U'' ≤ j₀ ⁻¹ᵁ U')
    (e : U'' ≤ U) (x : Γ(X₀, U)) :
    (j₀.appLE U' U'' e₂).hom ((f₀.appLE U U' e₁).hom x) = (X₀.presheaf.map (homOfLE e).op).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_apply_of_eq_id hjf _ e x

theorem ext_tri_res_pull1 {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {X X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X} {s' : X' ⟶ Sp R₀} {s'' : X'' ⟶ Sp R₀}
    (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R₀)) (a : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')).pull1 ((extMap R₁ (pairRes φ s')).pull1 a) =
      (extMap R₁ (cechTripleRestrictFirst ψ φ s'')).pull1 ((extMap R₁ (pairPull h')).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans ((extMap R₁ (pairRes φ s')).comp (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')))
    ((extMap R₁ (pairPull h')).comp (extMap R₁ (cechTripleRestrictFirst ψ φ s''))) { app U := 𝟙 _ } (fun U b ↦ ?_) a
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => (erw [map_zero]) <;> rfl
  | tmul x y => rfl
  | add x y hx hy => erw [map_add, map_add, hx, hy]

theorem retractionLiftObstruction_zero_of_liftedSection_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h j₀ hj j hjf hjt hij l hl w c hob
  obtain ⟨l', hl'L, hl'N⟩ := GlobalTheory.T.exists_natural_chart_lifts_of_morphism R R₀ I hI π hπ hk Z₀ X₀ Z X t₀ s₀ t s k i hkk hi S' S P' P j₀ hj j hjt hij
  have hle : ∀ T : (Triple j₀ f₀)ᵒᵖ, T.unop.1.1 ≤ T.unop.1.2.2 := fun T x hx ↦ by
    have h1 := T.unop.2.2 (T.unop.2.1 hx)
    have e := congrArg (fun g : X₀ ⟶ X₀ ↦ g.base x) hjf
    simp at e
    exact e ▸ h1
  let L'' : Pre I π (OTriple j₀ f₀ s₀) := (ofSys S).restrict (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀))
  let u : ∀ T : (Triple j₀ f₀)ᵒᵖ, (pairPre S' f₀).B ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T) →ₐ[R] L''.B T :=
    fun T ↦ l' ((cechTripleProjFirstSecond j₀ f₀).obj T)
  let v : ∀ T : (Triple j₀ f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T)) →ₐ[R] L''.B T :=
    fun T ↦ mp S.F (homOfLE (hle T)).op
  have hvan := GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt R R₀ I hI π hπ hk R₁ α (AffOp X₀) (OAff s₀) (Pair f₀)ᵒᵖ (OPair f₀ t₀) (ofSys S)
    (pairPre S' f₀) (pairPull h) l (Triple j₀ f₀)ᵒᵖ (OTriple j₀ f₀ s₀) L'' (cechTriplePullbackSecond hj) u v hl
    (fun T b ↦ hl'L ((cechTripleProjFirstSecond j₀ f₀).obj T) b)
    (fun T T' a b ↦ by
      have e1 : (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a = (pairFst j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have e2 : (pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a) = (pairSnd j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      change mp S.F ((cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a) (l' ((cechTripleProjFirstSecond j₀ f₀).obj T) b) =
        l' ((cechTripleProjFirstSecond j₀ f₀).obj T') (mp S'.F ((pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a)) b)
      rw [e1, e2]
      exact hl'N ((cechTripleProjFirstSecond j₀ f₀).map a) b)
    (fun T b ↦ by
      change S.p _ (mp S.F _ b) = (j₀.appLE _ _ _).hom ((f₀.appLE _ _ _).hom (S.p _ b))
      exact (S.nat _ b).trans (appLE_appLE_of_retr hjf _ _ _ _ _ (hle T) _).symm)
    (fun T T' a b ↦ by
      change mp S.F _ (mp S.F _ b) = mp S.F _ (mp S.F _ b)
      exact (mp_comp S.F _ _ b).symm.trans ((congrArg (fun q ↦ mp S.F q b)
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (mp_comp S.F _ _ b)))
    w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) hob
  rw [ext_tri_res_pull1] at hvan
  have inj := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ Z₀ X₀ s₀ j₀).2 X₀ f₀
  unfold IsExtendedPullbackDegOne
  rw [map_zero]
  exact inj (hvan.trans (map_zero _).symm)

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  first | exact @GlobalTheory.LiftSys.exists_defect_cocycle | exact GlobalTheory.LiftSys.exists_defect_cocycle | (intros; apply GlobalTheory.LiftSys.exists_defect_cocycle <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  first | exact @GlobalTheory.LiftSys.r_eq_neg_defect | exact GlobalTheory.LiftSys.r_eq_neg_defect | (intros; apply GlobalTheory.LiftSys.r_eq_neg_defect <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  first | exact @GlobalTheory.LiftSys.exists_corr_of_defect | exact GlobalTheory.LiftSys.exists_corr_of_defect | (intros; apply GlobalTheory.LiftSys.exists_corr_of_defect <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.locIso_transport_cochains_in_ideal : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  first | exact @GlobalTheory.LiftSys.locIso_transport | exact GlobalTheory.LiftSys.locIso_transport | (intros; apply GlobalTheory.LiftSys.locIso_transport <;> assumption)
end
