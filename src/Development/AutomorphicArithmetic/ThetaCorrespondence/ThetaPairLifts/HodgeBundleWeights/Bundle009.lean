module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
theorem boundary_unit_at_integral_points : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  intro _ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies
  letI := io.toAlgebra
  obtain ⟨φ, hφ⟩ := exists_factor T io hio
  have hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c)) := fun s => hVZ ▸ hlies s
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy
  have hp : Dw.mult τ.1 = Dw.p := by rw [Datum.mult, if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by rw [Datum.mult, if_neg (conj_ne τ)]
  obtain ⟨v, hv, hsv⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp
  obtain ⟨w, hw, hsw⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq
  let aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ := ⟨χ, hχ1, hχ3, v, w, hv, hw⟩
  have hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ =
      spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _) := Category.assoc _ _ _
  obtain ⟨v', hv', ev⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv
  obtain ⟨w', hw', ew⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw
  rw [hφ] at hv' hw'
  let aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io :=
    ⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1 := by
    refine ⟨hφ, rfl, fun i => ?_, fun i => ?_⟩
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i
      convert this using 2 with k
      exact (ev k).symm
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i
      convert this using 2 with k
      exact (ew k).symm
  have e := hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc
  simp only [Matrix.det_one, mul_one] at e
  have hm : Matches Y V τ y₀.1 aK :=
    ⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by
      change SameVec Y y₀.1 _ (v' i).left
      rw [ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by
      change SameVec Y y₀.1 _ (w' i).left
      rw [ew]; exact hsw i⟩⟩
  have hr := hrd T.Fr y₀.1 y₀.2.1 aK hm
  change nval T.V 1 (evR Xo c f y₀.1) = 0
  rw [hr]
  change nval T.V 1 (sig T.Fr io aK) = 0
  rw [e]
  exact nval_unit T _ (hvn T.V φ aT)
end GlobalTheory.BdryUnitVal
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit

theorem _root_.GlobalTheory.T.boundary_unit_valuation_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  first | exact @_root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | exact _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | (intros; apply _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points <;> assumption)
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_linearization_pullback : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF I g hI hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hPr hO hj heq
  obtain ⟨m, hm, hmv⟩ := _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators hP E H Dw l Xo c TF Z hpq hA Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq
  have hT := GlobalTheory.T.torsion_fibre_injects_levelModule E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq m hm hmv
  exact ⟨pullG TF Z φ, inferInstance, pullψ TF Z φ, pullAct TF Z φ, m,
    isGrpPullback_pullψ TF Z φ, pullAct_pullψ TF Z φ, hm.1, hm.2.1, hm.2.2,
    GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι hU X' φ ρ' hN hPr m hm hT⟩
end GlobalTheory.EqvAct
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.equivariant_linearization_pullback_compat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | exact _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback <;> assumption)
end
end
